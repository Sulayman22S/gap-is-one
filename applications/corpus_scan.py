"""Test graph families against the Duhamel-Cazenave conjecture corpus.

An independent evaluator for the prefix language of the corpus (grammar and conventions read
from the corpus documentation; nothing from the archive is imported or executed).

The corpus file index_conjectures.csv is in the archive of proofs of arXiv:2611.03879; it is not
redistributed here.

Usage:
    python -I corpus_scan.py <index_conjectures.csv> validate
    python -I corpus_scan.py <index_conjectures.csv> scan    scan.json
    python -I corpus_scan.py <index_conjectures.csv> control scan.json control.json
    python -I corpus_scan.py <index_conjectures.csv> big     big.json
    python -I corpus_scan.py summary scan.json control.json big.json refuted_open_rows.csv

validate  compares the evaluator with the margins and counterexamples recorded in the corpus.
scan      runs every row on 936 graphs built as matrices (up to 1,041 vertices).
control   asks, for each open row found by scan, whether plain barbells violate it too.
big       runs proved, open and conditional rows on graphs of up to two million vertices,
          computed from their classes of interchangeable vertices.
summary   merges the three result files into the list of violated open rows.

All results are FLOATING POINT. A row is reported as violated when left - right > TOL on a
graph where both sides are finite, the rule the corpus itself uses, and when that survives
twelve random perturbations of size 1e-9 of every real-valued invariant.
"""
import csv
import itertools
import json
import math
import sys

import numpy as np

TOL = 1e-6          # the corpus's refutation threshold
RANK_TOL = 1e-8     # the corpus's rank tolerance

BINARY = {"+", "-", "*", "/", "^"}
UNARY = {"log", "sqrt"}
GLOBALS = ("n", "rA", "rL", "l1", "l2", "mu1", "mu2", "sA", "sL", "R", "rad", "dia")


# ----------------------------------------------------------------------------- parser

def parse(s):
    toks = s.split()
    pos = [0]

    def take():
        t = toks[pos[0]]
        pos[0] += 1
        return t

    def need(t):
        if take() != t:
            raise ValueError("expected %s in %r" % (t, s))

    def matrix():
        t = take()
        if t == "Adj":
            return "A"
        if t == "laplac":
            need("Adj")
            return "L"
        raise ValueError("bad matrix in %r" % s)

    def vertex():
        t = take()
        if t not in ("u", "v"):
            raise ValueError("bad vertex in %r" % s)
        return t

    def expr():
        t = take()
        if t in BINARY:
            a = expr()
            b = expr()
            return (t, a, b)
        if t in UNARY:
            return (t, expr())
        if t in ("1", "2"):
            return ("const", float(t))
        if t == "rank":
            return ("atom", "r" + matrix())
        if t in ("large", "large-2", "sum"):
            need("eigen")
            mat = matrix()
            return ("atom", {("large", "A"): "l1", ("large-2", "A"): "l2", ("large", "L"): "mu1",
                             ("large-2", "L"): "mu2", ("sum", "A"): "sA", ("sum", "L"): "sL"}[(t, mat)])
        if t == "IndRand":
            need("Adj")
            return ("atom", "R")
        if t == "rad":
            need("Adj")
            return ("atom", "rad")
        if t == "dia":
            need("Adj")
            return ("atom", "dia")
        if t == "max-v":
            need("Adj")
            return ("maxv", expr())
        if t == "max-v-u":
            need("Adj")
            return ("maxe", expr())
        if t == "degree":
            return ("atom", "deg_" + vertex())
        if t == "temp":
            return ("atom", "temp_" + vertex())
        if t == "weight":
            vertex()
            vertex()
            return ("atom", "w")
        raise ValueError("unknown token %r in %r" % (t, s))

    need("<=")
    a = expr()
    b = expr()
    if pos[0] != len(toks):
        raise ValueError("trailing tokens in %r" % s)
    return a, b


# ----------------------------------------------------------------------------- graphs

def adj(n, edges):
    A = np.zeros((n, n))
    for u, v in edges:
        if u != v:
            A[u, v] = A[v, u] = 1.0
    return A


def eccentricities(A):
    n = len(A)
    B = A.astype(np.float32)
    reach = np.eye(n, dtype=bool)
    frontier = reach.copy()
    ecc = np.zeros(n)
    for k in range(1, n):
        nxt = (frontier.astype(np.float32) @ B) > 0
        new = nxt & ~reach
        if not new.any():
            break
        ecc[new.any(axis=1)] = k
        reach |= new
        frontier = new
    if not reach.all():
        raise ValueError("graph is not connected")
    return ecc


def invariants(A):
    n = len(A)
    deg = A.sum(axis=1)
    ea = np.linalg.eigvalsh(A)
    el = np.linalg.eigvalsh(np.diag(deg) - A)
    ecc = eccentricities(A)
    s, t = np.nonzero(A)
    pairs = sorted(set(zip(deg[s].tolist(), deg[t].tolist())))
    return {
        "n": float(n), "m": deg.sum() / 2,
        "rA": float((np.abs(ea) > RANK_TOL).sum()), "rL": float((np.abs(el) > RANK_TOL).sum()),
        "l1": ea[-1], "l2": ea[-2], "mu1": el[-1], "mu2": el[-2],
        "sA": 0.0, "sL": float(deg.sum()),
        "R": float((1.0 / np.sqrt(deg[s] * deg[t])).sum() / 2),
        "rad": float(ecc.min()), "dia": float(ecc.max()),
        "degs": sorted(set(deg.tolist())), "pairs": pairs,
    }


class Base:
    """A set of graphs, stored as the arrays the evaluator needs."""

    def __init__(self, items):
        self.names = [name for name, _ in items]
        inv = [g for _, g in items]
        G = len(inv)
        self.G = G
        self.glob = {k: np.array([g[k] for g in inv], dtype=float)[:, None] for k in GLOBALS}
        D = max(len(g["degs"]) for g in inv)
        P = max(len(g["pairs"]) for g in inv)
        self.deg = np.full((G, D), np.nan)
        self.du = np.full((G, P), np.nan)
        self.dv = np.full((G, P), np.nan)
        for i, g in enumerate(inv):
            self.deg[i, :len(g["degs"])] = g["degs"]
            # ordered pair (a, b): v has degree a, u (the other endpoint) has degree b
            self.dv[i, :len(g["pairs"])] = [p[0] for p in g["pairs"]]
            self.du[i, :len(g["pairs"])] = [p[1] for p in g["pairs"]]
        self.vmask = ~np.isnan(self.deg)
        self.emask = ~np.isnan(self.du)
        self.nan = np.full((G, 1), np.nan)


def ev(e, b, ctx):
    t = e[0]
    if t == "const":
        return np.float64(e[1])
    if t == "atom":
        a = e[1]
        if a in b.glob:
            return b.glob[a]
        if ctx is None:
            return b.nan
        if a == "deg_v":
            return b.deg if ctx == "v" else b.dv
        if a == "temp_v":
            d = b.deg if ctx == "v" else b.dv
            return d / (b.glob["n"] - d)
        if ctx != "e":
            return b.nan
        if a == "deg_u":
            return b.du
        if a == "temp_u":
            return b.du / (b.glob["n"] - b.du)
        if a == "w":
            return 1.0 / np.sqrt(b.du * b.dv)
        raise KeyError(a)
    if t in ("maxv", "maxe"):
        c = "v" if t == "maxv" else "e"
        mask = b.vmask if c == "v" else b.emask
        sub = np.broadcast_to(ev(e[1], b, c), mask.shape)
        bad = (np.isnan(sub) & mask).any(axis=1)
        r = np.where(mask, sub, -np.inf).max(axis=1)
        r = np.where(bad, np.nan, r)
        return r[:, None]
    if t == "log":
        return np.log(ev(e[1], b, ctx))
    if t == "sqrt":
        return np.sqrt(ev(e[1], b, ctx))
    x = ev(e[1], b, ctx)
    y = ev(e[2], b, ctx)
    if t == "+":
        return x + y
    if t == "-":
        return x - y
    if t == "*":
        return x * y
    if t == "/":
        return x / y
    if t == "^":
        return np.power(x, y)
    raise ValueError(t)


def margins(f, b):
    """left - right per graph; -inf where a side is undefined."""
    L = np.broadcast_to(ev(f[0], b, None), (b.G, 1))[:, 0]
    R = np.broadcast_to(ev(f[1], b, None), (b.G, 1))[:, 0]
    ok = np.isfinite(L) & np.isfinite(R)
    return np.where(ok, L - R, -np.inf)


# ----------------------------------------------------------------------------- families

def path(n):
    return adj(n, [(i, i + 1) for i in range(n - 1)])


def complete(n):
    return adj(n, itertools.combinations(range(n), 2))


def star(n):
    return adj(n, [(0, i) for i in range(1, n)])


def cycle(n):
    return adj(n, [(i, (i + 1) % n) for i in range(n)])


def wheel(n):
    return adj(n, [(0, i) for i in range(1, n)] + [(i, i % (n - 1) + 1) for i in range(1, n)])


def lollipop(m, p):
    E = list(itertools.combinations(range(m), 2)) + [(i, i + 1) for i in range(m - 1, m + p - 1)]
    return adj(m + p, E)


def barbell(m, k, drop=False):
    """Two K_m joined by a path with k inner vertices. drop=True removes, in each clique, the
    edge between the attachment vertex and one other vertex (m = 4, k = 3 is G11)."""
    E = []
    for base in (0, m):
        for i, j in itertools.combinations(range(m), 2):
            if drop and (i, j) == (0, 1):
                continue
            E.append((base + i, base + j))
    chain = [0] + [2 * m + t for t in range(k)] + [m]
    E += list(zip(chain, chain[1:]))
    return adj(2 * m + k, E)


def complete_bipartite(a, b):
    return adj(a + b, [(i, a + j) for i in range(a) for j in range(b)])


def complete_split(k, n):
    E = list(itertools.combinations(range(k), 2)) + [(i, j) for i in range(k) for j in range(k, n)]
    return adj(n, E)


def broom(n, k):
    E = [(i, i + 1) for i in range(n - k)] + [(0, n - k + 1 + i) for i in range(k - 1)]
    return adj(n, E)


def kite(n, k):
    E = list(itertools.combinations(range(k), 2)) + [(i, i + 1) for i in range(k - 1, n - 1)]
    return adj(n, E)


def double_star(n, a):
    E = [(0, 1)] + [(0, 2 + i) for i in range(a)] + [(1, 2 + a + i) for i in range(n - 2 - a)]
    return adj(n, E)


def clusters(m, s, k=1):
    """Two clusters (clique of m plus s satellites joined to the whole clique), their first
    satellites joined by a path with k inner vertices. k = 1 is the graph T(m, s - 1) of the
    Lean proof (one connector vertex)."""
    size = m + s
    E = []
    for base in (0, size):
        E += [(base + i, base + j) for i, j in itertools.combinations(range(m), 2)]
        E += [(base + i, base + m + v) for i in range(m) for v in range(s)]
    chain = [m] + [2 * size + t for t in range(k)] + [size + m]
    E += list(zip(chain, chain[1:]))
    return adj(2 * size + k, E)


def all_connected(n):
    """Every connected graph on n labelled vertices, one representative per invariant profile."""
    pairs = list(itertools.combinations(range(n), 2))
    seen = {}
    for bits in range(1 << len(pairs)):
        E = [p for i, p in enumerate(pairs) if bits >> i & 1]
        if len(E) < n - 1:
            continue
        A = adj(n, E)
        try:
            g = invariants(A)
        except ValueError:
            continue
        key = (g["m"], g["rA"], round(g["l1"], 9), round(g["l2"], 9), round(g["mu1"], 9),
               round(g["mu2"], 9), round(g["R"], 9), g["rad"], g["dia"], tuple(g["pairs"]))
        seen.setdefault(key, g)
    return list(seen.values())


def reference_families(nmax=30):
    """The deterministic families of the corpus's own graph base, for n up to nmax."""
    out = []
    for n in range(2, nmax + 1):
        out += [("path%d" % n, path(n)), ("star%d" % n, star(n)), ("K%d" % n, complete(n))]
        if n >= 3:
            out.append(("cycle%d" % n, cycle(n)))
        if n >= 4:
            out.append(("wheel%d" % n, wheel(n)))
            out.append(("lollipop%d" % n, lollipop(n // 2, n - n // 2)))
            c = max(3, n // 3)
            if n - 2 * c >= 0:
                out.append(("barbell%d" % n, barbell(c, n - 2 * c)))
            for a in range(1, n // 2 + 1):
                out.append(("K%d,%d" % (a, n - a), complete_bipartite(a, n - a)))
            for k in range(1, n - 1, max(1, n // 8)):
                out.append(("split%d,%d" % (k, n), complete_split(k, n)))
            for k in range(2, n - 1, max(1, n // 6)):
                out.append(("broom%d,%d" % (n, k), broom(n, k)))
                out.append(("kite%d,%d" % (n, k), kite(n, k)))
            for a in range(1, n - 2, max(1, n // 6)):
                out.append(("dstar%d,%d" % (n, a), double_star(n, a)))
    return out


def our_families():
    """The graphs of the theorems, and their close relatives."""
    out = []
    for d in range(3, 11):                       # blocks K_{d+1} minus an edge
        for k in range(0, 13):
            out.append(("D(%d,%d)" % (d, k), "deleted-edge barbell", barbell(d + 1, k, drop=True)))
    for m in range(2, 41):
        for s in range(2, 11):
            out.append(("T(m=%d,s=%d)" % (m, s), "cluster graph", clusters(m, s, 1)))
    for m, s in ((64, 4), (97, 4), (125, 5), (216, 6), (343, 7), (512, 8)):
        out.append(("T(m=%d,s=%d)" % (m, s), "cluster graph", clusters(m, s, 1)))
    for m in range(2, 21):
        for s in range(2, 7):
            for k in range(2, 7):
                out.append(("S(m=%d,s=%d,k=%d)" % (m, s, k), "clusters on a longer path",
                            clusters(m, s, k)))
    return out


# ----------------------------------------------------------------------------- corpus

def read_corpus(path_csv):
    rows = []
    with open(path_csv, encoding="utf-8", newline="") as f:
        r = csv.reader(f)
        next(r)
        for row in r:
            rows.append({"id": int(row[0]), "status": row[1], "text": row[3], "cex": row[9],
                         "margin": float(row[10]) if row[10] else None, "formula": row[11]})
    return rows


def validate(rows):
    print("building the reference base ...", flush=True)
    by_n = {n: all_connected(n) for n in range(2, 7)}
    print("connected graphs by invariant profile, n = 2..6:", {n: len(v) for n, v in by_n.items()})
    items = []
    for n, gs in by_n.items():
        items += [("all%d" % n, g) for g in gs]
    fam = [(name, invariants(A)) for name, A in reference_families(30)]
    base = Base(items + fam)
    is_n = {n: np.array([name == "all%d" % n for name in base.names]) for n in by_n}
    k2 = base.names.index("all2")
    stats = {"rows": 0, "exceeds": 0, "equal": 0, "cex_checked": 0, "cex_match": 0, "k2_checked": 0,
             "k2_match": 0, "parse_errors": 0}
    worst = []
    with np.errstate(all="ignore"):
        for row in rows:
            try:
                f = parse(row["formula"])
            except Exception:
                stats["parse_errors"] += 1
                continue
            if row["margin"] is None:
                continue
            stats["rows"] += 1
            d = margins(f, base)
            mine = float(d.max())
            ref = row["margin"]
            tol = 1e-7 * (1 + abs(ref))
            if row["status"].startswith("non d"):
                continue
            # 1. my base is a subset of theirs, so my maximum can never exceed theirs
            if mine > ref + tol:
                stats["exceeds"] += 1
                worst.append((row["id"], row["status"], row["text"], mine, ref,
                              base.names[int(d.argmax())]))
            elif abs(mine - ref) <= tol:
                stats["equal"] += 1
            # 2. recorded counterexample on n <= 6 vertices: the maximum over all graphs with
            #    that many vertices must reproduce the recorded margin
            cex = row["cex"]
            if cex.startswith("all") and "#" in cex:
                n = int(cex[3:cex.index("#")])
                if n in is_n:
                    stats["cex_checked"] += 1
                    here = float(d[is_n[n]].max())
                    if abs(here - ref) <= tol:
                        stats["cex_match"] += 1
                    else:
                        worst.append((row["id"], "cex " + cex, row["text"], here, ref, ""))
                if n == 2:
                    stats["k2_checked"] += 1
                    if abs(float(d[k2]) - ref) <= tol:
                        stats["k2_match"] += 1
    print(json.dumps(stats, indent=1))
    for w in worst:
        print("MISMATCH", w)


def perturbed(base, seed):
    """A copy of the base whose real-valued invariants are moved by about 1e-9. A violation
    that survives every such copy does not hang on the last bits of an eigenvalue."""
    rng = np.random.default_rng(seed)
    b = Base.__new__(Base)
    b.__dict__.update(base.__dict__)
    b.glob = dict(base.glob)
    for k in ("l1", "l2", "mu1", "mu2", "R"):
        sign = rng.choice([-1.0, 1.0], size=base.glob[k].shape)
        b.glob[k] = base.glob[k] * (1 + 1e-9 * sign) + 1e-9 * sign
    return b


def scan(rows, out_path):
    fams = our_families()
    print("computing invariants of %d graphs ..." % len(fams), flush=True)
    items = [(name, invariants(A)) for name, _, A in fams]
    kind = {name: k for name, k, _ in fams}
    order = np.array([g["n"] for _, g in items])
    base = Base(items)
    shaken = [perturbed(base, seed) for seed in range(12)]
    result = {"graphs": len(fams), "by_status": {}, "violated": []}
    with np.errstate(all="ignore"):
        for row in rows:
            st = row["status"]
            try:
                f = parse(row["formula"])
            except Exception:
                continue
            d = margins(f, base)
            c = result["by_status"].setdefault(st, {"rows": 0, "violated": 0, "robust": 0})
            c["rows"] += 1
            if float(d.max()) <= TOL:
                continue
            c["violated"] += 1
            if st.startswith("réfut") or st.startswith("non d"):
                continue
            # keep only violations that survive every perturbation and are not astronomically large
            lo = d.copy()
            for sb in shaken:
                lo = np.minimum(lo, margins(f, sb))
            lo = np.where(np.abs(d) < 1e9, lo, -np.inf)
            good = lo > TOL
            if not good.any():
                result["violated"].append({"id": row["id"], "status": st, "text": row["text"],
                                           "robust": False, "margin": float(d.max()),
                                           "graph": base.names[int(d.argmax())]})
                continue
            c["robust"] += 1
            i = int(np.where(good, lo, -np.inf).argmax())
            j = int(np.where(good, order, np.inf).argmin())
            result["violated"].append({
                "id": row["id"], "status": st, "text": row["text"], "robust": True,
                "margin": float(lo[i]), "graph": base.names[i], "kind": kind[base.names[i]],
                "vertices": int(order[i]), "graphs_violating": int(good.sum()),
                "smallest": base.names[j], "smallest_vertices": int(order[j]),
                "smallest_margin": float(lo[j]),
                "kinds": sorted({kind[base.names[k]] for k in np.nonzero(good)[0]}),
            })
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(result, fh, ensure_ascii=False, indent=1)
    print(json.dumps(result["by_status"], ensure_ascii=False, indent=1))
    for v in sorted(result["violated"], key=lambda v: (v["status"], not v["robust"], v["id"])):
        if v["robust"]:
            print("%-14s #%-8d %-44s margin %.4g on %s; %d graphs; smallest %s (%d vertices, margin %.4g); %s" % (
                v["status"], v["id"], v["text"], v["margin"], v["graph"], v["graphs_violating"],
                v["smallest"], v["smallest_vertices"], v["smallest_margin"], ", ".join(v["kinds"])))
        else:
            print("%-14s #%-8d %-44s NOT ROBUST (raw margin %.4g on %s)" % (
                v["status"], v["id"], v["text"], v["margin"], v["graph"]))


def sym_quotient(sizes, edges_between, inner_degree):
    """Symmetric quotient matrix of an equitable partition: S_ij = e_ij / sqrt(n_i n_j)."""
    k = len(sizes)
    S = np.zeros((k, k))
    for (i, j), e in edges_between.items():
        S[i, j] = S[j, i] = e / math.sqrt(sizes[i] * sizes[j])
    for i, d in inner_degree.items():
        S[i, i] = d
    return S


def closed_form(sizes, degs, edges_between, inner_degree, extra_adj, extra_lap, rad, dia):
    """Invariants of a graph given by an equitable partition into classes of twins.

    extra_adj / extra_lap: eigenvalues outside the quotient, as {value: multiplicity}."""
    n = sum(sizes)
    S = sym_quotient(sizes, edges_between, inner_degree)
    qa = np.linalg.eigvalsh(S)
    ql = np.linalg.eigvalsh(np.diag([float(d) for d in degs]) - S)

    def top_two(q, extra):
        vals = sorted(q.tolist(), reverse=True)[:2]
        for v, mult in extra.items():
            vals += [float(v)] * min(mult, 2)
        vals.sort(reverse=True)
        return vals[0], vals[1]

    l1, l2 = top_two(qa, extra_adj)
    mu1, mu2 = top_two(ql, extra_lap)
    zero_adj = int((np.abs(qa) <= RANK_TOL).sum()) + sum(m for v, m in extra_adj.items() if v == 0)
    medges = sum(edges_between.values()) + sum(sizes[i] * d / 2 for i, d in inner_degree.items())
    R = sum(e / math.sqrt(degs[i] * degs[j]) for (i, j), e in edges_between.items())
    R += sum(sizes[i] * d / 2 / degs[i] for i, d in inner_degree.items())
    pairs = set()
    for (i, j) in edges_between:
        pairs.add((float(degs[i]), float(degs[j])))
        pairs.add((float(degs[j]), float(degs[i])))
    for i, d in inner_degree.items():
        if d > 0:
            pairs.add((float(degs[i]), float(degs[i])))
    return {"n": float(n), "m": float(medges), "rA": float(n - zero_adj), "rL": float(n - 1),
            "l1": l1, "l2": l2, "mu1": mu1, "mu2": mu2, "sA": 0.0, "sL": float(2 * medges),
            "R": float(R), "rad": float(rad), "dia": float(dia),
            "degs": sorted({float(d) for d in degs}), "pairs": sorted(pairs)}


def cluster_closed(m, s):
    """T(m, s - 1) for m >= 2, s >= 2. Classes: connector; per cluster: attachment satellite,
    the other s - 1 satellites, the core."""
    sizes = [1, 1, s - 1, m, 1, s - 1, m]
    degs = [2, m + 1, m, m + s - 1, m + 1, m, m + s - 1]
    eb = {(0, 1): 1, (0, 4): 1, (1, 3): m, (2, 3): (s - 1) * m, (4, 6): m, (5, 6): (s - 1) * m}
    inner = {3: m - 1, 6: m - 1}
    return closed_form(sizes, degs, eb, inner, {-1: 2 * (m - 1), 0: 2 * (s - 2)},
                       {m + s: 2 * (m - 1), m: 2 * (s - 2)}, 3, 6)


def barbell_closed(m):
    """Two K_m joined by one edge, m >= 3. Classes per clique: attachment vertex, the rest."""
    sizes = [1, m - 1, 1, m - 1]
    degs = [m, m - 1, m, m - 1]
    eb = {(0, 2): 1, (0, 1): m - 1, (2, 3): m - 1}
    inner = {1: m - 2, 3: m - 2}
    return closed_form(sizes, degs, eb, inner, {-1: 2 * (m - 2)}, {m: 2 * (m - 2)}, 2, 3)


def check_closed_forms():
    worst = 0.0
    for m in range(2, 26):
        for s in range(2, 9):
            a, b = invariants(clusters(m, s, 1)), cluster_closed(m, s)
            for k in GLOBALS:
                worst = max(worst, abs(a[k] - b[k]) / (1 + abs(a[k])))
            assert a["degs"] == b["degs"] and a["pairs"] == b["pairs"], (m, s)
    for m in range(3, 41):
        a, b = invariants(barbell(m, 0)), barbell_closed(m)
        for k in GLOBALS:
            worst = max(worst, abs(a[k] - b[k]) / (1 + abs(a[k])))
        assert a["degs"] == b["degs"] and a["pairs"] == b["pairs"], m
    return worst


def big(rows, out_path):
    """The same test with very large graphs, from the exact structure instead of the matrix."""
    print("closed forms against brute force, largest relative difference: %.2e" % check_closed_forms())
    grid = [50, 100, 200, 500, 1000, 2000, 5000, 10 ** 4, 2 * 10 ** 4, 5 * 10 ** 4, 10 ** 5,
            2 * 10 ** 5, 5 * 10 ** 5, 10 ** 6]
    ts = []
    for s in (2, 3, 4, 6, 8, 9, 12, 16, 24, 32, 48, 64):
        for m in sorted(set(grid + [s ** 3, 2 * s ** 3] + ([1060] if s == 9 else []))):
            if m >= 2:
                ts.append(("T(m=%d,s=%d)" % (m, s), cluster_closed(m, s)))
    bs = [("B(%d,0)" % m, barbell_closed(m)) for m in sorted(set(grid + [31, 40, 64, 97, 125, 216, 343, 520]))]
    bases = {}
    for name, items in (("cluster graph", ts), ("plain barbell", bs)):
        b = Base(items)
        bases[name] = (b, [perturbed(b, seed) for seed in range(12)], np.array([g["n"] for _, g in items]))
    out = {"graphs": {k: len(v[0].names) for k, v in bases.items()}, "by_status": {}, "open": []}
    with np.errstate(all="ignore"):
        for row in rows:
            st = row["status"]
            if st.startswith("réfut") or st.startswith("non d"):
                continue
            f = parse(row["formula"])
            rec = {"id": row["id"], "text": row["text"], "by": {}}
            for name, (b, shaken, order) in bases.items():
                lo = robust_margins(f, b, shaken)
                good = lo > TOL
                if good.any():
                    j = int(np.where(good, order, np.inf).argmin())
                    rec["by"][name] = {"smallest": b.names[j], "vertices": int(order[j]),
                                       "margin_at_smallest": float(lo[j]), "graphs": int(good.sum())}
            c = out["by_status"].setdefault(st, {"rows": 0, "cluster graph": 0, "plain barbell": 0})
            c["rows"] += 1
            for name in rec["by"]:
                c[name] += 1
            if rec["by"] and st == "ouverte":
                out["open"].append(rec)
            elif rec["by"]:
                print("UNEXPECTED: %s row %d %s violated: %s" % (st, row["id"], row["text"], rec["by"]))
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1)
    print(json.dumps(out["graphs"]), json.dumps(out["by_status"], ensure_ascii=False))
    only = [r for r in out["open"] if "plain barbell" not in r["by"]]
    print("open rows violated by large cluster graphs or large plain barbells: %d" % len(out["open"]))
    print("  by cluster graphs: %d;  by plain barbells: %d;  by cluster graphs only: %d" % (
        sum("cluster graph" in r["by"] for r in out["open"]),
        sum("plain barbell" in r["by"] for r in out["open"]), len(only)))
    for r in only:
        v = r["by"]["cluster graph"]
        print("  only clusters: #%-8d %-46s smallest %s (%d vertices, margin %.3g)" % (
            r["id"], r["text"], v["smallest"], v["vertices"], v["margin_at_smallest"]))


def summary(scan_path, control_path, big_path, out_csv):
    """Merge the three runs into one list of open rows that our graphs violate."""
    rows = {}

    def put(i, text, who, vertices, name, margin):
        e = rows.setdefault(i, {"text": text, "ours": None, "barbell": None})
        if e[who] is None or vertices < e[who][0]:
            e[who] = (vertices, name, margin)

    with open(scan_path, encoding="utf-8") as fh:
        for v in json.load(fh)["violated"]:
            if v["robust"] and v["status"] == "ouverte":
                put(v["id"], v["text"], "ours", v["smallest_vertices"], v["smallest"], v["smallest_margin"])
    with open(control_path, encoding="utf-8") as fh:
        for r in json.load(fh):
            for k, who in (("plain barbell", "barbell"), ("deleted-edge barbell", "ours"),
                           ("cluster graph", "ours")):
                if k in r["by"]:
                    c = r["by"][k]
                    put(r["id"], r["text"], who, c["vertices"], c["smallest"], c["margin_at_smallest"])
    with open(big_path, encoding="utf-8") as fh:
        for r in json.load(fh)["open"]:
            for k, who in (("plain barbell", "barbell"), ("cluster graph", "ours")):
                if k in r["by"]:
                    c = r["by"][k]
                    put(r["id"], r["text"], who, c["vertices"], c["smallest"], c["margin_at_smallest"])
    ours = {i: e for i, e in rows.items() if e["ours"]}
    need = [i for i, e in ours.items() if e["barbell"] is None]
    print("open rows violated by our graphs: %d" % len(ours))
    print("  need the construction (no plain barbell tested violates them): %d" % len(need))
    print("  size only (plain barbells violate them too): %d" % (len(ours) - len(need)))
    print("open rows violated by plain barbells only: %d" % (len(rows) - len(ours)))
    buckets = {"10 to 60": [0, 0], "61 to 1,000": [0, 0], "over 1,000": [0, 0]}
    for e in ours.values():
        n = e["ours"][0] if e["barbell"] is None else min(e["ours"][0], e["barbell"][0])
        key = "10 to 60" if n <= 60 else "61 to 1,000" if n <= 1000 else "over 1,000"
        buckets[key][0 if e["barbell"] is None else 1] += 1
    for key, (a, b) in buckets.items():
        print("  smallest violating graph %-12s needs the construction %3d, size only %3d" % (key, a, b))
    with open(out_csv, "w", encoding="utf-8", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["corpus_id", "statement", "class", "smallest_graph_of_ours_tested", "vertices",
                    "left_minus_right", "smallest_plain_barbell_tested", "barbell_vertices"])
        for i, e in sorted(ours.items()):
            w.writerow([i, e["text"], "needs the construction" if e["barbell"] is None else "size only",
                        e["ours"][1], e["ours"][0], "%.6g" % e["ours"][2],
                        e["barbell"][1] if e["barbell"] else "", e["barbell"][0] if e["barbell"] else ""])
    print("wrote %s" % out_csv)


def robust_margins(f, base, shaken):
    d = margins(f, base)
    lo = d.copy()
    for sb in shaken:
        lo = np.minimum(lo, margins(f, sb))
    return np.where(np.abs(d) < 1e9, lo, -np.inf)


def control(rows, result_path, out_path):
    """For each open row our graphs violate: do plain barbells (two complete graphs joined by a
    short path), which need none of our constructions, violate it too?"""
    with open(result_path, encoding="utf-8") as fh:
        ids = {v["id"] for v in json.load(fh)["violated"] if v["robust"] and v["status"] == "ouverte"}
    sizes = list(range(3, 41)) + [64, 97, 125, 216, 343, 520]
    groups = {
        "plain barbell": [("B(%d,%d)" % (m, k), barbell(m, k)) for m in sizes for k in range(0, 4)],
        "deleted-edge barbell": [("D(%d,%d)" % (d, k), barbell(d + 1, k, drop=True))
                                 for d in range(3, 41) for k in range(0, 13)],
        "cluster graph": [("T(m=%d,s=%d)" % (m, s), clusters(m, s, 1)) for m in range(2, 41)
                          for s in range(2, 11)]
        + [("T(m=%d,s=%d)" % (m, s), clusters(m, s, 1))
           for m, s in ((64, 4), (97, 4), (125, 5), (216, 6), (343, 7), (512, 8))],
    }
    bases = {}
    for name, graphs in groups.items():
        print("computing %d graphs: %s" % (len(graphs), name), flush=True)
        items = [(gname, invariants(A)) for gname, A in graphs]
        b = Base(items)
        bases[name] = (b, [perturbed(b, seed) for seed in range(12)],
                       np.array([g["n"] for _, g in items]))
    out = []
    with np.errstate(all="ignore"):
        for row in rows:
            if row["id"] not in ids:
                continue
            f = parse(row["formula"])
            rec = {"id": row["id"], "text": row["text"], "by": {}}
            for name, (b, shaken, order) in bases.items():
                lo = robust_margins(f, b, shaken)
                good = lo > TOL
                if good.any():
                    j = int(np.where(good, order, np.inf).argmin())
                    i = int(np.where(good, lo, -np.inf).argmax())
                    rec["by"][name] = {"smallest": b.names[j], "vertices": int(order[j]),
                                       "margin_at_smallest": float(lo[j]), "graphs": int(good.sum()),
                                       "largest_margin": float(lo[i]), "at": b.names[i]}
            out.append(rec)
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1)
    need_ours = [r for r in out if "plain barbell" not in r["by"]]
    print("open rows violated by our graphs: %d" % len(out))
    print("  also violated by plain barbells: %d" % (len(out) - len(need_ours)))
    print("  NOT violated by any plain barbell tested: %d" % len(need_ours))
    for r in sorted(out, key=lambda r: ("plain barbell" in r["by"], r["id"])):
        parts = ["%s: %s (%d v, %.3g)" % (k, v["smallest"], v["vertices"], v["margin_at_smallest"])
                 for k, v in r["by"].items()]
        print("#%-8d %-44s %s" % (r["id"], r["text"], " | ".join(parts)))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if sys.argv[1] == "summary":
        summary(*sys.argv[2:6])
        sys.exit(0)
    corpus = read_corpus(sys.argv[1])
    if sys.argv[2] == "validate":
        validate(corpus)
    elif sys.argv[2] == "control":
        control(corpus, sys.argv[3], sys.argv[4])
    elif sys.argv[2] == "big":
        big(corpus, sys.argv[3])
    else:
        scan(corpus, sys.argv[3])
