"""Re-computes the numbers quoted in SOLUTION.md and in the paper.

Part 1 uses exact rational arithmetic and the standard library only. It checks the finite
certificates: the test vectors and the sum of squares for G11, the two lemmas behind the
family D_k, the cluster inequality for small parameters, and the fractions for H10.

Part 2 needs numpy. It compares the closed formulas that the paper proves by hand with
eigenvalues computed from the matrices, recomputes the last column of Table 1, and prints
the decimal values quoted in the remarks.

    python check_numbers.py        (part 2 is skipped when numpy is not installed)

This does not replace the Lean proof. It is an independent check that the certificates are
printed correctly and that the statements proved only by hand agree with computation."""
import sys
from decimal import Decimal, getcontext
from fractions import Fraction as F

FAILED = []


def check(label, ok, detail=""):
    print(("  ok    " if ok else "  FAIL  ") + label + (("   " + detail) if detail else ""))
    if not ok:
        FAILED.append(label)


# ---------------------------------------------------------------- exact linear algebra
def quad(terms, n):
    """Matrix of the quadratic form  sum_k w_k (linear form_k)^2."""
    S = [[F(0)] * n for _ in range(n)]
    for w, form in terms:
        for i, x in form.items():
            for j, y in form.items():
                S[i][j] += F(w) * x * y
    return S


def laplacian(n, edges):
    return quad([(1, {u: 1, v: -1}) for u, v in edges], n)


def adjacency(n, edges):
    A = [[F(0)] * n for _ in range(n)]
    for u, v in edges:
        A[u][v] = A[v][u] = F(1)
    return A


def form(M, x, y):
    return sum(x[i] * M[i][j] * y[j] for i in range(len(x)) for j in range(len(y)))


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def scaled_identity_minus(c, M):
    n = len(M)
    return [[(F(c) if i == j else 0) - M[i][j] for j in range(n)] for i in range(n)]


def psd(M):
    """Exact test that a symmetric rational matrix is positive semidefinite (LDL^T)."""
    n = len(M)
    M = [r[:] for r in M]
    for k in range(n):
        p = M[k][k]
        if p < 0:
            return False
        if p == 0:
            if any(M[i][k] != 0 for i in range(k + 1, n)):
                return False
            continue
        for i in range(k + 1, n):
            f = M[i][k] / p
            if f:
                for j in range(k, n):
                    M[i][j] -= f * M[k][j]
    return True


def charpoly(M):
    """Coefficients of det(xI - M), leading coefficient first (Faddeev-LeVerrier)."""
    n = len(M)
    c = [F(1)]
    Mk = [[F(0)] * n for _ in range(n)]
    for k in range(1, n + 1):
        T = [[Mk[i][j] + (c[k - 1] if i == j else 0) for j in range(n)] for i in range(n)]
        Mk = [[sum(M[i][t] * T[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
        c.append(-sum(Mk[i][i] for i in range(n)) / k)
    return c


def polymul(p, q):
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += F(a) * b
    return out


def eccentricities(n, edges):
    nb = [[] for _ in range(n)]
    for u, v in edges:
        nb[u].append(v)
        nb[v].append(u)
    ecc = []
    for s in range(n):
        dist = {s: 0}
        queue = [s]
        for u in queue:
            for v in nb[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    queue.append(v)
        assert len(dist) == n, "graph is not connected"
        ecc.append(max(dist.values()))
    return ecc


# ---------------------------------------------------------------- the graphs
G11_EDGES = [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
             (4, 6), (4, 7), (5, 6), (5, 7), (6, 7),
             (0, 8), (8, 9), (9, 10), (10, 4)]


def block_path(d, k, drop=True):
    """Two copies of K_{d+1}, each without one edge at its attachment vertex when `drop`,
    joined by a path with k inner vertices. Returns (n, edges, attach1, attach2, path)."""
    b = d + 1
    edges = []
    for off in (0, b):
        for i in range(b):
            for j in range(i + 1, b):
                if drop and (i, j) == (0, 1):
                    continue
                edges.append((off + i, off + j))
    path = list(range(2 * b, 2 * b + k))
    chain = [0] + path + [b]
    edges += list(zip(chain, chain[1:]))
    return 2 * b + k, edges, 0, b, path


def cluster_graph(m, s):
    """T(m, s): two clusters (core 0..m-1, satellites m..m+s-1, attachment = first satellite)
    and a connector joined to the two attachment vertices."""
    c = m + s
    edges = []
    for off in (0, c):
        for i in range(m):
            for j in range(i + 1, m):
                edges.append((off + i, off + j))
            for w in range(m, c):
                edges.append((off + i, off + w))
    conn = 2 * c
    edges += [(m, conn), (c + m, conn)]
    return 2 * c + 1, edges


def h10():
    """Two copies of K_5 without the edge u-w (u = 0, w = 1 in each copy), plus the edge u-u'."""
    edges = []
    for off in (0, 5):
        for i in range(5):
            for j in range(i + 1, 5):
                if (i, j) != (0, 1):
                    edges.append((off + i, off + j))
    edges.append((0, 5))
    return 10, edges


# ================================================================ part 1: exact
def part1():
    print("PART 1  exact rational arithmetic")

    print(" G11 (Theorem 1.1)")
    n = 11
    A, L = adjacency(n, G11_EDGES), laplacian(n, G11_EDGES)
    deg = [sum(r) for r in A]
    check("11 vertices, 14 edges, maximum degree 3", len(G11_EDGES) == 14 and max(deg) == 3)
    f = [F(v) for v in (7, 6, 8, 8, 0, 0, 0, 0, 3, 0, 0)]
    g = [F(v) for v in (0, 0, 0, 0, 7, 6, 8, 8, 0, 0, 3)]
    check("f.f = g.g = 222 and f.Af = g.Ag = 586",
          dot(f, f) == dot(g, g) == 222 and form(A, f, f) == form(A, g, g) == 586)
    check("f.g = 0 and f.Ag = 0", dot(f, g) == 0 and form(A, f, g) == 0)
    check("586/222 = 293/111", F(586, 222) == F(293, 111))

    def S(a, b, c, e, p, q):
        return [(F(8, 21), {b: F(21, 8), c: 1, e: 1}), (F(13, 14), {a: F(14, 13), c: 1, e: 1}),
                (F(13, 7), {a: F(7, 13), p: 1}), (F(17, 13), {p: F(13, 17), q: 1}),
                (F(1, 336), {c: 1, e: 1}), (F(5, 16), {c: 1, e: -1}),
                (F(1, 104), {a: 1}), (F(3, 952), {p: 1})]
    squares = S(0, 1, 2, 3, 8, 9) + S(4, 5, 6, 7, 10, 9) + [(F(1, 104), {9: 1})]
    check("(37/8)|z|^2 - z.Lz is the stated sum of 17 squares",
          len(squares) == 17 and all(w > 0 for w, _ in squares)
          and quad(squares, n) == scaled_identity_minus(F(37, 8), L))
    check("293/111 - 37/8 + 2 = 13/888", F(293, 111) - F(37, 8) + 2 == F(13, 888))

    print(" diamond with a pendant vertex (Remark 3.3)")
    dp = [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4)]
    check("characteristic polynomial is (x+1)(x^4 - x^3 - 5x^2 + x + 2)",
          charpoly(adjacency(5, dp)) == polymul([1, 1], [1, -1, -5, 1, 2]))
    lap_poly = charpoly(L)
    rem = lap_poly[:]
    while len(rem) >= 3:                       # divide by x^2 - 7x + 11
        lead = rem[0]
        for i, q in enumerate((1, -7, 11)):
            rem[i] -= lead * q
        rem.pop(0)
    check("(7 + sqrt 5)/2 is a Laplacian eigenvalue of G11: x^2 - 7x + 11 divides",
          not any(rem))

    print(" the family D_k (Lemmas 4.1, 4.2, Proposition 4.3)")
    a, b, c, e, p = range(5)
    lhs = quad([(1, {a: 1, c: -1}), (1, {a: 1, e: -1}), (1, {b: 1, c: -1}),
                (1, {b: 1, e: -1}), (1, {c: 1, e: -1}), (1, {p: 1, a: -1})], 5)
    rhs = quad([(F(37, 8), {a: 1}), (F(37, 8), {b: 1}), (F(37, 8), {c: 1}), (F(37, 8), {e: 1}),
                (F(20, 7), {p: 1})], 5)
    sos = quad([(F(8, 21), {b: F(21, 8), c: 1, e: 1}), (F(13, 14), {a: F(14, 13), c: 1, e: 1}),
                (F(13, 7), {a: F(7, 13), p: 1}), (F(1, 336), {c: 1, e: 1}),
                (F(5, 16), {c: 1, e: -1}), (F(1, 104), {a: 1})], 5)
    check("Lemma 4.2: right side minus left side is the stated sum of 6 squares",
          [[rhs[i][j] - lhs[i][j] for j in range(5)] for i in range(5)] == sos)
    ok = True
    for r in range(2, 41):
        edges = quad([(1, {i: 1, i + 1: -1}) for i in range(r)], r + 1)
        bound = quad([(F(30, 17), {0: 1}), (F(30, 17), {r: 1})]
                     + [(F(37, 8), {i: 1}) for i in range(1, r)], r + 1)
        ok &= psd([[bound[i][j] - edges[i][j] for j in range(r + 1)] for i in range(r + 1)])
    check("Lemma 4.1 for r = 2..40 (difference is positive semidefinite)", ok)
    check("(a-b)^2 <= (30/17)a^2 + (30/13)b^2 is the case t = 13/17",
          1 + F(13, 17) == F(30, 17) and 1 + F(17, 13) == F(30, 13))
    check("60/13 < 37/8 and 20/7 + 30/17 = 550/119 < 37/8",
          F(60, 13) < F(37, 8) and F(20, 7) + F(30, 17) == F(550, 119) < F(37, 8))
    ok_mu = ok_la = True
    for k in range(3, 26):
        n, edges, a1, a2, path = block_path(3, k)
        ok_mu &= psd(scaled_identity_minus(F(37, 8), laplacian(n, edges)))
        A = adjacency(n, edges)
        f, g = [F(0)] * n, [F(0)] * n
        for vec, off, first in ((f, 0, path[0]), (g, 4, path[-1])):
            vec[off], vec[off + 1], vec[off + 2], vec[off + 3], vec[first] = 7, 6, 8, 8, 3
        ok_la &= (dot(f, f) == dot(g, g) == 222 and form(A, f, f) == form(A, g, g) == 586
                  and dot(f, g) == 0 and form(A, f, g) == 0)
    check("D_k for k = 3..25: (37/8)I - L is positive semidefinite", ok_mu)
    check("D_k for k = 3..25: both test vectors have quotient 293/111, no cross terms", ok_la)
    n, edges, _, _, _ = block_path(3, 3)
    relabel = sorted(sorted(e) for e in edges)
    check("D_3 has 11 vertices and 14 edges, like G11", n == 11 and len(relabel) == 14)

    print(" the graphs T(m, s) (Lemma 5.2 to Theorem 5.5)")
    ok_c = ok_w = ok_r = ok_deg = True
    for s in range(2, 8):
        for m in range(2, 8):
            M = F(m + s) + F(3, s)
            n, edges = cluster_graph(m, s)
            c = m + s
            one = [(u, v) for u, v in edges if u < c and v < c]
            T = scaled_identity_minus(M, laplacian(c, one))
            T[m][m] -= 2
            ok_c &= psd(T)
            ok_w &= psd(scaled_identity_minus(M, laplacian(n, edges)))
            A = adjacency(n, edges)
            f = [F(1)] * c + [F(0)] * (c + 1)
            g = [F(0)] * c + [F(1)] * c + [F(0)]
            ray = F(m * (m - 1) + 2 * m * s, m + s)
            ok_r &= (form(A, f, f) / dot(f, f) == form(A, g, g) / dot(g, g) == ray
                     and dot(f, g) == 0 and form(A, f, g) == 0
                     and M - ray == 1 + F(3, s) + F(s * s - s, m + s))
            deg = sorted(int(sum(r)) for r in A)
            ok_deg &= (n == 2 * (m + s) + 1 and deg[-1] == m + s - 1 and deg[0] == 2)
    check("cluster inequality for m, s = 2..7 (positive semidefinite)", ok_c)
    check("(m + s + 3/s)I - L(T(m,s)) is positive semidefinite for m, s = 2..7", ok_w)
    check("indicator vectors: quotient (m(m-1)+2ms)/(m+s), no cross terms; gap identity", ok_r)
    check("T(m,s) has 2(m+s)+1 vertices and maximum degree m+s-1", ok_deg)
    for s in (2, 3, 5, 10):
        eta = F(3, s)
        check(f"(s + 3/s - 3)(1 + 3/s) - (s - 1) = (1 - 3/s)^2 for s = {s}",
              (s + eta - 3) * (1 + eta) - (s - 1) == (1 - eta) ** 2)

    print(" Theorem 1.3: parameters s > 4/(c-1), m = s^3")
    for name, power, s in (("2", 1, 5), ("sqrt 2", 2, 10), ("fourth root of 2", 4, 22)):
        m = s ** 3
        bound = 1 + F(3, s) + F(s * s - s, m + s)
        small = (1 + F(4, s)) ** power < 2          # 1 + 4/s < c
        prev = (1 + F(4, s - 1)) ** power >= 2      # s is the least such integer
        check(f"c = {name}: s = {s}, m = {m}, {2 * (m + s) + 1} vertices, "
              f"bound {float(bound):.4f} < 1 + 4/s < c", small and prev and bound < 1 + F(4, s))

    print(" H10 (Proposition 7.2)")
    n, edges = h10()
    A = adjacency(n, edges)
    deg = [int(sum(r)) for r in A]
    ecc = eccentricities(n, edges)
    check("radius 3, attained exactly at u and u'",
          min(ecc) == 3 and [v for v in range(n) if ecc[v] == 3] == [0, 5])
    n44 = sum(1 for u, v in edges if deg[u] == deg[v] == 4)
    n34 = sum(1 for u, v in edges if {deg[u], deg[v]} == {3, 4})
    check("19 edges: 13 between degrees 4 and 4, 6 between 3 and 4, so R = 13/4 + sqrt 3",
          len(edges) == 19 and n44 == 13 and n34 == 6)       # 6/sqrt(12) = sqrt 3
    x = [F(66), F(85), F(100), F(100), F(100)]
    f, g = x + x, x + [-v for v in x]
    check("g.Ag = 292488, f.f = g.g = 83162, f.g = 0, f.Ag = 0, f.Af >= g.Ag",
          form(A, g, g) == 292488 and dot(f, f) == dot(g, g) == 83162 and dot(f, g) == 0
          and form(A, f, g) == 0 and form(A, f, f) >= form(A, g, g))
    lam = F(292488, 83162)
    check("292488/83162 = 146244/41581", lam == F(146244, 41581))
    sq = (lam - F(7, 4)) ** 2
    check("(146244/41581 - 7/4)^2 = 86382500281/27663672976 > 3, and 146244/41581 > 7/4",
          sq == F(86382500281, 27663672976) and sq > 3 and lam > F(7, 4))


# ================================================================ part 2: numerical
def part2(np):
    print("PART 2  floating point (numpy)")

    def spectra(n, edges):
        A = np.zeros((n, n))
        for u, v in edges:
            A[u, v] = A[v, u] = 1.0
        d = A.sum(axis=1)
        lam = np.linalg.eigvalsh(A)
        mu = np.linalg.eigvalsh(np.diag(d) - A)
        return lam[-2], mu[-1], d

    def randic(edges, d):
        return sum(1.0 / (d[u] * d[v]) ** 0.5 for u, v in edges)

    print(" G11 and its barbell (Remarks 3.3 and 3.4)")
    l2, m1, _ = spectra(11, G11_EDGES)
    check("lambda_2(G11) = 2.64118..., largest root of x^4 - x^3 - 5x^2 + x + 2",
          abs(l2 - 2.64118) < 1e-5 and abs(l2 ** 4 - l2 ** 3 - 5 * l2 ** 2 + l2 + 2) < 1e-9,
          f"{l2:.6f}")
    check("mu_1(G11) = (7 + sqrt 5)/2 = 4.61803...", abs(m1 - (7 + 5 ** 0.5) / 2) < 1e-10,
          f"{m1:.6f}")
    check("lambda_2 - (mu_1 - 2) is about 0.0232", abs(l2 - m1 + 2 - 0.0232) < 5e-5,
          f"{l2 - m1 + 2:.5f}")
    n, edges, _, _, _ = block_path(3, 3, drop=False)
    bl2, bm1, _ = spectra(n, edges)
    check("barbell: mu_1 = 5.128, lambda_2 = 3.086, gap 2.042",
          abs(bm1 - 5.128) < 5e-4 and abs(bl2 - 3.086) < 5e-4 and abs(bm1 - bl2 - 2.042) < 5e-4,
          f"{bm1:.4f} {bl2:.4f} {bm1 - bl2:.4f}")
    check("removing the two edges lowers mu_1 by 0.510 and lambda_2 by 0.445",
          abs(bm1 - m1 - 0.510) < 5e-4 and abs(bl2 - l2 - 0.445) < 5e-4,
          f"{bm1 - m1:.4f} {bl2 - l2:.4f}")
    ok = True
    for m in range(3, 13):
        prev = None
        for k in (1, 2, 3, 4, 6, 8, 16, 32):
            n, edges, _, _, _ = block_path(m - 1, k, drop=False)
            a, b, _ = spectra(n, edges)
            # the excess over 2 decays geometrically and is below rounding error for long paths
            ok &= (b - a > 2 - 1e-9) and (prev is None or b - a < prev + 1e-9)
            ok &= (k > 3) or (b - a > 2.0005)
            prev = b - a
    check("barbells, K_m with 3 <= m <= 12: gap not below 2, decreasing in the path length", ok)

    print(" the family D_k (remark after Theorem 1.2)")
    gaps = {}
    for k in (3, 4, 6, 10, 20, 60, 200):
        n, edges, _, _, _ = block_path(3, k)
        a, b, _ = spectra(n, edges)
        gaps[k] = b - a
    seq = [gaps[k] for k in sorted(gaps)]
    check("mu_1 - lambda_2 decreases from 1.9768 at k = 3 to 1.9226",
          abs(gaps[3] - 1.9768) < 5e-5 and abs(gaps[200] - 1.9226) < 5e-5
          and all(x > y - 1e-12 for x, y in zip(seq, seq[1:])),
          " ".join(f"{k}:{gaps[k]:.4f}" for k in sorted(gaps)))
    n, edges, _, _, _ = block_path(3, 2)
    a, b, _ = spectra(n, edges)
    check("D_2 is not a counterexample", b - a > 2, f"gap {b - a:.4f}")
    short = {}
    for d, k in ((4, 1), (4, 2), (5, 1)):
        n, edges, _, _, _ = block_path(d, k)
        a, b, _ = spectra(n, edges)
        short[(d, k)] = b - a
    check("K_5 minus an edge: gap below 2 from k = 2 on; K_6 minus an edge: from k = 1 on",
          short[(4, 1)] > 2 > short[(4, 2)] and short[(5, 1)] < 2,
          " ".join(f"d={d},k={k}:{g:.4f}" for (d, k), g in short.items()))
    big = []
    for d in (4, 5, 20, 80, 320):
        n, edges, _, _, _ = block_path(d, 12)
        a, b, _ = spectra(n, edges)
        big.append((d, b - a))
    check("larger blocks: the gap falls towards the golden ratio 1.618",
          all(x[1] > y[1] for x, y in zip(big, big[1:])) and 1.618 < big[-1][1] < 1.63,
          " ".join(f"d={d}:{g:.4f}" for d, g in big))

    print(" T(m, s): bounds and the exact value of lambda_2 (Propositions 5.3, 5.4, 5.6)")
    ok_b = ok_e = True
    for s in range(2, 7):
        for m in range(2, 31):
            n, edges = cluster_graph(m, s)
            a, b, _ = spectra(n, edges)
            ok_b &= (b <= m + s + 3 / s + 1e-9
                     and a >= (m * (m - 1) + 2 * m * s) / (m + s) - 1e-9)
            ok_e &= abs(a - ((m - 1) + ((m - 1) ** 2 + 4 * m * s) ** 0.5) / 2) < 1e-9
    check("mu_1 <= m+s+3/s and lambda_2 >= (m(m-1)+2ms)/(m+s) for s = 2..6, m = 2..30", ok_b)
    check("lambda_2 = ((m-1) + sqrt((m-1)^2 + 4ms))/2 for s = 2..6, m = 2..30", ok_e)

    def mu1_quotient(m, s):
        """mu_1 of T(m, s) from the quotient by classes of twin vertices:
        core, attachment, other satellites (twice), connector."""
        Q = np.zeros((7, 7))
        for o in (0, 3):
            Q[o, o] = s
            Q[o, o + 1] = -1
            Q[o, o + 2] = -(s - 1)
            Q[o + 1, o] = -m
            Q[o + 1, o + 1] = m + 1
            Q[o + 1, 6] = -1
            Q[o + 2, o] = -m
            Q[o + 2, o + 2] = m
            Q[6, o + 1] = -1
        Q[6, 6] = 2
        return max(np.linalg.eigvals(Q).real)

    ok = True
    for s, m in ((2, 9), (3, 14), (5, 23)):
        n, edges = cluster_graph(m, s)
        ok &= abs(spectra(n, edges)[1] - mu1_quotient(m, s)) < 1e-9
    check("quotient matrix gives the same mu_1 as the full matrix (three cases)", ok)
    out = []
    ok = True
    for s in (2, 3, 4, 6, 10):
        m = 10 ** 7
        lam = ((m - 1) + ((m - 1) ** 2 + 4.0 * m * s) ** 0.5) / 2
        theta = 1 + (((s - 1) ** 2 + 4) ** 0.5 - (s - 1)) / 2
        gap = mu1_quotient(m, s) - lam
        ok &= abs(gap - theta) < 1e-4
        out.append(f"s={s}:{gap:.4f}/{theta:.4f}")
    check("Remark 5.7 (not proved): gap at m = 10^7 against theta_s", ok, " ".join(out))

    print(" T(m, 2) and the Randic index (Theorem 1.4)")
    ok = True
    for m in range(2, 41):
        n, edges = cluster_graph(m, 2)
        a, _, d = spectra(n, edges)
        ecc = eccentricities(n, edges)
        R = m + 2 * (m / (m + 1)) ** 0.5 + (2 / (m + 1)) ** 0.5
        ok &= (min(ecc) == 3 and max(ecc) == 6 and abs(randic(edges, d) - R) < 1e-9
               and abs(a - ((m - 1) + (m * m + 6 * m + 1) ** 0.5) / 2) < 1e-9
               and n == 2 * m + 5 and max(d) == m + 1)
    check("radius 3, diameter 6, the formulas for R and lambda_2, n = 2m+5: m = 2..40", ok)

    print(" Table 1: least m for which T(m, 2) violates the inequality")
    getcontext().prec = 60
    D = Decimal

    def R_minus_lam(m):
        m = D(m)
        R = m + 2 * (m / (m + 1)).sqrt() + (2 / (m + 1)).sqrt()
        lam = ((m - 1) + (m * m + 6 * m + 1).sqrt()) / 2
        return R - lam, R, lam

    ln3 = D(3).ln()
    rows = [
        ("R - rad/2", D(3) / 2, 10),
        ("R + 1 - sqrt(diam)", D(6).sqrt() - 1, 12),
        ("R - sqrt(rad - 1)", D(2).sqrt(), 15),
        ("R - sqrt(rad/2)", (D(3) / 2).sqrt(), 47),
        ("R - sqrt(diam)/2", D(6).sqrt() / 2, 47),
        ("R - (log rad)^2", ln3 * ln3, 55),
        ("R - log rad", ln3, 225),
        ("R - log(diam/2)", ln3, 225),
        ("R - sqrt(log rad)", ln3.sqrt(), 903),
        ("R - (log rad)^(1/4)", ln3.sqrt().sqrt(), 3617),
    ]
    decreasing = all(R_minus_lam(m)[0] > R_minus_lam(m + 1)[0] for m in range(2, 4000))
    far = R_minus_lam(10 ** 9)[0]              # R - lambda_2 = 1 + sqrt(2/m) + O(1/m)
    check("R - lambda_2 is decreasing for m = 2..4000 and tends to 1",
          decreasing and 1 < far < D("1.0001")
          and abs(far - 1 - (D(2) / 10 ** 9).sqrt()) < D("1e-8"), f"{float(far):.7f} at m = 10^9")
    for name, c, stated in rows:
        least = next(m for m in range(2, 5000) if R_minus_lam(m)[0] < c)
        check(f"lambda_2 <= {name}: c = {float(c):.4f}, least m = {stated}", least == stated,
              f"computed {least}")

    def margin_708247(m):
        m = D(m)
        _, R, lam = R_minus_lam(m)
        return lam - R * ((m + 1) / (m + 4)).sqrt()

    least = next(m for m in range(2, 200) if margin_708247(m) > 0)
    check("lambda_2 <= max_v R sqrt(d_v/(n - d_v)): least m = 14", least == 14,
          f"computed {least}")
    far = margin_708247(10 ** 9)               # 1/2 - sqrt(2/m) + O(1/m)
    check("its margin tends to 1/2", D("0.4999") < far < D("0.5"), f"{float(far):.7f} at m = 10^9")
    ok = True
    for name, c, stated in rows[:6]:
        for m, expect in ((stated - 1, False), (stated, True)):
            n, edges = cluster_graph(m, 2)
            a, _, d = spectra(n, edges)
            ok &= ((a > randic(edges, d) - float(c)) == expect)
    for m, expect in ((13, False), (14, True)):
        n, edges = cluster_graph(m, 2)
        a, _, d = spectra(n, edges)
        rhs = max(randic(edges, d) * (dv / (n - dv)) ** 0.5 for dv in d)
        ok &= ((a > rhs) == expect)
    check("the same thresholds from the matrices, for the rows with least m <= 55", ok)

    print(" H10 (Proposition 7.2)")
    n, edges = h10()
    a, _, d = spectra(n, edges)
    rhs = randic(edges, d) - 1.5
    check("lambda_2 = 3.5171 and R - rad/2 = 3.4821",
          abs(a - 3.5171) < 5e-5 and abs(rhs - 3.4821) < 5e-5
          and abs(rhs - (1.75 + 3 ** 0.5)) < 1e-12 and a >= 146244 / 41581,
          f"{a:.5f} {rhs:.5f}")


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    part1()
    try:
        import numpy
    except ImportError:
        print("PART 2  skipped: numpy is not installed")
    else:
        part2(numpy)
    print()
    if FAILED:
        print(f"{len(FAILED)} check(s) FAILED:")
        for label in FAILED:
            print("  " + label)
        sys.exit(1)
    print("all checks passed")
