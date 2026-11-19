# The best constant in `λ₂ ≤ μ₁ − c` is `c = 1`, checked in Lean 4

Sulaymon Sadullo, November 2026

| Part | Where |
|---|---|
| Solution | [`SOLUTION.md`](SOLUTION.md): the argument in a few pages, with every certificate written out |
| Lean formalization | this repository: [`Conj2/`](Conj2), nine files; see [What is proved](#what-is-proved) and [Building](#building) |
| Paper | [`paper/paper.pdf`](paper/paper.pdf), 14 pages |
| Exposition | [`exposition/index.html`](https://sulayman22s.github.io/gap-is-one/exposition/), a web page for readers outside the area |
| Potential applications | [`applications/index.html`](https://sulayman22s.github.io/gap-is-one/applications/), a web page |

Project website: <https://sulayman22s.github.io/gap-is-one/>

For a connected simple graph `G` on `n ≥ 2` vertices write

- `λ₂(G)` for the second largest eigenvalue of its adjacency matrix, and
- `μ₁(G)` for the largest eigenvalue of its Laplacian matrix `D − A`

(eigenvalues counted with multiplicity). The bound `λ₂(G) ≤ μ₁(G) − 1` is known: it follows from
`λ₂ ≤ λ₁ ≤ Δ` and the theorem of Grone and Merris that `μ₁ ≥ Δ + 1` (`Δ` the maximum degree),
and also from the stronger `μ₂ ≥ λ₂ + 1`, which is Theorem 1 of T. Cazenave, *Lemmas and
Conjectures in Spectral Graph Theory* ([arXiv:2611.03879](https://arxiv.org/abs/2611.03879)).
Conjecture 2 of that paper (corpus #20829) states that the constant can be improved to `2`:
`λ₂(G) ≤ μ₁(G) − 2`. The corpus behind the paper lists the same inequality with the constants
`√2` (#121082, also printed in Table 3 of the workshop paper of Duhamel and Cazenave) and
`√√2` (#717992) as open. See [Related work](#related-work) for sources.

This project proves in Lean 4 with Mathlib that **the constant `1` cannot be improved at all**:

> `λ₂(G) ≤ μ₁(G) − c` holds for every connected simple graph `G` on `n ≥ 2` vertices
> **if and only if** `c ≤ 1`.

In particular all three conjectures are false. Conjecture 2 already fails on 11 vertices, and
on `n` vertices for every `n ≥ 11`.

An illustrated account for readers outside the area is in
[`exposition/index.html`](https://sulayman22s.github.io/gap-is-one/exposition/). What follows from the result is in
[`applications/index.html`](https://sulayman22s.github.io/gap-is-one/applications/): among other things, the graphs of the proof
violate 125 of the 14,150 open conjectures of the corpus in floating-point arithmetic
(`applications/refuted_open_rows.csv`, reproducible with `applications/corpus_scan.py`). Only the
four conjectures of the form `λ₂ ≤ μ₁ − c` are proved false in Lean.

The paper is [`paper/paper.pdf`](paper/paper.pdf) (source `paper/paper.tex`, built with
`bash paper/build.sh`). Besides the formalized theorems it proves by hand, from exact formulas
for the graphs `T m 1`, that eighteen further open conjectures of the corpus about the Randić
index are false, and it gives necessary conditions for a counterexample to Conjecture 2.
`python paper/check_numbers.py` re-computes the numbers of the paper: the certificates with
exact fractions (Python only), the statements proved by hand against eigenvalues computed
from the matrices (needs numpy).

## What is proved

| Lean name | Statement |
|---|---|
| `Conj2.best_constant` | `(∀ n ≥ 2, ∀ G : SimpleGraph (Fin n), G.Connected → λ₂(G) ≤ μ₁(G) − c) ↔ c ≤ 1` |
| `Conj2.lambda₂_le_mu₁_sub_one` | `λ₂(G) ≤ μ₁(G) − 1` for every connected `G` on `n ≥ 2` vertices |
| `Conj2.Sharp.exists_gap_lt` | for every `ε > 0` there is a connected graph with `μ₁ − λ₂ < 1 + ε` |
| `Conj2.Sharp.exists_gap_le` | the graph `T m t` has `μ₁ − λ₂ ≤ 1 + 3/s + (s² − s)/(m + s)`, `s = t + 1` |
| `Conj2.Sharp.no_constant_above_one` | for every `c > 1` the inequality with constant `c` fails |
| `Conj2.Sharp.conjecture_sqrt_two_false` | `λ₂ ≤ μ₁ − √2` is false |
| `Conj2.Sharp.conjecture_fourth_root_two_false` | `λ₂ ≤ μ₁ − √√2` is false |
| `Conj2.conjecture_two_false` | Conjecture 2 is false (explicit 11-vertex graph `G11`) |
| `Conj2.counterexample_gap` | `13/888 ≤ λ₂(G11) − (μ₁(G11) − 2)` |
| `Conj2.Family.exists_counterexample` | `∀ n ≥ 11, ∃ G : SimpleGraph (Fin n), G.Connected ∧ μ₁(G) − 2 < λ₂(G)` |
| `Conj2.Family.counterexample_of_card` | the same with `2 ≤ n` as an explicit hypothesis, so that the statement contains no proof term |
| `Conj2.Family.conjecture_two_false_of_card` | for every `n ≥ 11` Conjecture 2 fails on `Fin n` |
| `Conj2.Family.family_gap` | `∀ N, 13/888 ≤ λ₂(D N) − (μ₁(D N) − 2)` |

`λ₂` and `μ₁` are `Matrix.IsHermitian.eigenvalues₀` (Mathlib's decreasing list of eigenvalues
with multiplicity) of `G.adjMatrix ℝ` at index `1` and of `G.lapMatrix ℝ` at index `0`.

## The graphs

**`T m t`** (`Conj2.Sharp.sg m t`), for the sharp constant. A *cluster* is a complete split
graph: a clique on `m` vertices plus `s = t + 1` further vertices, each joined to every clique
vertex and to nothing else. `T m t` is two clusters and one connector vertex joined to one
non-clique vertex of each. Its maximum degree is `Δ = m + s − 1`, and

- `μ₁ ≤ m + s + 3/s = Δ + 1 + 3/s`,
- `λ₂ ≥ (m(m−1) + 2ms)/(m+s)`, the average degree of a cluster,

so `μ₁ − λ₂ ≤ 1 + 3/s + (s² − s)/(m + s)`, which tends to `1` for `s → ∞`, `m = s³`.

**`G₁₁`** (`Conj2.G11`), the smallest counterexample to Conjecture 2 that we know: two diamonds
(`K₄` minus an edge) joined by a path with three inner vertices; 11 vertices, 14 edges. The paper
reports that the conjecture was tested on all connected graphs with at most 9 vertices, so a
smallest counterexample has 10 or 11 vertices; the case of 10 vertices is not settled here.

```
diamond 1:  0-2  0-3  1-2  1-3  2-3
diamond 2:  4-6  4-7  5-6  5-7  6-7
path:       0-8  8-9  9-10  10-4
```

Numerically `λ₂(G₁₁) ≈ 2.6412` and `μ₁(G₁₁) = (7 + √5)/2 ≈ 4.6180`.

**`D N`** (`Conj2.Family.fam N`): the same two diamonds joined by a path with `N + 3` inner
vertices; `N + 11` vertices; `D 0` is `G₁₁` with its vertices renamed
(`Conj2.Family.fam_zero_eq_G11`). Every `D N` has `μ₁ ≤ 37/8` and `λ₂ ≥ 293/111`.

## How the proofs go

All eigenvalue bounds come from two general facts about a real symmetric matrix `A`
(`Conj2/Rayleigh.lean`, derived from Mathlib's spectral theorem):

- if `zᵀAz ≤ c‖z‖²` for all `z`, then every eigenvalue of `A` is at most `c`;
- if two orthogonal vectors, not coupled by `A`, both have Rayleigh quotient at least `c`, then
  the second largest eigenvalue is at least `c` (two-dimensional Courant–Fischer).

So an upper bound on `μ₁` is an inequality between quadratic forms, proved by exhibiting
`c‖z‖² − zᵀLz` as a sum of squares; a lower bound on `λ₂` is a pair of test vectors.

| File | Content |
|---|---|
| `Conj2/Rayleigh.lean` | the two general facts above |
| `Conj2/Graph.lean` | `G11`, its edge list, connectivity, its quadratic forms as polynomials |
| `Conj2/Main.lean` | `μ₁(G11) ≤ 37/8` (17 squares), `λ₂(G11) ≥ 293/111`, Conjecture 2 is false |
| `Conj2/PathLemmas.lean` | sums along a path; weighted path inequalities by induction on the length |
| `Conj2/Family.lean` | the graphs `D N`; the same two bounds for every `N` |
| `Conj2/SharpLemmas.lean` | sums of squared differences over a clique; the cluster inequality `cluster_core` |
| `Conj2/Transfer.lean` | certificates checked on a structured vertex set transfer to `Fin n` |
| `Conj2/Sharp.lean` | the graphs `T m t`; `μ₁ − λ₂ ≤ 1 + 3/s + (s²−s)/(m+s)`; no constant above 1 |
| `Conj2/BestConstant.lean` | `λ₂ ≤ Δ`, `μ₁ ≥ Δ + 1` (star test vector), and `best_constant` |

The cluster inequality behind `T m t`: write `σ` for the sum over the clique, `α` for the value
at the attachment vertex and `ω` for the sum over the other non-clique vertices. With
`M = m + s + 3/s`, the quantity `M‖z‖² − zᵀLz − 2α²` on a cluster equals

```
(3/s)·Σ_clique z² + (σ + α + ω)² + [(s + 3/s − 3)α² − 2αω + (s + 3/s)·Σ_others z² − ω²],
```

and the bracket is non-negative by Cauchy–Schwarz (`ω² ≤ (s−1)·Σ_others z²`) and the identity
`(s + 3/s − 3)(1 + 3/s) − (s − 1) = (1 − 3/s)²`.

## The statement, for an independent check

Three files follow the layout that `lake comparator` expects. It is the layout of the Principia
and Palomar templates for Lean formalizations.

- [`Challenge.lean`](Challenge.lean) contains the two definitions and three theorems, each left
  as `sorry`: `Conj2.best_constant`, `Conj2.conjecture_two_false` and
  `Conj2.Family.counterexample_of_card`. It imports only Mathlib. Read this file to see exactly
  what is claimed.
- [`Solution.lean`](Solution.lean) is the whole proof in one module. It is generated from the
  nine files of `Conj2/` by `python tools/make_solution.py`.
- [`comparator.json`](comparator.json) names the three theorems and the permitted axioms.

`lake comparator` builds both modules. It checks that every named theorem has the same statement
in both and that the definitions it uses are identical, that no axiom outside the list is used,
and it replays the proofs through Lean's kernel and through two independent checkers, nanoda
and con-ron. It needs Linux with `bubblewrap`. The workflow in `.github/workflows/lean.yml` runs
it, together with the build, the audit and the false variants, on every change.

## Related work

Searched on 18 November 2026 (web search, arXiv listings and abstract search, OpenAlex, the
paper's own archive).

**Known before this project.**

- `μ₁ ≥ Δ + 1` for a graph with at least one edge: R. Grone and R. Merris, *The Laplacian
  spectrum of a graph II*, SIAM J. Discrete Math. 7 (1994) 221–229; stated as Theorem 3.19 in
  X.-D. Zhang, *The Laplacian eigenvalues of graphs: a survey*, arXiv:1111.2897. With `λ₁ ≤ Δ`
  it gives `λ₂ ≤ λ₁ ≤ μ₁ − 1`.
- `μ₂ ≥ λ₂ + 1` for connected graphs: Theorem 1 of arXiv:2611.03879 (verified in Lean by its
  author), who notes that it "only gives" `λ₂ ≤ μ₂ − 1 ≤ μ₁ − 1`. The corpus rows `λ₂ ≤ μ₁ − 1`
  (#20828) and `λ₁ ≤ μ₁ − 1` (#19612) are marked proved.
- Bounds on `μ₁ − λ₁` with their extremal graphs: H. Lin, Y. Hong and J. Shu, *Some relations
  between the eigenvalues of adjacency, Laplacian and signless Laplacian matrix of a graph*,
  Graphs Combin. 31 (2015) 669–677 (abstract read; full text not available to us).

So the direction "`c ≤ 1` works" of `Conj2.best_constant` is not new. It is proved again here
(`Conj2.lambda₂_le_mu₁_sub_one`) so that the project depends on Mathlib only.

**What this project adds, as far as the search found.** No constant larger than `1` works: the
infimum of `μ₁ − λ₂` over connected graphs is `1` (not attained). This settles every row of the
corpus of the form `λ₂ ≤ μ₁ − c` with `c` a constant: the rows with `c ∈ {−1, log √2, 1/2, 1}`
are marked proved there, and the rows marked open, `c = √√2` (#717992), `c = √2` (#121082) and
`c = 2` (#20829, and #723906 written as `(μ₁ − 1) − 1`), are false.

**Earlier attempts found.** arXiv lists only version 1 of the paper (2 November 2026) and
OpenAlex lists no citing work. A public automated-research repository
(`the-omega-institute/trureturing`, issue 26790, 5 November 2026) records an attempt on
Conjecture 2 that ended without a proof or a counterexample. We found no published refutation
and no earlier statement that the constant `1` is best possible. This is the result of a
bounded search, not a guarantee of priority.

**Sources for the conjectures.** T. Cazenave, arXiv:2611.03879 (Conjecture 2; Theorem 1);
E. Duhamel and T. Cazenave, *Spectral Graph Theory Conjecture Generation*, AAAI 2026 Workshop
AI for Research (Table 3 lists `λ₂ ≤ μ₁ − √2`; equation (1) gives `λ₁ ≤ μ₁ − 1` as an example);
the corpus file `index_conjectures.csv` in the archive of arXiv:2611.03879.

## How this was made

A computer search found the first counterexample, `G₁₁`. The constructions, the proofs, the Lean
code, the programs, the paper and the two web pages were written by an AI system (Claude, by
Anthropic, used through Claude Code in November 2026), directed by the author. Three kinds of
statement appear in this project, and each is labelled where it is made:

- checked by the Lean kernel: everything in [What is proved](#what-is-proved);
- proved by hand in the paper and not formalized: the exact value of `λ₂(T m t)`, the results
  on the Randić index, the 10-vertex graph `H₁₀`, the necessary conditions for a counterexample;
- numerical only: the scan of the corpus, apart from the rows covered by the two items above.

## Building

Lean `v4.36.0-rc1`, Mathlib `v4.36.0-rc1` (pinned in `lean-toolchain` and `lake-manifest.json`).

```
lake exe cache get
lake build
lake env lean Check.lean
```

`Check.lean` prints the main statements and their axioms. Expected:
`[propext, Classical.choice, Quot.sound]` and nothing else. The proof files (`Conj2/` and
`Solution.lean`) contain no `sorry` and no `native_decide`. `Challenge.lean` states three theorems
and leaves each as `sorry` on purpose, so `lake build` prints three warnings for it.

On a machine that is short of free memory, plain `lake build` can fail with
`failed to read file … .olean`, because it compiles independent files in parallel and every Lean
process loads all of Mathlib. `bash build.sh` builds one file at a time and then runs the audit;
`bash build.sh clean` rebuilds from scratch (several minutes).

The folder `controls/` holds deliberately false variants of several statements, together with a
few true ones, as a check that the build is not vacuous. They are not part of the library;
`lake env lean controls/NegativeControlsSharp.lean` must report exactly 5 errors,
`controls/NegativeControlsFamily.lean` exactly 4 and `controls/NegativeControls.lean` exactly 3.

## Licence

The code and the texts of this repository are released under the MIT licence; see
[`LICENSE`](LICENSE). The file `applications/refuted_open_rows.csv` quotes statements of
conjectures from the corpus of Duhamel and Cazenave. Those statements are theirs.
