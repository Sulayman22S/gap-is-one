# Solution: the best constant in `λ₂ ≤ μ₁ − c` is 1

Sulaymon Sadullo, November 2026

This is the short write-up of the mathematics. The paper ([`paper/paper.pdf`](paper/paper.pdf))
has the same material with full proofs and references. A statement marked **[Lean]** is
machine-checked in this repository. A statement marked **[hand]** is proved in the paper and
not formalized. A statement marked **[numerical]** was only computed.

## 1. The question

Let `G` be a connected simple graph with `n ≥ 2` vertices, `A` its adjacency matrix and
`L = D − A` its Laplacian matrix, where `D` is the diagonal matrix of degrees. Write

- `λ₁ ≥ λ₂ ≥ …` for the eigenvalues of `A`,
- `μ₁` for the largest eigenvalue of `L`,
- `Δ` for the largest degree.

It is known that `λ₂ ≤ λ₁ ≤ Δ ≤ μ₁ − 1`. The last step is a theorem of Grone and Merris (1994).

**Conjecture 2** of T. Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*
([arXiv:2611.03879](https://arxiv.org/abs/2611.03879)), asks for one unit more:
`λ₂ ≤ μ₁ − 2` for every connected graph. The conjecture came out of a corpus of 305,755
machine-generated inequalities. It holds for all connected graphs with at most 9 vertices, and
on paths the difference `μ₁ − λ₂` decreases to 2.

## 2. The answer

**Theorem A [Lean].** The graph `G₁₁` of section 4 has `μ₁ ≤ 37/8` and `λ₂ ≥ 293/111`. So
`λ₂ − (μ₁ − 2) ≥ 13/888 > 0`, and Conjecture 2 is false.

**Theorem B [Lean].** For every `n ≥ 11` there is a connected graph on `n` vertices with
`λ₂ > μ₁ − 2`.

**Theorem C [Lean].** Let `c` be a real number. The inequality `λ₂(G) ≤ μ₁(G) − c` holds for
every connected graph `G` with at least 2 vertices if and only if `c ≤ 1`.

So the infimum of `μ₁ − λ₂` over connected graphs is 1. It is not attained, because
`λ₂ < λ₁` in a connected graph. The corpus also lists the inequality with `√2` and with `⁴√2` in
place of 2 as open; Theorem C shows that both are false.

Only the direction "no constant above 1 works" is new. The direction "`c ≤ 1` works" is the
known bound above; it is proved again in Lean so that the formal statement is complete.

## 3. Two tests for eigenvalues

For a vector `x` indexed by the vertices,

```
xᵀAx = 2 · Σ over edges uv of x_u·x_v          xᵀLx = Σ over edges uv of (x_u − x_v)²
```

Everything below uses two facts about a real symmetric matrix `M`.

- **Upper test.** If `xᵀMx ≤ c·xᵀx` for every `x`, then every eigenvalue of `M` is at most `c`.
- **Two-vector test.** If `f` and `g` are non-zero, `fᵀg = 0`, `fᵀMg = 0`, and both
  `fᵀMf ≥ c·fᵀf` and `gᵀMg ≥ c·gᵀg`, then the second largest eigenvalue of `M` is at least `c`.
  This is the Courant–Fischer theorem on the plane spanned by `f` and `g`.

For an adjacency matrix the two conditions `fᵀg = 0` and `fᵀAg = 0` hold as soon as `f` and `g`
live on two sets of vertices that are disjoint and have no edge between them.

So an upper bound on `μ₁` is an inequality between quadratic forms, and a way to prove it is to
write `c·xᵀx − xᵀLx` as a sum of squares. A lower bound on `λ₂` is a pair of vectors.

## 4. Eleven vertices

A *diamond* is the complete graph `K₄` with one edge removed. `G₁₁` is two diamonds joined by a
path with three inner vertices. It has 11 vertices, 14 edges, and largest degree 3.

```
   2                          6
 / | \                      / | \
1  |  0 -- 8 -- 9 -- 10 -- 4  |  5
 \ | /                      \ | /
   3                          7
```

```
diamond 1:  0-2  0-3  1-2  1-3  2-3
diamond 2:  4-6  4-7  5-6  5-7  6-7
path:       0-8  8-9  9-10  10-4
```

**`λ₂ ≥ 293/111`.** Take

```
f = (7, 6, 8, 8, 0, 0, 0, 0, 3, 0, 0)          g = (0, 0, 0, 0, 7, 6, 8, 8, 0, 0, 3)
```

with the coordinates in the order `0, 1, …, 10`. The vector `f` lives on `{0, 1, 2, 3, 8}` and
`g` on `{4, 5, 6, 7, 10}`. These sets are disjoint and no edge joins them. Then

```
fᵀAf = 2·(7·8 + 7·8 + 6·8 + 6·8 + 8·8 + 7·3) = 586        fᵀf = 49 + 36 + 64 + 64 + 9 = 222
```

and the same for `g`. The two-vector test gives `λ₂ ≥ 586/222 = 293/111 ≈ 2.6396`.

**`μ₁ ≤ 37/8`.** For real numbers `a, b, c, e, p, q` put

```
S(a,b,c,e,p,q) = (8/21)·((21/8)·b + c + e)²  + (13/14)·((14/13)·a + c + e)²
               + (13/7)·((7/13)·a + p)²      + (17/13)·((13/17)·p + q)²
               + (1/336)·(c + e)²            + (5/16)·(c − e)²
               + (1/104)·a²                  + (3/952)·p²
```

Then, for every vector `z`,

```
(37/8)·Σ z_i² − zᵀLz = S(z₀,z₁,z₂,z₃,z₈,z₉) + S(z₄,z₅,z₆,z₇,z₁₀,z₉) + (1/104)·z₉²
```

The right-hand side is a sum of 17 squares with positive coefficients, so the upper test gives
`μ₁ ≤ 37/8 = 4.625`.

**Conclusion.** `λ₂ − (μ₁ − 2) ≥ 293/111 − 37/8 + 2 = 13/888`.

The true values are `λ₂ = 2.64118…` and `μ₁ = (7 + √5)/2 = 4.61803…`, so the true excess is
about `0.0232` **[numerical]**.

**Why this graph.** Put the two removed edges back and you get a barbell: two copies of `K₄` and
a path. In the barbell the two vertices where the path attaches have degree 4, so `μ₁ ≥ 5`.
Removing one edge at each of them lowers the largest degree to 3. That lowers `μ₁` by `0.510`
and `λ₂` by only `0.445`, and the gap `μ₁ − λ₂` drops from `2.042` to `1.977` **[numerical]**.

## 5. Every size from eleven up

For `k ≥ 3` let `D_k` be two diamonds joined, at a vertex of degree 2 of each, by a path with `k`
inner vertices `p₁, …, p_k`. It has `k + 8` vertices, and `D₃ = G₁₁`.

**Claim [Lean].** `μ₁(D_k) ≤ 37/8` and `λ₂(D_k) ≥ 293/111` for every `k ≥ 3`.

The lower bound uses the same two vectors: `7, 6, 8, 8` on a diamond (7 at the vertex where the
path attaches), `3` on the neighbouring path vertex, `0` elsewhere. Their supports have no edge
between them because `p₁` and `p_k` are different and not adjacent. That is where `k ≥ 3` is
used. For `k = 2` the gap is `2.037`, so `D₂` is not a counterexample **[numerical]**.

The upper bound splits `zᵀLz` into three parts and bounds each one.

- *A diamond with the edge to the path.* For all real `a, b, c, e, p`,

  ```
  (a−c)² + (a−e)² + (b−c)² + (b−e)² + (c−e)² + (p−a)²  ≤  (37/8)·(a² + b² + c² + e²) + (20/7)·p²
  ```

  The difference of the two sides is the sum of six squares

  ```
  (8/21)·((21/8)·b + c + e)² + (13/14)·((14/13)·a + c + e)² + (13/7)·((7/13)·a + p)²
     + (1/336)·(c + e)² + (5/16)·(c − e)² + (1/104)·a²
  ```

- *The path.* For `r ≥ 2` and real `y₀, …, y_r`,

  ```
  Σ_{i=0}^{r−1} (y_i − y_{i+1})²  ≤  (30/17)·(y₀² + y_r²) + (37/8)·Σ_{i=1}^{r−1} y_i²
  ```

  This follows from `(a − b)² ≤ (1 + t)·a² + (1 + 1/t)·b²`, with `t = 13/17` on the first and the
  last edge and `t = 1` on the others. An inner vertex receives at most `60/13 < 37/8`.

Add the three bounds. The vertices `p₁` and `p_k` receive `20/7 + 30/17 = 550/119 < 37/8`, and
every other vertex receives at most `37/8`. So `zᵀLz ≤ (37/8)·zᵀz`.

Theorem B follows with `G = D_{n−8}`.

## 6. No constant above 1

A *cluster* `C(m, s)` is a clique on `m` vertices (the core) together with `s` more vertices
(the satellites), each joined to every core vertex and to nothing else. The graph `T(m, s)`,
for `m ≥ 2` and `s ≥ 2`, is two clusters and one more vertex, the connector, joined to one
satellite of each cluster. These two satellites are the attachment vertices.

`T(m, s)` has `2(m + s) + 1` vertices. Core vertices have degree `m + s − 1`, attachment vertices
`m + 1`, the other satellites `m`, and the connector 2. So `Δ = m + s − 1`.

The idea: by the known bound, `μ₁ − λ₂` can only be close to 1 if `λ₂` is close to `Δ` and `μ₁`
is close to `Δ + 1`. The first needs two separate parts in which almost every vertex has degree
almost `Δ`. The second breaks as soon as anything is attached to a vertex of largest degree.
In a cluster the satellites have smaller degree than the core, so the two clusters can be
joined there without raising `Δ`.

**Cluster inequality [Lean].** Let `a` be a satellite of a cluster. For every vector `z` on the
cluster,

```
Σ over edges uv of the cluster of (z_u − z_v)²  +  2·z_a²   ≤   (m + s + 3/s) · Σ z_v²
```

*Proof.* Write `σ` and `P` for the sum and the sum of squares of `z` over the core, `α = z_a`,
and `ω` and `Q` for the sum and the sum of squares over the other satellites. The core edges
contribute `mP − σ²`, and the edges between core and satellites contribute
`sP − 2σ(α + ω) + m(α² + Q)`. With `η = 3/s`, the right-hand side minus the left-hand side
equals

```
η·P + (σ + α + ω)² + [ (s + η − 3)·α² − 2αω + (s + η)·Q − ω² ]
```

By Cauchy–Schwarz `ω² ≤ (s − 1)·Q`, so the bracket is at least
`(s + η − 3)·α² − 2αω + ((1 + η)/(s − 1))·ω²`. This quadratic form in `(α, ω)` is non-negative,
because its two coefficients are positive and

```
(s + η − 3)·(1 + η) − (s − 1) = (1 − 3/s)² ≥ 0
```

**Upper bound [Lean].** `μ₁(T(m, s)) ≤ m + s + 3/s`. For the two edges at the connector `c`,
`(z_c − z_a)² ≤ 2·z_c² + 2·z_a²`. So `zᵀLz` is at most `4·z_c²` plus, for each cluster, the
left-hand side of the cluster inequality. Since `4 ≤ m + s + 3/s`, the upper test applies.

**Lower bound [Lean].** `λ₂(T(m, s)) ≥ (m(m − 1) + 2ms)/(m + s)`. Take the two vectors that are
1 on one cluster and 0 elsewhere. A cluster has `m(m − 1)/2 + ms` edges and `m + s` vertices, and
the connector keeps the two supports apart.

**The gap [Lean].** Subtracting,

```
μ₁(T(m, s)) − λ₂(T(m, s))  ≤  1 + 3/s + (s² − s)/(m + s)
```

*Proof of Theorem C.* If `c ≤ 1`, the inequality is the known bound. If `c > 1`, choose an
integer `s ≥ 2` with `4/s < c − 1` and put `m = s³`. Then `(s² − s)/(m + s) < 1/s`, so
`μ₁ − λ₂ < 1 + 4/s < c` on the connected graph `T(s³, s)`.

| `c` | `s` | `m = s³` | vertices | bound on `μ₁ − λ₂` |
|---|---|---|---|---|
| `2` | 5 | 125 | 261 | 1.7538 |
| `√2 ≈ 1.4142` | 10 | 1000 | 2021 | 1.3891 |
| `⁴√2 ≈ 1.1892` | 22 | 10648 | 21341 | 1.1797 |

These are the graphs the proof produces. Smaller ones do the same job: `G₁₁` for `c = 2`.

## 7. What else the paper proves

All of this is **[hand]**: proved in the paper, not formalized.

- `λ₂(T(m, s)) = ((m − 1) + √((m − 1)² + 4ms))/2` exactly. Delete the connector, and
  interlacing squeezes `λ₂` between the largest eigenvalues of the two clusters.
- The Randić index `R` is the sum of `1/√(d_u·d_v)` over the edges `uv`, where `d_v` is the
  degree of `v`. The graph `T(m, 2)` has radius 3, diameter 6 and
  `R = m + 2·√(m/(m + 1)) + √(2/(m + 1))`, so `R − λ₂` tends to 1. Seventeen open conjectures of
  the corpus say `λ₂ ≤ R − f`, where `f` depends on the radius and the diameter and exceeds 1
  at radius 3 and diameter 6. All seventeen are false, and so is one more of a similar kind.
- One of them, `λ₂ ≤ R − radius/2`, already fails on 10 vertices, with an exact certificate.
- A counterexample to Conjecture 2 cannot be bipartite, has `λ₂ > Δ − 1`, and has at least
  `2Δ + 2` vertices. So `Δ ≥ 3`, and the smallest counterexample has 10 or 11 vertices. Whether
  there is one with 10 is open.

## 8. How to check this

- **Lean.** `lake exe cache get`, then `lake build`, then `lake env lean Check.lean`. The last
  command prints the main statements and the axioms they depend on. See the
  [README](README.md) for details and for the names of the theorems.
- **By computer, without Lean.** `python paper/check_numbers.py` re-computes every certificate
  of sections 4 to 6 with exact fractions, and compares the formulas of section 7 with
  eigenvalues computed from the matrices. The first part needs only Python; the second needs
  numpy.
- **By hand.** Sections 4 to 6 use nothing beyond expanding squares.

## References

- T. Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*, arXiv:2611.03879, 2026.
- E. Duhamel and T. Cazenave, *Spectral Graph Theory Conjecture Generation*, AAAI 2026 Workshop
  AI for Research, 2026.
- R. Grone and R. Merris, *The Laplacian spectrum of a graph II*, SIAM Journal on Discrete
  Mathematics 7 (1994), 221–229.

A computer search found the first counterexample. The proofs, the Lean code and this write-up
were written by an AI system (Claude, by Anthropic), directed by the author. Every formal proof
is checked by the Lean kernel.
