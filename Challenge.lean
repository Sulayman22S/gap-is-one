module

public import Mathlib

@[expose] public section

/-!
# The best constant in `λ₂ ≤ μ₁ − c` is `1`: the statements

This file is the statement surface. It imports only Mathlib, and every theorem in it is left as
`sorry`. `Solution.lean` proves each one, and `comparator.json` lists them.

Throughout, `G` is a simple graph on the vertex set `Fin n` with `n ≥ 2`.

* `lambda₂ G h` is `λ₂(G)`, the second largest eigenvalue of the adjacency matrix of `G` over
  `ℝ`, counted with multiplicity.
* `mu₁ G h` is `μ₁(G)`, the largest eigenvalue of the Laplacian matrix `D − A` of `G` over `ℝ`.

Both are read off `Matrix.IsHermitian.eigenvalues₀`, Mathlib's list of the eigenvalues of a
Hermitian matrix in decreasing order (`Matrix.IsHermitian.eigenvalues₀_antitone`), at the indices
`1` and `0`. The argument `h : 2 ≤ n` only shows that these indices exist.

Conjecture 2 of T. Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*
(arXiv:2611.03879), asserts `λ₂(G) ≤ μ₁(G) − 2` for every connected graph.

* `conjecture_two_false` says that this conjecture is false.
* `Family.counterexample_of_card` says that it fails on `n` vertices for every `n ≥ 11`.
* `best_constant` says that `λ₂(G) ≤ μ₁(G) − c` holds for every connected graph on at least two
  vertices if and only if `c ≤ 1`.

The direction `c ≤ 1` of `best_constant` is a known bound: `λ₂ ≤ Δ` and, by a theorem of Grone
and Merris (1994), `μ₁ ≥ Δ + 1`, where `Δ` is the maximum degree.
-/

open Matrix SimpleGraph

namespace Conj2

/-- `λ₂(G)`: the second largest eigenvalue (with multiplicity) of the adjacency matrix.

`Matrix.IsHermitian.eigenvalues₀` lists the eigenvalues of a Hermitian matrix with multiplicity
in decreasing order (`Matrix.IsHermitian.eigenvalues₀_antitone`), so index `1` is the second
largest. The hypothesis `h` only serves to show that the index `1` exists. Its proof is written as
a term, not with tactics, so that `Challenge.lean` and `Solution.lean` elaborate it identically. -/
noncomputable def lambda₂ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : 2 ≤ n) : ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀
    ⟨1, lt_of_lt_of_eq (Nat.lt_of_succ_le h) (Fintype.card_fin n).symm⟩

/-- `μ₁(G)`: the largest eigenvalue of the Laplacian matrix `D − A` (index `0` of the decreasing
list `Matrix.IsHermitian.eigenvalues₀`). The hypothesis `h` only serves to show that the index `0`
exists. -/
noncomputable def mu₁ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : 2 ≤ n) : ℝ :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues₀
    ⟨0, lt_of_lt_of_eq (Nat.lt_of_lt_of_le Nat.zero_lt_two h) (Fintype.card_fin n).symm⟩

/-- **Conjecture 2 of arXiv:2611.03879 is false.** It is not true that `λ₂(G) ≤ μ₁(G) − 2` for
every connected simple graph `G` on at least two vertices. -/
theorem conjecture_two_false :
    ¬ ∀ (n : ℕ) (h : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → lambda₂ G h ≤ mu₁ G h - 2 := by
  sorry

namespace Family

/-- **A counterexample on every number of vertices `n ≥ 11`.** For every `n ≥ 11` there is a
connected simple graph on `Fin n` with `μ₁ − 2 < λ₂`. The hypothesis `2 ≤ n` is passed explicitly,
so that the statement contains no proof term of its own. -/
theorem counterexample_of_card (n : ℕ) (h2 : 2 ≤ n) (h11 : 11 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ mu₁ G h2 - 2 < lambda₂ G h2 := by
  sorry

end Family

/-- **The best constant is `1`.** The inequality `λ₂(G) ≤ μ₁(G) − c` holds for every connected
simple graph `G` on `n ≥ 2` vertices if and only if `c ≤ 1`. -/
theorem best_constant (c : ℝ) :
    (∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → lambda₂ G hn ≤ mu₁ G hn - c) ↔ c ≤ 1 := by
  sorry

end Conj2
