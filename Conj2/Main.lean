import Conj2.Rayleigh
import Conj2.Graph

/-!
# A counterexample to `λ₂ ≤ μ₁ − 2`

For a connected simple graph `G` on `n ≥ 2` vertices let `λ₂(G)` be the second largest eigenvalue
of its adjacency matrix and `μ₁(G)` the largest eigenvalue of its Laplacian matrix (eigenvalues
counted with multiplicity).

Conjecture 2 of T. Cazenave, *Lemmas and Conjectures in Spectral Graph Theory*
(arXiv:2611.03879), asserts `λ₂(G) ≤ μ₁(G) − 2` for every such graph.

This file proves that the conjecture is false. For the 11-vertex graph `G₁₁` of `Conj2.Graph`
(two diamonds joined by a path) we show

* `μ₁(G₁₁) ≤ 37/8`   (`Conj2.mu₁_G11_le`), by writing `(37/8)‖z‖² − zᵀLz` as a sum of squares;
* `λ₂(G₁₁) ≥ 293/111` (`Conj2.lambda₂_G11_ge`), by exhibiting two test vectors supported on the
  two diamonds;

and `37/8 − 2 = 21/8 < 293/111`.

## Main statements

* `Conj2.counterexample : G11.Connected ∧ mu₁ G11 _ - 2 < lambda₂ G11 _`
* `Conj2.conjecture_two_false`: the universally quantified conjecture is false.
-/

open Matrix SimpleGraph

namespace Conj2

/-- `λ₂(G)`: the second largest eigenvalue (with multiplicity) of the adjacency matrix.

`Matrix.IsHermitian.eigenvalues₀` lists the eigenvalues of a Hermitian matrix with multiplicity
in decreasing order (`Matrix.IsHermitian.eigenvalues₀_antitone`), so index `1` is the second
largest. -/
noncomputable def lambda₂ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : 2 ≤ n) : ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨1, by rw [Fintype.card_fin]; omega⟩

/-- `μ₁(G)`: the largest eigenvalue of the Laplacian matrix `D − A` (index `0` of the decreasing
list `Matrix.IsHermitian.eigenvalues₀`). -/
noncomputable def mu₁ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : 2 ≤ n) : ℝ :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨0, by rw [Fintype.card_fin]; omega⟩

/-- `μ₁(G)` is at least every Laplacian eigenvalue of `G`. -/
lemma lapEigenvalue_le_mu₁ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : 2 ≤ n)
    (k : Fin (Fintype.card (Fin n))) : (G.isHermitian_lapMatrix ℝ).eigenvalues₀ k ≤ mu₁ G h :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone (Fin.mk_le_of_le_val (Nat.zero_le _))

/-- Every adjacency eigenvalue of `G` except the top-indexed one is at most `λ₂(G)`. -/
lemma adjEigenvalue_le_lambda₂ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : 2 ≤ n)
    (k : Fin (Fintype.card (Fin n))) (hk : 1 ≤ k.val) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues₀ k ≤ lambda₂ G h :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀_antitone (Fin.mk_le_of_le_val hk)

/-! ### The Laplacian bound `μ₁(G₁₁) ≤ 37/8` -/

/-- `zᵀ L z ≤ (37/8) ‖z‖²` for the Laplacian of `G₁₁`: the difference is a sum of squares. -/
lemma lap_quadForm_le (z : Fin 11 → ℝ) :
    z ⬝ᵥ (G11.lapMatrix ℝ *ᵥ z) ≤ 37 / 8 * (z ⬝ᵥ z) := by
  rw [lap_form, dot_self]
  have key :
      37 / 8 * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2 + z 5 ^ 2 + z 6 ^ 2 + z 7 ^ 2
          + z 8 ^ 2 + z 9 ^ 2 + z 10 ^ 2)
        - ((z 0 - z 2) ^ 2 + (z 0 - z 3) ^ 2 + (z 1 - z 2) ^ 2 + (z 1 - z 3) ^ 2
          + (z 2 - z 3) ^ 2 + (z 4 - z 6) ^ 2 + (z 4 - z 7) ^ 2 + (z 5 - z 6) ^ 2
          + (z 5 - z 7) ^ 2 + (z 6 - z 7) ^ 2 + (z 0 - z 8) ^ 2 + (z 8 - z 9) ^ 2
          + (z 9 - z 10) ^ 2 + (z 10 - z 4) ^ 2)
      = 8 / 21 * (21 / 8 * z 1 + z 2 + z 3) ^ 2 + 13 / 14 * (14 / 13 * z 0 + z 2 + z 3) ^ 2
        + 13 / 7 * (7 / 13 * z 0 + z 8) ^ 2 + 17 / 13 * (13 / 17 * z 8 + z 9) ^ 2
        + 1 / 336 * (z 2 + z 3) ^ 2 + 5 / 16 * (z 2 - z 3) ^ 2
        + 1 / 104 * z 0 ^ 2 + 3 / 952 * z 8 ^ 2
        + 8 / 21 * (21 / 8 * z 5 + z 6 + z 7) ^ 2 + 13 / 14 * (14 / 13 * z 4 + z 6 + z 7) ^ 2
        + 13 / 7 * (7 / 13 * z 4 + z 10) ^ 2 + 17 / 13 * (13 / 17 * z 10 + z 9) ^ 2
        + 1 / 336 * (z 6 + z 7) ^ 2 + 5 / 16 * (z 6 - z 7) ^ 2
        + 1 / 104 * z 4 ^ 2 + 3 / 952 * z 10 ^ 2
        + 1 / 104 * z 9 ^ 2 := by
    ring
  have hnn :
      0 ≤ 8 / 21 * (21 / 8 * z 1 + z 2 + z 3) ^ 2 + 13 / 14 * (14 / 13 * z 0 + z 2 + z 3) ^ 2
        + 13 / 7 * (7 / 13 * z 0 + z 8) ^ 2 + 17 / 13 * (13 / 17 * z 8 + z 9) ^ 2
        + 1 / 336 * (z 2 + z 3) ^ 2 + 5 / 16 * (z 2 - z 3) ^ 2
        + 1 / 104 * z 0 ^ 2 + 3 / 952 * z 8 ^ 2
        + 8 / 21 * (21 / 8 * z 5 + z 6 + z 7) ^ 2 + 13 / 14 * (14 / 13 * z 4 + z 6 + z 7) ^ 2
        + 13 / 7 * (7 / 13 * z 4 + z 10) ^ 2 + 17 / 13 * (13 / 17 * z 10 + z 9) ^ 2
        + 1 / 336 * (z 6 + z 7) ^ 2 + 5 / 16 * (z 6 - z 7) ^ 2
        + 1 / 104 * z 4 ^ 2 + 3 / 952 * z 10 ^ 2
        + 1 / 104 * z 9 ^ 2 := by
    positivity
  linarith

/-- Every Laplacian eigenvalue of `G₁₁` is at most `37/8`; in particular `μ₁(G₁₁) ≤ 37/8`. -/
theorem mu₁_G11_le : mu₁ G11 (by norm_num) ≤ 37 / 8 :=
  eigenvalues₀_le_of_quadForm_le (G11.isHermitian_lapMatrix ℝ) lap_quadForm_le _

/-! ### The adjacency bound `λ₂(G₁₁) ≥ 293/111` -/

/-- Test vector supported on the first diamond and its attachment vertex `8`. -/
def f₁ : Fin 11 → ℝ := ![7, 6, 8, 8, 0, 0, 0, 0, 3, 0, 0]

/-- Test vector supported on the second diamond and its attachment vertex `10`. -/
def f₂ : Fin 11 → ℝ := ![0, 0, 0, 0, 7, 6, 8, 8, 0, 0, 3]

lemma f₁_dot_f₁ : f₁ ⬝ᵥ f₁ = 222 := by
  rw [dot_self]; simp [f₁]; norm_num

lemma f₂_dot_f₂ : f₂ ⬝ᵥ f₂ = 222 := by
  rw [dot_self]; simp [f₂]; norm_num

lemma f₁_dot_f₂ : f₁ ⬝ᵥ f₂ = 0 := by
  simp [dotProduct, sum_univ_eleven, f₁, f₂]

lemma f₁_adj_f₁ : f₁ ⬝ᵥ (G11.adjMatrix ℝ *ᵥ f₁) = 586 := by
  rw [adj_form]; simp [f₁]; norm_num

lemma f₂_adj_f₂ : f₂ ⬝ᵥ (G11.adjMatrix ℝ *ᵥ f₂) = 586 := by
  rw [adj_form]; simp [f₂]; norm_num

lemma f₁_adj_f₂ : f₁ ⬝ᵥ (G11.adjMatrix ℝ *ᵥ f₂) = 0 := by
  rw [adj_form]; simp [f₁, f₂]

lemma f₂_adj_f₁ : f₂ ⬝ᵥ (G11.adjMatrix ℝ *ᵥ f₁) = 0 := by
  rw [adj_form]; simp [f₁, f₂]

/-- `λ₂(G₁₁) ≥ 293/111`. -/
theorem lambda₂_G11_ge : 293 / 111 ≤ lambda₂ G11 (by norm_num) := by
  refine le_eigenvalues₀_one (G11.isHermitian_adjMatrix ℝ) _ f₁ f₂ ?_ ?_
    f₁_adj_f₂ f₂_adj_f₁ f₁_dot_f₂ ?_ ?_
  · rw [f₁_dot_f₁, f₁_adj_f₁]; norm_num
  · rw [f₂_dot_f₂, f₂_adj_f₂]; norm_num
  · rw [f₁_dot_f₁]; norm_num
  · rw [f₂_dot_f₂]; norm_num

/-! ### The counterexample -/

/-- **`G₁₁` violates `λ₂ ≤ μ₁ − 2`.** It is connected, and `μ₁(G₁₁) − 2 < λ₂(G₁₁)`. -/
theorem counterexample :
    G11.Connected ∧ mu₁ G11 (by norm_num) - 2 < lambda₂ G11 (by norm_num) := by
  refine ⟨G11_connected, ?_⟩
  have h1 := mu₁_G11_le
  have h2 := lambda₂_G11_ge
  linarith

/-- A quantitative form: `G₁₁` violates the conjectured inequality by at least `13/888`.
(The true excess is `λ₂ − (μ₁ − 2) ≈ 0.0232`.) -/
theorem counterexample_gap :
    13 / 888 ≤ lambda₂ G11 (by norm_num) - (mu₁ G11 (by norm_num) - 2) := by
  have h1 := mu₁_G11_le
  have h2 := lambda₂_G11_ge
  linarith

/-- **Conjecture 2 is false**: it is not true that `λ₂(G) ≤ μ₁(G) − 2` for every connected
simple graph `G` on `n ≥ 2` vertices. -/
theorem conjecture_two_false :
    ¬ ∀ (n : ℕ) (h : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → lambda₂ G h ≤ mu₁ G h - 2 := by
  intro hconj
  have h := hconj 11 (by norm_num) G11 counterexample.1
  have h' := counterexample.2
  linarith

end Conj2
