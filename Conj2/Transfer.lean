import Conj2.Main

/-!
# Relabelling a graph along a bijection

The statements about `λ₂` and `μ₁` in this project are about graphs on `Fin n`. For the sharp
family it is far more convenient to describe the graph on a structured vertex set `V`
(an `Option` of a product of sums) and to compute sums there.

Given a graph `H` on a finite type `V` and a bijection `e : Fin n ≃ V`, the graph `H.comap e` on
`Fin n` is `H` with its vertices renamed. This file shows that the two Rayleigh-type
certificates used throughout — a bound on the Laplacian quadratic form, and a pair of test
vectors for the adjacency form — can be checked on `V`:

* `mu₁_comap_le`: if `zᵀ L_H z ≤ c ‖z‖²` for all `z : V → ℝ`, then `μ₁(H.comap e) ≤ c`;
* `le_lambda₂_comap`: test vectors on `V` give `c ≤ λ₂(H.comap e)`;
* `connected_comap`: connectivity is preserved.
-/

open Matrix SimpleGraph Finset

namespace Conj2

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj] (e : Fin n ≃ V)

omit [Fintype V] [DecidableEq V] in
lemma comp_comp_symm (f : V → ℝ) : (f ∘ e) ∘ e.symm = f := by
  ext x
  simp

omit [DecidableEq V] in
/-- The dot product does not change under renaming. -/
lemma dotProduct_comap (x y : Fin n → ℝ) :
    x ⬝ᵥ y = (x ∘ e.symm) ⬝ᵥ (y ∘ e.symm) := by
  simp only [dotProduct]
  exact Fintype.sum_equiv e _ _ fun u => by simp

/-- The Laplacian quadratic form of the renamed graph. -/
lemma lap_form_comap (z : Fin n → ℝ) :
    z ⬝ᵥ ((H.comap e).lapMatrix ℝ *ᵥ z)
      = (z ∘ e.symm) ⬝ᵥ (H.lapMatrix ℝ *ᵥ (z ∘ e.symm)) := by
  rw [← Matrix.toLinearMap₂'_apply', lapMatrix_toLinearMap₂',
    ← Matrix.toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
  congr 1
  refine Fintype.sum_equiv e _ _ fun u => Fintype.sum_equiv e _ _ fun v => ?_
  simp

omit [DecidableEq V] in
/-- The adjacency bilinear form of the renamed graph. -/
lemma adj_form_comap (x y : Fin n → ℝ) :
    x ⬝ᵥ ((H.comap e).adjMatrix ℝ *ᵥ y)
      = (x ∘ e.symm) ⬝ᵥ (H.adjMatrix ℝ *ᵥ (y ∘ e.symm)) := by
  rw [dotProduct_mulVec_adjMatrix, dotProduct_mulVec_adjMatrix]
  refine Fintype.sum_equiv e _ _ fun u => Fintype.sum_equiv e _ _ fun v => ?_
  simp

/-- A bound on the Laplacian form of `H` bounds `μ₁` of the renamed graph. -/
theorem mu₁_comap_le (hn : 2 ≤ n) {c : ℝ}
    (h : ∀ z : V → ℝ, z ⬝ᵥ (H.lapMatrix ℝ *ᵥ z) ≤ c * (z ⬝ᵥ z)) :
    mu₁ (H.comap e) hn ≤ c := by
  refine eigenvalues₀_le_of_quadForm_le ((H.comap e).isHermitian_lapMatrix ℝ) (fun z => ?_) _
  rw [lap_form_comap, dotProduct_comap e z z]
  exact h _

omit [DecidableEq V] in
/-- Two test vectors on `V` (orthogonal, non-zero, not coupled by the adjacency matrix of `H`,
both with Rayleigh quotient at least `c`) bound `λ₂` of the renamed graph from below. -/
theorem le_lambda₂_comap (hn : 2 ≤ n) {c : ℝ} (f₁ f₂ : V → ℝ)
    (h₁ : c * (f₁ ⬝ᵥ f₁) ≤ f₁ ⬝ᵥ (H.adjMatrix ℝ *ᵥ f₁))
    (h₂ : c * (f₂ ⬝ᵥ f₂) ≤ f₂ ⬝ᵥ (H.adjMatrix ℝ *ᵥ f₂))
    (h₁₂ : f₁ ⬝ᵥ (H.adjMatrix ℝ *ᵥ f₂) = 0) (h₂₁ : f₂ ⬝ᵥ (H.adjMatrix ℝ *ᵥ f₁) = 0)
    (o : f₁ ⬝ᵥ f₂ = 0) (p₁ : 0 < f₁ ⬝ᵥ f₁) (p₂ : 0 < f₂ ⬝ᵥ f₂) :
    c ≤ lambda₂ (H.comap e) hn := by
  have d11 : (f₁ ∘ e) ⬝ᵥ (f₁ ∘ e) = f₁ ⬝ᵥ f₁ := by
    rw [dotProduct_comap e, comp_comp_symm]
  have d22 : (f₂ ∘ e) ⬝ᵥ (f₂ ∘ e) = f₂ ⬝ᵥ f₂ := by
    rw [dotProduct_comap e, comp_comp_symm]
  have d12 : (f₁ ∘ e) ⬝ᵥ (f₂ ∘ e) = f₁ ⬝ᵥ f₂ := by
    rw [dotProduct_comap e, comp_comp_symm, comp_comp_symm]
  have a11 : (f₁ ∘ e) ⬝ᵥ ((H.comap e).adjMatrix ℝ *ᵥ (f₁ ∘ e))
      = f₁ ⬝ᵥ (H.adjMatrix ℝ *ᵥ f₁) := by
    rw [adj_form_comap, comp_comp_symm]
  have a22 : (f₂ ∘ e) ⬝ᵥ ((H.comap e).adjMatrix ℝ *ᵥ (f₂ ∘ e))
      = f₂ ⬝ᵥ (H.adjMatrix ℝ *ᵥ f₂) := by
    rw [adj_form_comap, comp_comp_symm]
  have a12 : (f₁ ∘ e) ⬝ᵥ ((H.comap e).adjMatrix ℝ *ᵥ (f₂ ∘ e))
      = f₁ ⬝ᵥ (H.adjMatrix ℝ *ᵥ f₂) := by
    rw [adj_form_comap, comp_comp_symm, comp_comp_symm]
  have a21 : (f₂ ∘ e) ⬝ᵥ ((H.comap e).adjMatrix ℝ *ᵥ (f₁ ∘ e))
      = f₂ ⬝ᵥ (H.adjMatrix ℝ *ᵥ f₁) := by
    rw [adj_form_comap, comp_comp_symm, comp_comp_symm]
  refine le_eigenvalues₀_one ((H.comap e).isHermitian_adjMatrix ℝ) _ (f₁ ∘ e) (f₂ ∘ e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [d11, a11]; exact h₁
  · rw [d22, a22]; exact h₂
  · rw [a12]; exact h₁₂
  · rw [a21]; exact h₂₁
  · rw [d12]; exact o
  · rw [d11]; exact p₁
  · rw [d22]; exact p₂

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
/-- Renaming the vertices preserves connectivity. -/
theorem connected_comap (hc : H.Connected) : (H.comap e).Connected :=
  (Iso.comap e H).connected_iff.mpr hc

end Conj2
