import Mathlib

/-!
# Two Rayleigh-quotient bounds for real symmetric matrices

Let `A` be a real symmetric (Hermitian) matrix indexed by `Fin n`, and let
`hA.eigenvalues₀ : Fin (Fintype.card (Fin n)) → ℝ` be Mathlib's list of its eigenvalues, with
multiplicity, in decreasing order (`Matrix.IsHermitian.eigenvalues₀_antitone`).

* `Conj2.eigenvalues₀_le_of_quadForm_le`: if `z ⬝ᵥ A *ᵥ z ≤ c * (z ⬝ᵥ z)` for every `z`, then
  every eigenvalue of `A` is at most `c`.
* `Conj2.le_eigenvalues₀_one`: if `f₁, f₂` are orthogonal non-zero vectors, uncoupled by `A`,
  whose Rayleigh quotients are both at least `c`, then the second largest eigenvalue of `A` is at
  least `c` (the two-dimensional case of the Courant–Fischer min-max principle).

Both are derived from Mathlib's spectral theorem `A = U D Uᵀ` by passing to the coordinates
`Uᵀ z` of a vector `z` in an orthonormal eigenbasis.
-/

open Matrix

namespace Conj2

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)

/-- The orthogonal matrix whose columns form an orthonormal eigenbasis of `A`. -/
noncomputable abbrev eigU : Matrix (Fin n) (Fin n) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)

lemma eigU_mul_transpose : eigU hA * (eigU hA)ᵀ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

lemma transpose_mul_eigU : (eigU hA)ᵀ * eigU hA = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- The spectral theorem over `ℝ`: `A = U D Uᵀ`. -/
lemma spectral : A = eigU hA * diagonal hA.eigenvalues * (eigU hA)ᵀ := by
  have h := hA.spectral_theorem
  simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, Function.comp_def]
    using h

/-- Coordinates of `z` in the orthonormal eigenbasis of `A`. -/
noncomputable def coords (z : Fin n → ℝ) : Fin n → ℝ := (eigU hA)ᵀ *ᵥ z

/-- Parseval: the squared norm is the sum of the squared coordinates. -/
lemma dot_self_eq (z : Fin n → ℝ) : z ⬝ᵥ z = ∑ i, coords hA z i ^ 2 := by
  have h : coords hA z ⬝ᵥ coords hA z = z ⬝ᵥ z := by
    unfold coords
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, eigU_mul_transpose, one_mulVec]
  rw [← h]
  simp [dotProduct, sq]

/-- The quadratic form of `A` is diagonal in the coordinates `coords hA z`. -/
lemma quadForm_eq (z : Fin n → ℝ) :
    z ⬝ᵥ (A *ᵥ z) = ∑ i, hA.eigenvalues i * coords hA z i ^ 2 := by
  have h : z ⬝ᵥ (A *ᵥ z) = coords hA z ⬝ᵥ (diagonal hA.eigenvalues *ᵥ coords hA z) := by
    conv_lhs => rw [spectral hA]
    unfold coords
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  rw [h]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The reindexing between Mathlib's two ways of listing the eigenvalues. -/
noncomputable abbrev idx (n : ℕ) : Fin (Fintype.card (Fin n)) ≃ Fin n :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

lemma eigenvalues_idx (k : Fin (Fintype.card (Fin n))) :
    hA.eigenvalues (idx n k) = hA.eigenvalues₀ k := by
  change hA.eigenvalues₀ ((idx n).symm (idx n k)) = _
  rw [Equiv.symm_apply_apply]

/-- If the quadratic form of `A` is bounded by `c` times the squared norm, every eigenvalue of
`A` is at most `c`. -/
theorem eigenvalues₀_le_of_quadForm_le {c : ℝ}
    (h : ∀ z : Fin n → ℝ, z ⬝ᵥ (A *ᵥ z) ≤ c * (z ⬝ᵥ z)) (k : Fin (Fintype.card (Fin n))) :
    hA.eigenvalues₀ k ≤ c := by
  have hw : coords hA (eigU hA *ᵥ Pi.single (idx n k) 1) = Pi.single (idx n k) 1 := by
    unfold coords
    rw [mulVec_mulVec, transpose_mul_eigU, one_mulVec]
  have h1 := h (eigU hA *ᵥ Pi.single (idx n k) 1)
  rw [quadForm_eq hA, dot_self_eq hA, hw] at h1
  simp only [Pi.single_apply, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  rw [eigenvalues_idx] at h1
  exact h1

/-- Every eigenvalue other than the top-indexed one is at most the second largest. -/
lemma eigenvalues_le_second (hn : 1 < Fintype.card (Fin n)) (i : Fin n)
    (hi : i ≠ idx n ⟨0, by omega⟩) : hA.eigenvalues i ≤ hA.eigenvalues₀ ⟨1, hn⟩ := by
  change hA.eigenvalues₀ ((idx n).symm i) ≤ _
  apply hA.eigenvalues₀_antitone
  rw [Fin.le_def]
  show 1 ≤ ((idx n).symm i).val
  by_contra hlt
  apply hi
  have h0 : (idx n).symm i = ⟨0, by omega⟩ :=
    Fin.ext (show ((idx n).symm i).val = 0 by omega)
  rw [← h0, Equiv.apply_symm_apply]

/-- A vector with no component along the top eigenvector has Rayleigh quotient at most the
second largest eigenvalue. -/
lemma quadForm_le_second (hn : 1 < Fintype.card (Fin n)) (z : Fin n → ℝ)
    (hz : coords hA z (idx n ⟨0, by omega⟩) = 0) :
    z ⬝ᵥ (A *ᵥ z) ≤ hA.eigenvalues₀ ⟨1, hn⟩ * (z ⬝ᵥ z) := by
  rw [quadForm_eq hA, dot_self_eq hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i = idx n ⟨0, by omega⟩
  · rw [hi, hz]; simp
  · exact mul_le_mul_of_nonneg_right (eigenvalues_le_second hA hn i hi) (sq_nonneg _)

/-- **Two-dimensional Courant–Fischer bound.** If `f₁` and `f₂` are orthogonal, non-zero,
not coupled by `A`, and both have Rayleigh quotient at least `c`, then the second largest
eigenvalue of `A` is at least `c`. -/
theorem le_eigenvalues₀_one (hn : 1 < Fintype.card (Fin n)) {c : ℝ} (f₁ f₂ : Fin n → ℝ)
    (h₁ : c * (f₁ ⬝ᵥ f₁) ≤ f₁ ⬝ᵥ (A *ᵥ f₁)) (h₂ : c * (f₂ ⬝ᵥ f₂) ≤ f₂ ⬝ᵥ (A *ᵥ f₂))
    (h₁₂ : f₁ ⬝ᵥ (A *ᵥ f₂) = 0) (h₂₁ : f₂ ⬝ᵥ (A *ᵥ f₁) = 0) (o : f₁ ⬝ᵥ f₂ = 0)
    (p₁ : 0 < f₁ ⬝ᵥ f₁) (p₂ : 0 < f₂ ⬝ᵥ f₂) :
    c ≤ hA.eigenvalues₀ ⟨1, hn⟩ := by
  set i₀ : Fin n := idx n ⟨0, by omega⟩ with hi₀
  set α : ℝ := coords hA f₁ i₀ with hα
  set β : ℝ := coords hA f₂ i₀ with hβ
  by_cases hαβ : α = 0 ∧ β = 0
  · -- `f₁` itself is orthogonal to the top eigenvector
    have h3 := quadForm_le_second hA hn f₁ hαβ.1
    exact le_of_mul_le_mul_right (h₁.trans h3) p₁
  · -- `z = β f₁ - α f₂` is orthogonal to the top eigenvector and non-zero
    have hz0 : coords hA (β • f₁ - α • f₂) i₀ = 0 := by
      have : coords hA (β • f₁ - α • f₂) = β • coords hA f₁ - α • coords hA f₂ := by
        unfold coords
        rw [mulVec_sub, mulVec_smul, mulVec_smul]
      rw [this]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hα, ← hβ]
      ring
    have o' : f₂ ⬝ᵥ f₁ = 0 := by rw [dotProduct_comm]; exact o
    have hzz : (β • f₁ - α • f₂) ⬝ᵥ (β • f₁ - α • f₂)
        = β ^ 2 * (f₁ ⬝ᵥ f₁) + α ^ 2 * (f₂ ⬝ᵥ f₂) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        o, o']
      ring
    have hzAz : (β • f₁ - α • f₂) ⬝ᵥ (A *ᵥ (β • f₁ - α • f₂))
        = β ^ 2 * (f₁ ⬝ᵥ (A *ᵥ f₁)) + α ^ 2 * (f₂ ⬝ᵥ (A *ᵥ f₂)) := by
      simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, h₁₂, h₂₁]
      ring
    have hpos : 0 < β ^ 2 * (f₁ ⬝ᵥ f₁) + α ^ 2 * (f₂ ⬝ᵥ f₂) := by
      rcases not_and_or.mp hαβ with h | h
      · have : 0 < α ^ 2 := by positivity
        have : 0 ≤ β ^ 2 := sq_nonneg β
        nlinarith
      · have : 0 < β ^ 2 := by positivity
        have : 0 ≤ α ^ 2 := sq_nonneg α
        nlinarith
    have h3 := quadForm_le_second hA hn (β • f₁ - α • f₂) hz0
    rw [hzAz, hzz] at h3
    have h4 : c * (β ^ 2 * (f₁ ⬝ᵥ f₁) + α ^ 2 * (f₂ ⬝ᵥ f₂))
        ≤ β ^ 2 * (f₁ ⬝ᵥ (A *ᵥ f₁)) + α ^ 2 * (f₂ ⬝ᵥ (A *ᵥ f₂)) := by
      have := mul_le_mul_of_nonneg_left h₁ (sq_nonneg β)
      have := mul_le_mul_of_nonneg_left h₂ (sq_nonneg α)
      nlinarith
    exact le_of_mul_le_mul_right (h4.trans h3) hpos

end Conj2
