import Mathlib

/-!
# Algebra behind the sharp family

Auxiliary lemmas for `Conj2.Sharp`: sums of squared differences over a clique and between a
clique and an independent set, and the inequality `cluster_core` that bounds the Laplacian form
of a complete split graph. Everything here is about real numbers and finite sums; no graphs
appear.
-/

open Finset

namespace Conj2

/-- A double sum restricted to distinct indices: the full double sum minus the diagonal. -/
lemma sum_sum_ne {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ι → ℝ) :
    ∑ i, ∑ j, (if i ≠ j then K i j else 0) = ∑ i, ∑ j, K i j - ∑ i, K i i := by
  have h : ∀ i, ∑ j, (if i ≠ j then K i j else 0) = ∑ j, K i j - K i i := by
    intro i
    have hterm : ∀ j, (if i ≠ j then K i j else 0) = K i j - (if i = j then K i j else 0) := by
      intro j
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    simp only [hterm, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true]
  simp only [h, sum_sub_distrib]

/-- Squared differences over all ordered pairs of one index set. -/
lemma sum_sum_sq_sub {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∑ i, ∑ j, (f i - f j) ^ 2
      = 2 * (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 - 2 * (∑ i, f i) ^ 2 := by
  have h : ∀ i, ∑ j, (f i - f j) ^ 2
      = (Fintype.card ι : ℝ) * f i ^ 2 - 2 * f i * ∑ j, f j + ∑ j, f j ^ 2 := by
    intro i
    have hterm : ∀ j, (f i - f j) ^ 2 = f i ^ 2 - 2 * f i * f j + f j ^ 2 := fun j => by ring
    simp only [hterm, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
      ← mul_sum]
  simp only [h, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum, ← sum_mul]
  ring

/-- Squared differences over all pairs taken from two index sets. -/
lemma sum_sum_sq_sub_two {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ℝ) (g : κ → ℝ) :
    ∑ i, ∑ j, (f i - g j) ^ 2
      = (Fintype.card κ : ℝ) * ∑ i, f i ^ 2 - 2 * (∑ i, f i) * (∑ j, g j)
        + (Fintype.card ι : ℝ) * ∑ j, g j ^ 2 := by
  have h : ∀ i, ∑ j, (f i - g j) ^ 2
      = (Fintype.card κ : ℝ) * f i ^ 2 - 2 * f i * ∑ j, g j + ∑ j, g j ^ 2 := by
    intro i
    have hterm : ∀ j, (f i - g j) ^ 2 = f i ^ 2 - 2 * f i * g j + g j ^ 2 := fun j => by ring
    simp only [hterm, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
      ← mul_sum]
  simp only [h, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← mul_sum, ← sum_mul]

/-- **The cluster inequality, in abstract form.** Think of a clique of size `m` whose values
have sum `σ` and sum of squares `PC`, and `s` further vertices joined to the whole clique:
one of them has value `α`, the others have sum `ω` and sum of squares `PW`
(so `ω² ≤ (s − 1) PW` by Cauchy–Schwarz). With `η = 3 / s`, the Laplacian form of this complete
split graph, plus `2 α²`, is at most `(m + s + η)` times the squared norm. -/
lemma cluster_core (m s η PC σ α ω PW : ℝ) (hs : 2 ≤ s) (hη : η * s = 3)
    (hPC : 0 ≤ PC) (hPW : 0 ≤ PW) (hCS : ω ^ 2 ≤ (s - 1) * PW) :
    (m * PC - σ ^ 2) + (s * PC - 2 * σ * (α + ω) + m * (α ^ 2 + PW)) + 2 * α ^ 2
      ≤ (m + s + η) * (PC + α ^ 2 + PW) := by
  have hηpos : 0 < η := by nlinarith
  have hAs : (s + η - 3) * s = s ^ 2 - 3 * s + 3 := by linear_combination hη
  have hApos : 0 < s + η - 3 := by nlinarith [sq_nonneg (s - 3 / 2)]
  have key : (s + η - 3) * ((s + η - 3) * α ^ 2 - 2 * α * ω + (s + η) * PW - ω ^ 2)
      = ((s + η - 3) * α - ω) ^ 2 + (s + η - 3 + 1) * ((s - 1) * PW - ω ^ 2)
        + (η - 1) ^ 2 * PW := by
    linear_combination PW * hη
  have hbr : 0 ≤ (s + η - 3) * α ^ 2 - 2 * α * ω + (s + η) * PW - ω ^ 2 := by
    have h1 : 0 ≤ ((s + η - 3) * α - ω) ^ 2 + (s + η - 3 + 1) * ((s - 1) * PW - ω ^ 2)
        + (η - 1) ^ 2 * PW := by
      have h2 : 0 ≤ (s + η - 3 + 1) * ((s - 1) * PW - ω ^ 2) :=
        mul_nonneg (by linarith) (by linarith)
      have h3 : 0 ≤ (η - 1) ^ 2 * PW := mul_nonneg (sq_nonneg _) hPW
      have h4 : 0 ≤ ((s + η - 3) * α - ω) ^ 2 := sq_nonneg _
      linarith
    rw [← key] at h1
    exact nonneg_of_mul_nonneg_right h1 hApos
  nlinarith [sq_nonneg (σ + α + ω), mul_nonneg hηpos.le hPC]

end Conj2
