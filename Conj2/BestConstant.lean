import Conj2.Sharp

/-!
# The best constant in `λ₂ ≤ μ₁ − c` is `c = 1`

For connected simple graphs on `n ≥ 2` vertices:

* `lambda₂_le_mu₁_sub_one`: `λ₂ ≤ μ₁ − 1`. This direction is known: every adjacency eigenvalue
  is at most the maximum degree `Δ` (`adj_quadForm_le`), and `μ₁ ≥ Δ + 1`
  (`maxDegree_add_one_le_mu₁`; Grone and Merris, SIAM J. Discrete Math. 7 (1994) 221–229), proved
  here from the star test vector at a vertex of maximum degree. It also follows from
  `μ₂ ≥ λ₂ + 1`, Theorem 1 of arXiv:2611.03879.
* `Conj2.Sharp.no_constant_above_one`: no constant `c > 1` works.

Together (`best_constant`): the inequality `λ₂ ≤ μ₁ − c` holds for all connected graphs
**if and only if** `c ≤ 1`.
-/

open Matrix SimpleGraph Finset

namespace Conj2

section top

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)

/-- The quadratic form is at most the largest eigenvalue times the squared norm. -/
lemma quadForm_le_top (hn : 0 < Fintype.card (Fin n)) (z : Fin n → ℝ) :
    z ⬝ᵥ (A *ᵥ z) ≤ hA.eigenvalues₀ ⟨0, hn⟩ * (z ⬝ᵥ z) := by
  rw [quadForm_eq hA, dot_self_eq hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  change hA.eigenvalues₀ ((idx n).symm i) ≤ _
  exact hA.eigenvalues₀_antitone (Fin.mk_le_of_le_val (Nat.zero_le _))

end top

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-! ### Adjacency eigenvalues are at most the maximum degree -/

/-- `zᵀ A z ≤ Δ ‖z‖²`. -/
lemma adj_quadForm_le (z : Fin n → ℝ) :
    z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) ≤ (G.maxDegree : ℝ) * (z ⬝ᵥ z) := by
  rw [dotProduct_mulVec_adjMatrix]
  have h1 : ∀ i j, (if G.Adj i j then z i * z j else 0)
      ≤ (if G.Adj i j then z i ^ 2 else 0) / 2 + (if G.Adj i j then z j ^ 2 else 0) / 2 := by
    intro i j
    split_ifs
    · nlinarith [sq_nonneg (z i - z j)]
    · norm_num
  have hrow : ∀ i, ∑ j, (if G.Adj i j then z i ^ 2 else 0) = (G.degree i : ℝ) * z i ^ 2 := by
    intro i
    rw [degree_eq_sum_if_adj, sum_mul]
    exact sum_congr rfl fun j _ => by split_ifs <;> simp
  have hcol : ∑ i, ∑ j, (if G.Adj i j then z j ^ 2 else 0)
      = ∑ j, (G.degree j : ℝ) * z j ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [degree_eq_sum_if_adj, sum_mul]
    exact sum_congr rfl fun i _ => by
      by_cases h : G.Adj i j
      · simp [h, h.symm]
      · have h' : ¬G.Adj j i := fun h'' => h h''.symm
        simp [h, h']
  calc ∑ i, ∑ j, (if G.Adj i j then z i * z j else 0)
      ≤ ∑ i, ∑ j, ((if G.Adj i j then z i ^ 2 else 0) / 2
          + (if G.Adj i j then z j ^ 2 else 0) / 2) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => h1 i j
    _ = ∑ i, (G.degree i : ℝ) * z i ^ 2 := by
        simp only [sum_add_distrib, ← sum_div, hrow, hcol]
        ring
    _ ≤ ∑ i, (G.maxDegree : ℝ) * z i ^ 2 :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
          (by exact_mod_cast G.degree_le_maxDegree i) (sq_nonneg _)
    _ = (G.maxDegree : ℝ) * (z ⬝ᵥ z) := by
        simp only [dotProduct, mul_sum, sq]

/-! ### The largest Laplacian eigenvalue is at least `Δ + 1` -/

/-- The star test vector at `v`: `deg v` at `v`, `−1` at its neighbours, `0` elsewhere. -/
def starVec (v : Fin n) : Fin n → ℝ := fun u =>
  if u = v then (G.degree v : ℝ) else if G.Adj v u then -1 else 0

lemma starVec_self (v : Fin n) : starVec G v v = G.degree v := by
  simp [starVec]

lemma starVec_adj {v u : Fin n} (h : G.Adj v u) : starVec G v u = -1 := by
  have hne : u ≠ v := (G.ne_of_adj h).symm
  simp [starVec, hne, h]

lemma starVec_sq (v u : Fin n) :
    starVec G v u ^ 2
      = (if u = v then (G.degree v : ℝ) ^ 2 else 0) + (if G.Adj v u then 1 else 0) := by
  by_cases huv : u = v
  · subst huv
    simp [starVec]
  · by_cases h : G.Adj v u
    · simp [starVec, huv, h]
    · simp [starVec, huv, h]

lemma starVec_dot (v : Fin n) :
    starVec G v ⬝ᵥ starVec G v = (G.degree v : ℝ) ^ 2 + G.degree v := by
  simp only [dotProduct, ← sq, starVec_sq, sum_add_distrib, sum_ite_eq', mem_univ, ite_true,
    ← degree_eq_sum_if_adj]

/-- One term of the Laplacian double sum of the star vector. -/
def starTerm (v u w : Fin n) : ℝ :=
  if G.Adj u w then (starVec G v u - starVec G v w) ^ 2 else 0

lemma starTerm_nonneg (v u w : Fin n) : 0 ≤ starTerm G v u w := by
  unfold starTerm
  split_ifs <;> positivity

lemma starTerm_self (v : Fin n) : starTerm G v v v = 0 := by
  simp [starTerm]

lemma sum_starTerm_row (v : Fin n) :
    ∑ w, starTerm G v v w = (G.degree v : ℝ) * ((G.degree v : ℝ) + 1) ^ 2 := by
  have h : ∀ w, starTerm G v v w
      = ((G.degree v : ℝ) + 1) ^ 2 * (if G.Adj v w then (1 : ℝ) else 0) := by
    intro w
    unfold starTerm
    by_cases hvw : G.Adj v w
    · rw [ite_eq_left hvw, ite_eq_left hvw, starVec_self, starVec_adj G hvw]
      ring
    · rw [ite_eq_right hvw, ite_eq_right hvw]
      ring
  simp only [h, ← mul_sum, ← degree_eq_sum_if_adj]
  ring

lemma sum_starTerm_col (v : Fin n) :
    ∑ u, starTerm G v u v = (G.degree v : ℝ) * ((G.degree v : ℝ) + 1) ^ 2 := by
  have h : ∀ u, starTerm G v u v
      = ((G.degree v : ℝ) + 1) ^ 2 * (if G.Adj v u then (1 : ℝ) else 0) := by
    intro u
    unfold starTerm
    by_cases hvu : G.Adj v u
    · rw [ite_eq_left hvu.symm, ite_eq_left hvu, starVec_self, starVec_adj G hvu]
      ring
    · have hvu' : ¬G.Adj u v := fun h' => hvu h'.symm
      rw [ite_eq_right hvu', ite_eq_right hvu]
      ring
  simp only [h, ← mul_sum, ← degree_eq_sum_if_adj]
  ring

/-- The Rayleigh quotient of the star vector at `v` for the Laplacian is at least `deg v + 1`. -/
lemma lap_star_ge (v : Fin n) :
    ((G.degree v : ℝ) + 1) * (starVec G v ⬝ᵥ starVec G v)
      ≤ starVec G v ⬝ᵥ (G.lapMatrix ℝ *ᵥ starVec G v) := by
  rw [← Matrix.toLinearMap₂'_apply', lapMatrix_toLinearMap₂', starVec_dot]
  change _ ≤ (∑ u, ∑ w, starTerm G v u w) / 2
  -- each row dominates its entry in the column of `v`; the row of `v` is counted in full
  have hlow : ∀ u, (if u = v then ∑ w, starTerm G v v w else 0) + starTerm G v u v
      ≤ ∑ w, starTerm G v u w := by
    intro u
    by_cases hu : u = v
    · subst hu
      simp [starTerm_self]
    · rw [ite_eq_right hu, zero_add]
      exact single_le_sum (fun w _ => starTerm_nonneg G v u w) (mem_univ v)
  have hsum : ∑ u, ((if u = v then ∑ w, starTerm G v v w else 0) + starTerm G v u v)
      = 2 * ((G.degree v : ℝ) * ((G.degree v : ℝ) + 1) ^ 2) := by
    rw [sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ v), sum_starTerm_row,
      sum_starTerm_col]
    ring
  have htot : 2 * ((G.degree v : ℝ) * ((G.degree v : ℝ) + 1) ^ 2)
      ≤ ∑ u, ∑ w, starTerm G v u w := by
    rw [← hsum]
    exact sum_le_sum fun u _ => hlow u
  nlinarith [htot]

/-- `μ₁ ≥ Δ + 1` for a connected graph on at least two vertices. -/
theorem maxDegree_add_one_le_mu₁ (hn : 2 ≤ n) (hc : G.Connected) :
    (G.maxDegree : ℝ) + 1 ≤ mu₁ G hn := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hdpos : 0 < G.degree v := hc.preconnected.degree_pos_of_nontrivial v
  have hd : (0 : ℝ) < G.degree v := by exact_mod_cast hdpos
  have h1 := lap_star_ge G v
  have h2 := quadForm_le_top (G.isHermitian_lapMatrix ℝ)
    (by rw [Fintype.card_fin]; omega) (starVec G v)
  have hnorm : 0 < starVec G v ⬝ᵥ starVec G v := by
    rw [starVec_dot]
    positivity
  rw [hv]
  exact le_of_mul_le_mul_right (h1.trans h2) hnorm

/-! ### The classical bound and the best constant -/

/-- **`λ₂ ≤ μ₁ − 1`** for every connected simple graph on at least two vertices. -/
theorem lambda₂_le_mu₁_sub_one (hn : 2 ≤ n) (hc : G.Connected) :
    lambda₂ G hn ≤ mu₁ G hn - 1 := by
  have h1 : lambda₂ G hn ≤ (G.maxDegree : ℝ) :=
    eigenvalues₀_le_of_quadForm_le (G.isHermitian_adjMatrix ℝ) (adj_quadForm_le G) _
  have h2 := maxDegree_add_one_le_mu₁ G hn hc
  linarith

/-- **The best constant is `1`.** The inequality `λ₂(G) ≤ μ₁(G) − c` holds for every connected
simple graph `G` on `n ≥ 2` vertices if and only if `c ≤ 1`. -/
theorem best_constant (c : ℝ) :
    (∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → lambda₂ G hn ≤ mu₁ G hn - c) ↔ c ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    exact Sharp.no_constant_above_one c (not_le.mp hc) h
  · intro hc n hn G _ hconn
    have h := lambda₂_le_mu₁_sub_one G hn hconn
    linarith

end Conj2
