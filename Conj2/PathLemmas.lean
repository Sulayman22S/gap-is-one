import Mathlib

/-!
# Sums along a path

Auxiliary lemmas for the infinite family of counterexamples (`Conj2.Family`).

* `sum_range_consecutive`: a double sum restricted to consecutive indices is a single sum over
  the edges of a path.
* `path_left`, `path_both`: the edge terms `(y e - y (e+1))²` of a path are bounded by a
  weighted sum of squares in which the end vertices carry the weight `30/17` and every inner
  vertex at most `37/8`.
* `diamond_attach_le`: the five edges of a diamond plus one pendant edge.

Everything here is about real numbers and sums over `Finset.range`; no graphs appear.
-/

open Finset

namespace Conj2

/-- A double sum over `Fin k × Fin k` of a function of the two values is a double sum over
`range k × range k`. -/
lemma sum_fin_fin (k : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ i : Fin k, ∑ j : Fin k, g i.val j.val = ∑ i ∈ range k, ∑ j ∈ range k, g i j := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range k, g i j) k]
  exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (fun j => g i.val j) k

/-- Sum over the ordered pairs of consecutive indices below `k + 1`: each of the `k` edges
`e – (e+1)` of the path appears once in each direction. -/
lemma sum_range_consecutive (k : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), (if i + 1 = j ∨ j + 1 = i then G i j else 0)
      = ∑ e ∈ range k, (G e (e + 1) + G (e + 1) e) := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- the last column, restricted to the first `k + 1` rows, contributes `G k (k + 1)`
    have hrow : ∀ i ∈ range (k + 1),
        ∑ j ∈ range (k + 1 + 1), (if i + 1 = j ∨ j + 1 = i then G i j else 0)
          = ∑ j ∈ range (k + 1), (if i + 1 = j ∨ j + 1 = i then G i j else 0)
            + (if i = k then G k (k + 1) else 0) := by
      intro i hi
      have hik : i < k + 1 := mem_range.mp hi
      rw [sum_range_succ]
      congr 1
      by_cases h : i = k
      · rw [h, ite_eq_left (Or.inl rfl), ite_eq_left rfl]
      · have hne : ¬(i + 1 = k + 1 ∨ k + 1 + 1 = i) := by omega
        rw [ite_eq_right hne, ite_eq_right h]
    -- the last row contributes `G (k + 1) k`
    have hlast : ∑ j ∈ range (k + 1 + 1),
        (if k + 1 + 1 = j ∨ j + 1 = k + 1 then G (k + 1) j else 0) = G (k + 1) k := by
      rw [sum_range_succ, sum_range_succ]
      have h0 : ∑ j ∈ range k,
          (if k + 1 + 1 = j ∨ j + 1 = k + 1 then G (k + 1) j else 0) = 0 :=
        sum_eq_zero fun j hj => by
          have hjk : j < k := mem_range.mp hj
          have hne : ¬(k + 1 + 1 = j ∨ j + 1 = k + 1) := by omega
          rw [ite_eq_right hne]
      have h1 : k + 1 + 1 = k ∨ k + 1 = k + 1 := Or.inr rfl
      have h2 : ¬(k + 1 + 1 = k + 1 ∨ k + 1 + 1 = k + 1) := by omega
      rw [h0, ite_eq_left h1, ite_eq_right h2]
      ring
    have hcol : ∑ i ∈ range (k + 1), (if i = k then G k (k + 1) else 0) = G k (k + 1) := by
      rw [sum_ite_eq' (range (k + 1)) k (fun _ => G k (k + 1)),
        ite_eq_left (mem_range.mpr (Nat.lt_succ_self k))]
    rw [sum_range_succ, sum_congr rfl hrow, sum_add_distrib, ih, hlast, hcol, sum_range_succ]
    ring

/-- A path edge charged `30/17` at one end and `30/13` at the other. -/
lemma sq_sub_le_outer (a b : ℝ) : (a - b) ^ 2 ≤ 30 / 17 * a ^ 2 + 30 / 13 * b ^ 2 := by
  nlinarith [sq_nonneg (13 / 17 * a + b)]

/-- A path edge charged `2` at both ends. -/
lemma sq_sub_le_two (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- The edges of a path `y 0 – y 1 – ⋯ – y (N+1)`: the first vertex is charged `30/17`, every
inner vertex at most `37/8`, and the last vertex `30/13`. -/
lemma path_left (y : ℕ → ℝ) (N : ℕ) :
    ∑ e ∈ range (N + 1), (y e - y (e + 1)) ^ 2
      ≤ 30 / 17 * y 0 ^ 2 + 37 / 8 * ∑ i ∈ range N, y (i + 1) ^ 2
        + 30 / 13 * y (N + 1) ^ 2 := by
  induction N with
  | zero =>
    have h := sq_sub_le_outer (y 0) (y 1)
    simpa using h
  | succ N ih =>
    rw [sum_range_succ (fun e => (y e - y (e + 1)) ^ 2) (N + 1),
      sum_range_succ (fun i => y (i + 1) ^ 2) N]
    have h := sq_sub_le_two (y (N + 1)) (y (N + 1 + 1))
    nlinarith [sq_nonneg (y (N + 1)), sq_nonneg (y (N + 1 + 1))]

/-- The edges of a path `y 0 – y 1 – ⋯ – y (N+2)` (at least two edges): both end vertices are
charged `30/17` and every inner vertex at most `37/8`. -/
lemma path_both (y : ℕ → ℝ) (N : ℕ) :
    ∑ e ∈ range (N + 2), (y e - y (e + 1)) ^ 2
      ≤ 30 / 17 * (y 0 ^ 2 + y (N + 2) ^ 2)
        + 37 / 8 * ∑ i ∈ range (N + 1), y (i + 1) ^ 2 := by
  have h1 := path_left y N
  have h2 := sq_sub_le_outer (y (N + 2)) (y (N + 1))
  have h3 : (y (N + 1) - y (N + 2)) ^ 2 = (y (N + 2) - y (N + 1)) ^ 2 := by ring
  have e2 : N + 1 + 1 = N + 2 := rfl
  rw [sum_range_succ (fun e => (y e - y (e + 1)) ^ 2) (N + 1),
    sum_range_succ (fun i => y (i + 1) ^ 2) N, e2]
  nlinarith [sq_nonneg (y (N + 1))]

/-- The five edges of a diamond on `a, b, c, e` (the missing edge is `a – b`) together with one
pendant edge `p – a`: the Laplacian form is at most `(37/8)(a² + b² + c² + e²) + (20/7) p²`. -/
lemma diamond_attach_le (a b c e p : ℝ) :
    (a - c) ^ 2 + (a - e) ^ 2 + (b - c) ^ 2 + (b - e) ^ 2 + (c - e) ^ 2 + (p - a) ^ 2
      ≤ 37 / 8 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) + 20 / 7 * p ^ 2 := by
  have key : 37 / 8 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) + 20 / 7 * p ^ 2
      - ((a - c) ^ 2 + (a - e) ^ 2 + (b - c) ^ 2 + (b - e) ^ 2 + (c - e) ^ 2 + (p - a) ^ 2)
      = 8 / 21 * (21 / 8 * b + c + e) ^ 2 + 13 / 14 * (14 / 13 * a + c + e) ^ 2
        + 13 / 7 * (7 / 13 * a + p) ^ 2 + 1 / 336 * (c + e) ^ 2 + 5 / 16 * (c - e) ^ 2
        + 1 / 104 * a ^ 2 := by
    ring
  have hnn : 0 ≤ 8 / 21 * (21 / 8 * b + c + e) ^ 2 + 13 / 14 * (14 / 13 * a + c + e) ^ 2
        + 13 / 7 * (7 / 13 * a + p) ^ 2 + 1 / 336 * (c + e) ^ 2 + 5 / 16 * (c - e) ^ 2
        + 1 / 104 * a ^ 2 := by
    positivity
  linarith

end Conj2
