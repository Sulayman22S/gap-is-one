import Conj2

/-! Negative controls for the infinite family. Every `example` marked FALSE states something
untrue and must be REJECTED; the ones marked TRUE must be accepted. Expected: exactly 4 errors. -/

open Matrix SimpleGraph Finset Conj2 Conj2.Family

-- TRUE: the first path vertex is adjacent to diamond vertex 0, for every N.
example (N : ℕ) : (fam N).Adj (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 0) :=
  (adj_pd N 0 0).mpr (Or.inl ⟨rfl, rfl⟩)

-- TRUE: the path inequality as proved.
example (y : ℕ → ℝ) (N : ℕ) :
    ∑ e ∈ range (N + 2), (y e - y (e + 1)) ^ 2
      ≤ 30 / 17 * (y 0 ^ 2 + y (N + 2) ^ 2) + 37 / 8 * ∑ i ∈ range (N + 1), y (i + 1) ^ 2 :=
  path_both y N

-- FALSE 1: the first path vertex adjacent to diamond vertex 1.
example (N : ℕ) : (fam N).Adj (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 1) :=
  (adj_pd N 0 1).mpr (Or.inl ⟨rfl, rfl⟩)

-- FALSE 2: the path inequality with inner weight 4 instead of 37/8
-- (false already for N = 0, y = (1, -2, 1): 18 > 30/17 * 2 + 16).
example (y : ℕ → ℝ) (N : ℕ) :
    ∑ e ∈ range (N + 2), (y e - y (e + 1)) ^ 2
      ≤ 30 / 17 * (y 0 ^ 2 + y (N + 2) ^ 2) + 4 * ∑ i ∈ range (N + 1), y (i + 1) ^ 2 := by
  have h1 := path_left y N
  have h2 := sq_sub_le_outer (y (N + 2)) (y (N + 1))
  have h3 : (y (N + 1) - y (N + 2)) ^ 2 = (y (N + 2) - y (N + 1)) ^ 2 := by ring
  have e2 : N + 1 + 1 = N + 2 := rfl
  rw [sum_range_succ (fun e => (y e - y (e + 1)) ^ 2) (N + 1),
    sum_range_succ (fun i => y (i + 1) ^ 2) N, e2]
  nlinarith [sq_nonneg (y (N + 1))]

-- FALSE 3: the diamond inequality with 4 instead of 37/8.
example (a b c e p : ℝ) :
    (a - c) ^ 2 + (a - e) ^ 2 + (b - c) ^ 2 + (b - e) ^ 2 + (c - e) ^ 2 + (p - a) ^ 2
      ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) + 20 / 7 * p ^ 2 := by
  nlinarith [sq_nonneg (21 / 8 * b + c + e), sq_nonneg (14 / 13 * a + c + e),
    sq_nonneg (7 / 13 * a + p), sq_nonneg (c + e), sq_nonneg (c - e), sq_nonneg a]

-- FALSE 4: a wrong renaming between G11 and D 0 (two entries swapped).
example : ∀ i j : Fin 11, G11.Adj i j ↔
    (fam 0).Adj ((![3, 4, 5, 6, 7, 8, 9, 10, 0, 2, 1] : Fin 11 → Fin (0 + 3 + 8)) i)
      ((![3, 4, 5, 6, 7, 8, 9, 10, 0, 2, 1] : Fin 11 → Fin (0 + 3 + 8)) j) := by
  decide
