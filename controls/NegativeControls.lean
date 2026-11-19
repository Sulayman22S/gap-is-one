import Conj2

/-! Negative controls. Every `example` marked FALSE states something untrue and must be REJECTED.
The one marked TRUE must be accepted. Expected: exactly 3 errors. -/

open Matrix SimpleGraph Conj2

-- TRUE (positive control): 9 and 10 are adjacent.
example : G11.Adj 9 10 := by decide

-- FALSE 1: the sum-of-squares identity with 23/5 = 4.6 in place of 37/8 = 4.625.
-- (4.6 is below the true largest Laplacian eigenvalue 4.618..., so no certificate can exist.)
example (z : Fin 11 → ℝ) :
    23 / 5 * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2 + z 5 ^ 2 + z 6 ^ 2 + z 7 ^ 2
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

-- FALSE 2: a Rayleigh quotient of 300/111 for the test vector (the true value is 293/111).
example : (300 : ℝ) / 111 * (f₁ ⬝ᵥ f₁) ≤ f₁ ⬝ᵥ (G11.adjMatrix ℝ *ᵥ f₁) := by
  rw [f₁_dot_f₁, f₁_adj_f₁]; norm_num

-- FALSE 3: the edge list with the edge 9 – 10 left out.
example : ∀ i j : Fin 11, G11.Adj i j ↔
    (i, j) ∈ [((0 : Fin 11), (2 : Fin 11)), (0, 3), (1, 2), (1, 3), (2, 3), (4, 6), (4, 7),
      (5, 6), (5, 7), (6, 7), (0, 8), (8, 9), (10, 4)] ∨
    (j, i) ∈ [((0 : Fin 11), (2 : Fin 11)), (0, 3), (1, 2), (1, 3), (2, 3), (4, 6), (4, 7),
      (5, 6), (5, 7), (6, 7), (0, 8), (8, 9), (10, 4)] := by
  decide
