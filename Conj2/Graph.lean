import Mathlib

/-!
# The graph `G₁₁`: two diamonds joined by a path

`G₁₁` has vertex set `Fin 11` and 14 edges:

* a diamond (`K₄` minus an edge) on `{0, 1, 2, 3}`, the missing edge being `0 – 1`;
* a second diamond on `{4, 5, 6, 7}`, the missing edge being `4 – 5`;
* the path `0 – 8 – 9 – 10 – 4` joining a degree-2 vertex of each diamond.

The graph is defined from its `0/1` adjacency table; `Conj2.adj_iff_edges` certifies that this
table is exactly the edge list above. The two quadratic forms `x ⬝ᵥ A *ᵥ y` (adjacency) and
`z ⬝ᵥ L *ᵥ z` (Laplacian) are then written out as explicit polynomials.
-/

open Matrix SimpleGraph

namespace Conj2

/-- The `0/1` adjacency table of `G₁₁` (row `i`, column `j`). -/
def adjTable : Fin 11 → Fin 11 → ℕ :=
  ![![0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]]

/-- The 14 edges of `G₁₁`. -/
def edges : List (Fin 11 × Fin 11) :=
  [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3),
   (4, 6), (4, 7), (5, 6), (5, 7), (6, 7),
   (0, 8), (8, 9), (9, 10), (10, 4)]

/-- `G₁₁`: two diamonds joined by a path with three inner vertices. -/
def G11 : SimpleGraph (Fin 11) where
  Adj i j := adjTable i j = 1
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G11.Adj := fun i j => inferInstanceAs (Decidable (adjTable i j = 1))

lemma adj_iff (i j : Fin 11) : G11.Adj i j ↔ adjTable i j = 1 := Iff.rfl

/-- The adjacency table is exactly the list of 14 edges. -/
theorem adj_iff_edges : ∀ i j : Fin 11, G11.Adj i j ↔ (i, j) ∈ edges ∨ (j, i) ∈ edges := by
  decide

/-- Sum over `Fin 9`, written out. -/
lemma sum_univ_nine {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

/-- Sum over `Fin 10`, written out. -/
lemma sum_univ_ten {M : Type*} [AddCommMonoid M] (f : Fin 10 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, sum_univ_nine]
  rfl

/-- Sum over `Fin 11`, written out. -/
lemma sum_univ_eleven {M : Type*} [AddCommMonoid M] (f : Fin 11 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  rw [Fin.sum_univ_castSucc, sum_univ_ten]
  rfl

/-- `G₁₁` is connected. -/
theorem G11_connected : G11.Connected := by
  rw [connected_iff_exists_forall_reachable]
  have a02 : G11.Adj 0 2 := by decide
  have a03 : G11.Adj 0 3 := by decide
  have a21 : G11.Adj 2 1 := by decide
  have a08 : G11.Adj 0 8 := by decide
  have a89 : G11.Adj 8 9 := by decide
  have a9t : G11.Adj 9 10 := by decide
  have at4 : G11.Adj 10 4 := by decide
  have a46 : G11.Adj 4 6 := by decide
  have a47 : G11.Adj 4 7 := by decide
  have a65 : G11.Adj 6 5 := by decide
  have r0 : G11.Reachable 0 0 := Reachable.refl 0
  have r2 : G11.Reachable 0 2 := a02.reachable
  have r3 : G11.Reachable 0 3 := a03.reachable
  have r1 : G11.Reachable 0 1 := r2.trans a21.reachable
  have r8 : G11.Reachable 0 8 := a08.reachable
  have r9 : G11.Reachable 0 9 := r8.trans a89.reachable
  have r10 : G11.Reachable 0 10 := r9.trans a9t.reachable
  have r4 : G11.Reachable 0 4 := r10.trans at4.reachable
  have r6 : G11.Reachable 0 6 := r4.trans a46.reachable
  have r7 : G11.Reachable 0 7 := r4.trans a47.reachable
  have r5 : G11.Reachable 0 5 := r6.trans a65.reachable
  refine ⟨0, fun w => ?_⟩
  fin_cases w
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10

/-- The adjacency bilinear form of `G₁₁`: each vertex times the sum over its neighbours. -/
lemma adj_form (x y : Fin 11 → ℝ) :
    x ⬝ᵥ (G11.adjMatrix ℝ *ᵥ y) =
      x 0 * (y 2 + y 3 + y 8) + x 1 * (y 2 + y 3) + x 2 * (y 0 + y 1 + y 3)
      + x 3 * (y 0 + y 1 + y 2) + x 4 * (y 6 + y 7 + y 10) + x 5 * (y 6 + y 7)
      + x 6 * (y 4 + y 5 + y 7) + x 7 * (y 4 + y 5 + y 6) + x 8 * (y 0 + y 9)
      + x 9 * (y 8 + y 10) + x 10 * (y 4 + y 9) := by
  rw [dotProduct_mulVec_adjMatrix]
  simp only [sum_univ_eleven, adj_iff, adjTable]
  simp
  ring

/-- The Laplacian quadratic form of `G₁₁`: the sum of `(z i - z j)²` over the 14 edges. -/
lemma lap_form (z : Fin 11 → ℝ) :
    z ⬝ᵥ (G11.lapMatrix ℝ *ᵥ z) =
      (z 0 - z 2) ^ 2 + (z 0 - z 3) ^ 2 + (z 1 - z 2) ^ 2 + (z 1 - z 3) ^ 2 + (z 2 - z 3) ^ 2
      + (z 4 - z 6) ^ 2 + (z 4 - z 7) ^ 2 + (z 5 - z 6) ^ 2 + (z 5 - z 7) ^ 2 + (z 6 - z 7) ^ 2
      + (z 0 - z 8) ^ 2 + (z 8 - z 9) ^ 2 + (z 9 - z 10) ^ 2 + (z 10 - z 4) ^ 2 := by
  rw [← Matrix.toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
  simp only [sum_univ_eleven, adj_iff, adjTable]
  simp
  ring

/-- The squared norm on `Fin 11 → ℝ`, written out. -/
lemma dot_self (z : Fin 11 → ℝ) :
    z ⬝ᵥ z = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2 + z 5 ^ 2 + z 6 ^ 2 + z 7 ^ 2
      + z 8 ^ 2 + z 9 ^ 2 + z 10 ^ 2 := by
  simp only [dotProduct, sum_univ_eleven]
  ring

end Conj2
