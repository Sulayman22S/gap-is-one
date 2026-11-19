import Conj2.PathLemmas
import Conj2.Main

/-!
# Infinitely many counterexamples to `λ₂ ≤ μ₁ − 2`

For every `N : ℕ` let `D N` (`Conj2.Family.fam N`) be the graph on `N + 11` vertices made of two
diamonds (`K₄` minus an edge) joined, through a degree-2 vertex of each, by a path with `N + 3`
inner vertices. `D 0` is the 11-vertex graph `G₁₁` of `Conj2.Graph`, up to the names of the
vertices.

Vertices of `fam N : SimpleGraph (Fin (N + 3 + 8))`:

* `Fin.castAdd 8 i`, `i : Fin (N + 3)`: the path vertices, in order;
* `Fin.natAdd (N + 3) a`, `a : Fin 8`: the diamond vertices. Diamond 1 is `a ∈ {0,1,2,3}` with
  missing edge `0 – 1`, attached at `a = 0` to the first path vertex; diamond 2 is
  `a ∈ {4,5,6,7}` with missing edge `4 – 5`, attached at `a = 4` to the last path vertex.

The same two bounds as for `G₁₁` hold for every `N`:

* `μ₁(D N) ≤ 37/8` (`mu₁_fam_le`): each diamond with its attachment edge is bounded as in
  `diamond_attach_le`, and the path edges are bounded by `path_both` (induction along the path);
* `λ₂(D N) ≥ 293/111` (`lambda₂_fam_ge`): the two test vectors live on a diamond and its
  attachment vertex, and never interact because the path has at least three inner vertices.

## Main statements

* `Conj2.Family.family_counterexample`: every `D N` is connected and has `μ₁ − 2 < λ₂`.
* `Conj2.Family.exists_counterexample`: for every `n ≥ 11` there is a connected graph on
  `Fin n` with `μ₁ − 2 < λ₂`.
* `Conj2.Family.conjecture_two_false_of_card`: the conjecture fails on `n` vertices for every
  `n ≥ 11`.
-/

open Matrix SimpleGraph Finset

namespace Conj2
namespace Family

/-! ### The graphs -/

/-- `0/1` adjacency table of two disjoint diamonds on `Fin 8`: `{0,1,2,3}` with missing edge
`0 – 1`, and `{4,5,6,7}` with missing edge `4 – 5`. -/
def diamonds : Fin 8 → Fin 8 → ℕ :=
  ![![0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0]]

lemma diamonds_symm : ∀ a b : Fin 8, diamonds a b = 1 → diamonds b a = 1 := by decide

lemma diamonds_irrefl : ∀ a : Fin 8, diamonds a a ≠ 1 := by decide

/-- Adjacency of `D N` on the vertex set "path `⊕` diamonds":
consecutive path vertices; the first path vertex and diamond vertex `0`; the last path vertex
and diamond vertex `4`; and the diamond edges. -/
def rel (N : ℕ) : Fin (N + 3) ⊕ Fin 8 → Fin (N + 3) ⊕ Fin 8 → Prop
  | .inl i, .inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | .inl i, .inr b => (i = 0 ∧ b = 0) ∨ (i = Fin.last (N + 2) ∧ b = 4)
  | .inr a, .inl j => (j = 0 ∧ a = 0) ∨ (j = Fin.last (N + 2) ∧ a = 4)
  | .inr a, .inr b => diamonds a b = 1

lemma rel_symm (N : ℕ) : ∀ u v, rel N u v → rel N v u := by
  rintro (i | a) (j | b) h
  · exact Or.symm h
  · exact h
  · exact h
  · exact diamonds_symm a b h

lemma rel_irrefl (N : ℕ) : ∀ u, ¬rel N u u := by
  rintro (i | a) h
  · have h' : i.val + 1 = i.val ∨ i.val + 1 = i.val := h
    omega
  · exact diamonds_irrefl a h

instance relDecidable (N : ℕ) : DecidableRel (rel N) := fun u v =>
  match u, v with
  | .inl i, .inl j => inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))
  | .inl i, .inr b =>
      inferInstanceAs (Decidable ((i = 0 ∧ b = 0) ∨ (i = Fin.last (N + 2) ∧ b = 4)))
  | .inr a, .inl j =>
      inferInstanceAs (Decidable ((j = 0 ∧ a = 0) ∨ (j = Fin.last (N + 2) ∧ a = 4)))
  | .inr a, .inr b => inferInstanceAs (Decidable (diamonds a b = 1))

/-- `D N`: two diamonds joined by a path with `N + 3` inner vertices; `N + 11` vertices. -/
def fam (N : ℕ) : SimpleGraph (Fin (N + 3 + 8)) where
  Adj u v := rel N (finSumFinEquiv.symm u) (finSumFinEquiv.symm v)
  symm := ⟨fun _ _ h => rel_symm N _ _ h⟩
  loopless := ⟨fun _ h => rel_irrefl N _ h⟩

instance (N : ℕ) : DecidableRel (fam N).Adj := fun u v =>
  relDecidable N (finSumFinEquiv.symm u) (finSumFinEquiv.symm v)

/-- Two path vertices are adjacent iff they are consecutive. -/
lemma adj_pp (N : ℕ) (i j : Fin (N + 3)) :
    (fam N).Adj (Fin.castAdd 8 i) (Fin.castAdd 8 j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  show rel N (finSumFinEquiv.symm (Fin.castAdd 8 i)) (finSumFinEquiv.symm (Fin.castAdd 8 j)) ↔ _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- A path vertex and a diamond vertex are adjacent iff they are an attachment pair. -/
lemma adj_pd (N : ℕ) (i : Fin (N + 3)) (b : Fin 8) :
    (fam N).Adj (Fin.castAdd 8 i) (Fin.natAdd (N + 3) b)
      ↔ (i = 0 ∧ b = 0) ∨ (i = Fin.last (N + 2) ∧ b = 4) := by
  show rel N (finSumFinEquiv.symm (Fin.castAdd 8 i))
    (finSumFinEquiv.symm (Fin.natAdd (N + 3) b)) ↔ _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  rfl

lemma adj_dp (N : ℕ) (a : Fin 8) (j : Fin (N + 3)) :
    (fam N).Adj (Fin.natAdd (N + 3) a) (Fin.castAdd 8 j)
      ↔ (j = 0 ∧ a = 0) ∨ (j = Fin.last (N + 2) ∧ a = 4) := by
  show rel N (finSumFinEquiv.symm (Fin.natAdd (N + 3) a))
    (finSumFinEquiv.symm (Fin.castAdd 8 j)) ↔ _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Two diamond vertices are adjacent iff the table says so. -/
lemma adj_dd (N : ℕ) (a b : Fin 8) :
    (fam N).Adj (Fin.natAdd (N + 3) a) (Fin.natAdd (N + 3) b) ↔ diamonds a b = 1 := by
  show rel N (finSumFinEquiv.symm (Fin.natAdd (N + 3) a))
    (finSumFinEquiv.symm (Fin.natAdd (N + 3) b)) ↔ _
  rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-! ### Sums over ordered adjacent pairs -/

/-- A double sum over `Fin (m + n)` splits into four blocks. -/
lemma sum_blocks {m n : ℕ} (K : Fin (m + n) → Fin (m + n) → ℝ) :
    ∑ u, ∑ v, K u v
      = ∑ i : Fin m, ∑ j : Fin m, K (Fin.castAdd n i) (Fin.castAdd n j)
        + ∑ i : Fin m, ∑ b : Fin n, K (Fin.castAdd n i) (Fin.natAdd m b)
        + ∑ a : Fin n, ∑ j : Fin m, K (Fin.natAdd m a) (Fin.castAdd n j)
        + ∑ a : Fin n, ∑ b : Fin n, K (Fin.natAdd m a) (Fin.natAdd m b) := by
  simp only [Fin.sum_univ_add, sum_add_distrib]
  ring

/-- The attachment block, from the path side. -/
lemma sum_attach (N : ℕ) (H : Fin (N + 3) → Fin 8 → ℝ) :
    ∑ i, ∑ b, (if (i = 0 ∧ b = 0) ∨ (i = Fin.last (N + 2) ∧ b = 4) then H i b else 0)
      = H 0 0 + H (Fin.last (N + 2)) 4 := by
  simp [Fin.sum_univ_eight, sum_add_distrib]

/-- The attachment block, from the diamond side. -/
lemma sum_attach' (N : ℕ) (H : Fin 8 → Fin (N + 3) → ℝ) :
    ∑ a, ∑ j, (if (j = 0 ∧ a = 0) ∨ (j = Fin.last (N + 2) ∧ a = 4) then H a j else 0)
      = H 0 0 + H 4 (Fin.last (N + 2)) := by
  simp [Fin.sum_univ_eight]

/-- The diamond block: the ten diamond edges, each in both directions. -/
lemma sum_diamonds (H : Fin 8 → Fin 8 → ℝ) :
    ∑ a, ∑ b, (if diamonds a b = 1 then H a b else 0)
      = H 0 2 + H 0 3 + H 1 2 + H 1 3 + H 2 0 + H 2 1 + H 2 3 + H 3 0 + H 3 1 + H 3 2
        + H 4 6 + H 4 7 + H 5 6 + H 5 7 + H 6 4 + H 6 5 + H 6 7 + H 7 4 + H 7 5 + H 7 6 := by
  simp [Fin.sum_univ_eight, diamonds]
  ring

/-- The sum over ordered adjacent pairs of `fam N`, split into the path, the two attachment
edges (in both directions) and the two diamonds. -/
lemma sum_adj (N : ℕ) (F : Fin (N + 3 + 8) → Fin (N + 3 + 8) → ℝ) :
    ∑ u, ∑ v, (if (fam N).Adj u v then F u v else 0)
      = (∑ i : Fin (N + 3), ∑ j : Fin (N + 3),
            if i.val + 1 = j.val ∨ j.val + 1 = i.val
              then F (Fin.castAdd 8 i) (Fin.castAdd 8 j) else 0)
        + (F (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 0)
            + F (Fin.castAdd 8 (Fin.last (N + 2))) (Fin.natAdd (N + 3) 4))
        + (F (Fin.natAdd (N + 3) 0) (Fin.castAdd 8 0)
            + F (Fin.natAdd (N + 3) 4) (Fin.castAdd 8 (Fin.last (N + 2))))
        + (F (Fin.natAdd (N + 3) 0) (Fin.natAdd (N + 3) 2)
            + F (Fin.natAdd (N + 3) 0) (Fin.natAdd (N + 3) 3)
            + F (Fin.natAdd (N + 3) 1) (Fin.natAdd (N + 3) 2)
            + F (Fin.natAdd (N + 3) 1) (Fin.natAdd (N + 3) 3)
            + F (Fin.natAdd (N + 3) 2) (Fin.natAdd (N + 3) 0)
            + F (Fin.natAdd (N + 3) 2) (Fin.natAdd (N + 3) 1)
            + F (Fin.natAdd (N + 3) 2) (Fin.natAdd (N + 3) 3)
            + F (Fin.natAdd (N + 3) 3) (Fin.natAdd (N + 3) 0)
            + F (Fin.natAdd (N + 3) 3) (Fin.natAdd (N + 3) 1)
            + F (Fin.natAdd (N + 3) 3) (Fin.natAdd (N + 3) 2)
            + F (Fin.natAdd (N + 3) 4) (Fin.natAdd (N + 3) 6)
            + F (Fin.natAdd (N + 3) 4) (Fin.natAdd (N + 3) 7)
            + F (Fin.natAdd (N + 3) 5) (Fin.natAdd (N + 3) 6)
            + F (Fin.natAdd (N + 3) 5) (Fin.natAdd (N + 3) 7)
            + F (Fin.natAdd (N + 3) 6) (Fin.natAdd (N + 3) 4)
            + F (Fin.natAdd (N + 3) 6) (Fin.natAdd (N + 3) 5)
            + F (Fin.natAdd (N + 3) 6) (Fin.natAdd (N + 3) 7)
            + F (Fin.natAdd (N + 3) 7) (Fin.natAdd (N + 3) 4)
            + F (Fin.natAdd (N + 3) 7) (Fin.natAdd (N + 3) 5)
            + F (Fin.natAdd (N + 3) 7) (Fin.natAdd (N + 3) 6)) := by
  rw [sum_blocks]
  simp only [adj_pp, adj_pd, adj_dp, adj_dd]
  rw [sum_attach N (fun i b => F (Fin.castAdd 8 i) (Fin.natAdd (N + 3) b)),
    sum_attach' N (fun a j => F (Fin.natAdd (N + 3) a) (Fin.castAdd 8 j)),
    sum_diamonds (fun a b => F (Fin.natAdd (N + 3) a) (Fin.natAdd (N + 3) b))]

/-! ### The Laplacian bound `μ₁(D N) ≤ 37/8` -/

/-- The values of `z` along the path, as a sequence on `ℕ` (zero beyond the path). -/
def pathVal (N : ℕ) (z : Fin (N + 3 + 8) → ℝ) (m : ℕ) : ℝ :=
  if h : m < N + 3 then z (Fin.castAdd 8 ⟨m, h⟩) else 0

lemma pathVal_val (N : ℕ) (z : Fin (N + 3 + 8) → ℝ) (i : Fin (N + 3)) :
    pathVal N z i.val = z (Fin.castAdd 8 i) := by
  simp [pathVal]

lemma pathVal_zero (N : ℕ) (z : Fin (N + 3 + 8) → ℝ) :
    pathVal N z 0 = z (Fin.castAdd 8 0) :=
  pathVal_val N z 0

lemma pathVal_last (N : ℕ) (z : Fin (N + 3 + 8) → ℝ) :
    pathVal N z (N + 2) = z (Fin.castAdd 8 (Fin.last (N + 2))) :=
  pathVal_val N z (Fin.last (N + 2))

/-- The Laplacian quadratic form of `D N`: the path edges, the two attachment edges and the
five edges of each diamond. -/
lemma lap_form (N : ℕ) (z : Fin (N + 3 + 8) → ℝ) :
    z ⬝ᵥ ((fam N).lapMatrix ℝ *ᵥ z)
      = ∑ e ∈ range (N + 2), (pathVal N z e - pathVal N z (e + 1)) ^ 2
        + ((z (Fin.natAdd (N + 3) 0) - z (Fin.natAdd (N + 3) 2)) ^ 2
            + (z (Fin.natAdd (N + 3) 0) - z (Fin.natAdd (N + 3) 3)) ^ 2
            + (z (Fin.natAdd (N + 3) 1) - z (Fin.natAdd (N + 3) 2)) ^ 2
            + (z (Fin.natAdd (N + 3) 1) - z (Fin.natAdd (N + 3) 3)) ^ 2
            + (z (Fin.natAdd (N + 3) 2) - z (Fin.natAdd (N + 3) 3)) ^ 2
            + (pathVal N z 0 - z (Fin.natAdd (N + 3) 0)) ^ 2)
        + ((z (Fin.natAdd (N + 3) 4) - z (Fin.natAdd (N + 3) 6)) ^ 2
            + (z (Fin.natAdd (N + 3) 4) - z (Fin.natAdd (N + 3) 7)) ^ 2
            + (z (Fin.natAdd (N + 3) 5) - z (Fin.natAdd (N + 3) 6)) ^ 2
            + (z (Fin.natAdd (N + 3) 5) - z (Fin.natAdd (N + 3) 7)) ^ 2
            + (z (Fin.natAdd (N + 3) 6) - z (Fin.natAdd (N + 3) 7)) ^ 2
            + (pathVal N z (N + 2) - z (Fin.natAdd (N + 3) 4)) ^ 2) := by
  rw [← Matrix.toLinearMap₂'_apply', lapMatrix_toLinearMap₂', sum_adj]
  -- the path block: every path edge appears once in each direction
  have hp : (∑ i : Fin (N + 3), ∑ j : Fin (N + 3),
        if i.val + 1 = j.val ∨ j.val + 1 = i.val
          then (z (Fin.castAdd 8 i) - z (Fin.castAdd 8 j)) ^ 2 else 0)
      = ∑ e ∈ range (N + 2), ((pathVal N z e - pathVal N z (e + 1)) ^ 2
          + (pathVal N z (e + 1) - pathVal N z e) ^ 2) := by
    rw [← sum_range_consecutive (N + 2) (fun a b => (pathVal N z a - pathVal N z b) ^ 2),
      ← sum_fin_fin (N + 3)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [pathVal_val, pathVal_val]
  have hs : ∑ e ∈ range (N + 2), ((pathVal N z e - pathVal N z (e + 1)) ^ 2
          + (pathVal N z (e + 1) - pathVal N z e) ^ 2)
      = 2 * ∑ e ∈ range (N + 2), (pathVal N z e - pathVal N z (e + 1)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hp, hs, ← pathVal_zero N z, ← pathVal_last N z]
  ring

/-- The squared norm on the vertex set of `D N`. -/
lemma dot_self (N : ℕ) (z : Fin (N + 3 + 8) → ℝ) :
    z ⬝ᵥ z = pathVal N z 0 ^ 2 + ∑ i ∈ range (N + 1), pathVal N z (i + 1) ^ 2
        + pathVal N z (N + 2) ^ 2
        + (z (Fin.natAdd (N + 3) 0) ^ 2 + z (Fin.natAdd (N + 3) 1) ^ 2
            + z (Fin.natAdd (N + 3) 2) ^ 2 + z (Fin.natAdd (N + 3) 3) ^ 2)
        + (z (Fin.natAdd (N + 3) 4) ^ 2 + z (Fin.natAdd (N + 3) 5) ^ 2
            + z (Fin.natAdd (N + 3) 6) ^ 2 + z (Fin.natAdd (N + 3) 7) ^ 2) := by
  have hpath : ∑ i : Fin (N + 3), z (Fin.castAdd 8 i) * z (Fin.castAdd 8 i)
      = ∑ m ∈ range (N + 3), pathVal N z m ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => pathVal N z m ^ 2) (N + 3)]
    exact Finset.sum_congr rfl fun i _ => by rw [pathVal_val]; ring
  simp only [dotProduct]
  rw [Fin.sum_univ_add, Fin.sum_univ_eight, hpath,
    sum_range_succ (fun m => pathVal N z m ^ 2) (N + 2),
    sum_range_succ' (fun m => pathVal N z m ^ 2) (N + 1)]
  ring

/-- `zᵀ L z ≤ (37/8) ‖z‖²` for the Laplacian of every `D N`. -/
lemma lap_quadForm_le (N : ℕ) (z : Fin (N + 3 + 8) → ℝ) :
    z ⬝ᵥ ((fam N).lapMatrix ℝ *ᵥ z) ≤ 37 / 8 * (z ⬝ᵥ z) := by
  rw [lap_form, dot_self]
  have h1 := path_both (pathVal N z) N
  have h2 := diamond_attach_le (z (Fin.natAdd (N + 3) 0)) (z (Fin.natAdd (N + 3) 1))
    (z (Fin.natAdd (N + 3) 2)) (z (Fin.natAdd (N + 3) 3)) (pathVal N z 0)
  have h3 := diamond_attach_le (z (Fin.natAdd (N + 3) 4)) (z (Fin.natAdd (N + 3) 5))
    (z (Fin.natAdd (N + 3) 6)) (z (Fin.natAdd (N + 3) 7)) (pathVal N z (N + 2))
  nlinarith [sq_nonneg (pathVal N z 0), sq_nonneg (pathVal N z (N + 2))]

/-- Every Laplacian eigenvalue of `D N` is at most `37/8`; in particular `μ₁(D N) ≤ 37/8`. -/
theorem mu₁_fam_le (N : ℕ) : mu₁ (fam N) (by omega) ≤ 37 / 8 :=
  eigenvalues₀_le_of_quadForm_le ((fam N).isHermitian_lapMatrix ℝ) (lap_quadForm_le N) _

/-! ### The adjacency bound `λ₂(D N) ≥ 293/111` -/

/-- The adjacency bilinear form of `D N`, split as in `sum_adj`. -/
lemma adj_form (N : ℕ) (x y : Fin (N + 3 + 8) → ℝ) :
    x ⬝ᵥ ((fam N).adjMatrix ℝ *ᵥ y)
      = (∑ i : Fin (N + 3), ∑ j : Fin (N + 3),
            if i.val + 1 = j.val ∨ j.val + 1 = i.val
              then x (Fin.castAdd 8 i) * y (Fin.castAdd 8 j) else 0)
        + (x (Fin.castAdd 8 0) * y (Fin.natAdd (N + 3) 0)
            + x (Fin.castAdd 8 (Fin.last (N + 2))) * y (Fin.natAdd (N + 3) 4))
        + (x (Fin.natAdd (N + 3) 0) * y (Fin.castAdd 8 0)
            + x (Fin.natAdd (N + 3) 4) * y (Fin.castAdd 8 (Fin.last (N + 2))))
        + (x (Fin.natAdd (N + 3) 0) * y (Fin.natAdd (N + 3) 2)
            + x (Fin.natAdd (N + 3) 0) * y (Fin.natAdd (N + 3) 3)
            + x (Fin.natAdd (N + 3) 1) * y (Fin.natAdd (N + 3) 2)
            + x (Fin.natAdd (N + 3) 1) * y (Fin.natAdd (N + 3) 3)
            + x (Fin.natAdd (N + 3) 2) * y (Fin.natAdd (N + 3) 0)
            + x (Fin.natAdd (N + 3) 2) * y (Fin.natAdd (N + 3) 1)
            + x (Fin.natAdd (N + 3) 2) * y (Fin.natAdd (N + 3) 3)
            + x (Fin.natAdd (N + 3) 3) * y (Fin.natAdd (N + 3) 0)
            + x (Fin.natAdd (N + 3) 3) * y (Fin.natAdd (N + 3) 1)
            + x (Fin.natAdd (N + 3) 3) * y (Fin.natAdd (N + 3) 2)
            + x (Fin.natAdd (N + 3) 4) * y (Fin.natAdd (N + 3) 6)
            + x (Fin.natAdd (N + 3) 4) * y (Fin.natAdd (N + 3) 7)
            + x (Fin.natAdd (N + 3) 5) * y (Fin.natAdd (N + 3) 6)
            + x (Fin.natAdd (N + 3) 5) * y (Fin.natAdd (N + 3) 7)
            + x (Fin.natAdd (N + 3) 6) * y (Fin.natAdd (N + 3) 4)
            + x (Fin.natAdd (N + 3) 6) * y (Fin.natAdd (N + 3) 5)
            + x (Fin.natAdd (N + 3) 6) * y (Fin.natAdd (N + 3) 7)
            + x (Fin.natAdd (N + 3) 7) * y (Fin.natAdd (N + 3) 4)
            + x (Fin.natAdd (N + 3) 7) * y (Fin.natAdd (N + 3) 5)
            + x (Fin.natAdd (N + 3) 7) * y (Fin.natAdd (N + 3) 6)) := by
  rw [dotProduct_mulVec_adjMatrix, sum_adj]

/-- Test vector supported on the first diamond and the first path vertex. -/
def g₁ (N : ℕ) : Fin (N + 3 + 8) → ℝ := fun u =>
  Fin.addCases (motive := fun _ => ℝ) (fun i : Fin (N + 3) => if i = 0 then 3 else 0)
    (fun a : Fin 8 => ![7, 6, 8, 8, 0, 0, 0, 0] a) u

/-- Test vector supported on the second diamond and the last path vertex. -/
def g₂ (N : ℕ) : Fin (N + 3 + 8) → ℝ := fun u =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun i : Fin (N + 3) => if i = Fin.last (N + 2) then 3 else 0)
    (fun a : Fin 8 => ![0, 0, 0, 0, 7, 6, 8, 8] a) u

lemma g₁_path (N : ℕ) (i : Fin (N + 3)) : g₁ N (Fin.castAdd 8 i) = if i = 0 then 3 else 0 := by
  simp only [g₁, Fin.addCases_left]

lemma g₁_diam (N : ℕ) (a : Fin 8) :
    g₁ N (Fin.natAdd (N + 3) a) = ![7, 6, 8, 8, 0, 0, 0, 0] a := by
  simp only [g₁, Fin.addCases_right]

lemma g₂_path (N : ℕ) (i : Fin (N + 3)) :
    g₂ N (Fin.castAdd 8 i) = if i = Fin.last (N + 2) then 3 else 0 := by
  simp only [g₂, Fin.addCases_left]

lemma g₂_diam (N : ℕ) (a : Fin 8) :
    g₂ N (Fin.natAdd (N + 3) a) = ![0, 0, 0, 0, 7, 6, 8, 8] a := by
  simp only [g₂, Fin.addCases_right]

/-- The first and the last path vertex are different. -/
lemma zero_ne_last (N : ℕ) : (0 : Fin (N + 3)) ≠ Fin.last (N + 2) := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h'
  omega

/-- The path block vanishes on two vectors each supported on a single path vertex, as soon as
those two vertices are not adjacent. -/
lemma path_block_zero (N : ℕ) (p q : Fin (N + 3))
    (hpq : ¬(p.val + 1 = q.val ∨ q.val + 1 = p.val)) (c d : ℝ) :
    (∑ i : Fin (N + 3), ∑ j : Fin (N + 3),
        if i.val + 1 = j.val ∨ j.val + 1 = i.val
          then (if i = p then c else 0) * (if j = q then d else 0) else 0) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases hi : i = p
  · by_cases hj : j = q
    · rw [hi, hj, ite_eq_right hpq]
    · simp [hj]
  · simp [hi]

lemma not_adj_zero_zero (N : ℕ) :
    ¬((0 : Fin (N + 3)).val + 1 = (0 : Fin (N + 3)).val
      ∨ (0 : Fin (N + 3)).val + 1 = (0 : Fin (N + 3)).val) := by
  simp only [Fin.val_zero]
  omega

lemma not_adj_last_last (N : ℕ) :
    ¬((Fin.last (N + 2)).val + 1 = (Fin.last (N + 2)).val
      ∨ (Fin.last (N + 2)).val + 1 = (Fin.last (N + 2)).val) := by
  simp only [Fin.val_last]
  omega

lemma not_adj_zero_last (N : ℕ) :
    ¬((0 : Fin (N + 3)).val + 1 = (Fin.last (N + 2)).val
      ∨ (Fin.last (N + 2)).val + 1 = (0 : Fin (N + 3)).val) := by
  simp only [Fin.val_zero, Fin.val_last]
  omega

lemma not_adj_last_zero (N : ℕ) :
    ¬((Fin.last (N + 2)).val + 1 = (0 : Fin (N + 3)).val
      ∨ (0 : Fin (N + 3)).val + 1 = (Fin.last (N + 2)).val) := by
  simp only [Fin.val_zero, Fin.val_last]
  omega

lemma g₁_dot_g₁ (N : ℕ) : g₁ N ⬝ᵥ g₁ N = 222 := by
  simp only [dotProduct]
  rw [Fin.sum_univ_add, Fin.sum_univ_eight]
  simp only [g₁_path, g₁_diam]
  norm_num

lemma g₂_dot_g₂ (N : ℕ) : g₂ N ⬝ᵥ g₂ N = 222 := by
  simp only [dotProduct]
  rw [Fin.sum_univ_add, Fin.sum_univ_eight]
  simp only [g₂_path, g₂_diam]
  norm_num

lemma g₁_dot_g₂ (N : ℕ) : g₁ N ⬝ᵥ g₂ N = 0 := by
  simp only [dotProduct]
  rw [Fin.sum_univ_add, Fin.sum_univ_eight]
  simp only [g₁_path, g₁_diam, g₂_path, g₂_diam]
  norm_num [zero_ne_last N]

lemma g₁_adj_g₁ (N : ℕ) : g₁ N ⬝ᵥ ((fam N).adjMatrix ℝ *ᵥ g₁ N) = 586 := by
  rw [adj_form]
  simp only [g₁_path, g₁_diam]
  rw [path_block_zero N 0 0 (not_adj_zero_zero N) 3 3]
  norm_num [(zero_ne_last N).symm]

lemma g₂_adj_g₂ (N : ℕ) : g₂ N ⬝ᵥ ((fam N).adjMatrix ℝ *ᵥ g₂ N) = 586 := by
  rw [adj_form]
  simp only [g₂_path, g₂_diam]
  rw [path_block_zero N (Fin.last (N + 2)) (Fin.last (N + 2)) (not_adj_last_last N) 3 3]
  norm_num [zero_ne_last N]

lemma g₁_adj_g₂ (N : ℕ) : g₁ N ⬝ᵥ ((fam N).adjMatrix ℝ *ᵥ g₂ N) = 0 := by
  rw [adj_form]
  simp only [g₁_path, g₁_diam, g₂_path, g₂_diam]
  rw [path_block_zero N 0 (Fin.last (N + 2)) (not_adj_zero_last N) 3 3]
  norm_num [zero_ne_last N, (zero_ne_last N).symm]

lemma g₂_adj_g₁ (N : ℕ) : g₂ N ⬝ᵥ ((fam N).adjMatrix ℝ *ᵥ g₁ N) = 0 := by
  rw [adj_form]
  simp only [g₁_path, g₁_diam, g₂_path, g₂_diam]
  rw [path_block_zero N (Fin.last (N + 2)) 0 (not_adj_last_zero N) 3 3]
  norm_num [zero_ne_last N, (zero_ne_last N).symm]

/-- `λ₂(D N) ≥ 293/111` for every `N`. -/
theorem lambda₂_fam_ge (N : ℕ) : 293 / 111 ≤ lambda₂ (fam N) (by omega) := by
  refine le_eigenvalues₀_one ((fam N).isHermitian_adjMatrix ℝ) _ (g₁ N) (g₂ N) ?_ ?_
    (g₁_adj_g₂ N) (g₂_adj_g₁ N) (g₁_dot_g₂ N) ?_ ?_
  · rw [g₁_dot_g₁, g₁_adj_g₁]; norm_num
  · rw [g₂_dot_g₂, g₂_adj_g₂]; norm_num
  · rw [g₁_dot_g₁]; norm_num
  · rw [g₂_dot_g₂]; norm_num

/-! ### Connectivity -/

/-- Every `D N` is connected. -/
theorem fam_connected (N : ℕ) : (fam N).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨Fin.castAdd 8 0, fun w => ?_⟩
  -- along the path
  have hpath : ∀ (m : ℕ) (hm : m < N + 3),
      (fam N).Reachable (Fin.castAdd 8 0) (Fin.castAdd 8 ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero =>
      intro hm
      exact Reachable.refl _
    | succ m ih =>
      intro hm
      have hadj : (fam N).Adj (Fin.castAdd 8 ⟨m, by omega⟩) (Fin.castAdd 8 ⟨m + 1, hm⟩) :=
        (adj_pp N _ _).mpr (Or.inl rfl)
      exact (ih (by omega)).trans hadj.reachable
  have rL : (fam N).Reachable (Fin.castAdd 8 0) (Fin.castAdd 8 (Fin.last (N + 2))) :=
    hpath (N + 2) (by omega)
  -- into the two diamonds
  have a0 : (fam N).Adj (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 0) :=
    (adj_pd N 0 0).mpr (Or.inl ⟨rfl, rfl⟩)
  have a4 : (fam N).Adj (Fin.castAdd 8 (Fin.last (N + 2))) (Fin.natAdd (N + 3) 4) :=
    (adj_pd N (Fin.last (N + 2)) 4).mpr (Or.inr ⟨rfl, rfl⟩)
  have d02 : (fam N).Adj (Fin.natAdd (N + 3) 0) (Fin.natAdd (N + 3) 2) :=
    (adj_dd N 0 2).mpr (by decide)
  have d03 : (fam N).Adj (Fin.natAdd (N + 3) 0) (Fin.natAdd (N + 3) 3) :=
    (adj_dd N 0 3).mpr (by decide)
  have d21 : (fam N).Adj (Fin.natAdd (N + 3) 2) (Fin.natAdd (N + 3) 1) :=
    (adj_dd N 2 1).mpr (by decide)
  have d46 : (fam N).Adj (Fin.natAdd (N + 3) 4) (Fin.natAdd (N + 3) 6) :=
    (adj_dd N 4 6).mpr (by decide)
  have d47 : (fam N).Adj (Fin.natAdd (N + 3) 4) (Fin.natAdd (N + 3) 7) :=
    (adj_dd N 4 7).mpr (by decide)
  have d65 : (fam N).Adj (Fin.natAdd (N + 3) 6) (Fin.natAdd (N + 3) 5) :=
    (adj_dd N 6 5).mpr (by decide)
  have r0 : (fam N).Reachable (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 0) := a0.reachable
  have r2 : (fam N).Reachable (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 2) := r0.trans d02.reachable
  have r3 : (fam N).Reachable (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 3) := r0.trans d03.reachable
  have r1 : (fam N).Reachable (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 1) := r2.trans d21.reachable
  have r4 : (fam N).Reachable (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 4) := rL.trans a4.reachable
  have r6 : (fam N).Reachable (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 6) := r4.trans d46.reachable
  have r7 : (fam N).Reachable (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 7) := r4.trans d47.reachable
  have r5 : (fam N).Reachable (Fin.castAdd 8 0) (Fin.natAdd (N + 3) 5) := r6.trans d65.reachable
  refine Fin.addCases (fun i => ?_) (fun a => ?_) w
  · exact hpath i.val i.isLt
  · fin_cases a
    · exact r0
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
    · exact r7

/-! ### The counterexamples -/

/-- **Every `D N` violates `λ₂ ≤ μ₁ − 2`.** It is connected, and `μ₁(D N) − 2 < λ₂(D N)`. -/
theorem family_counterexample (N : ℕ) :
    (fam N).Connected ∧ mu₁ (fam N) (by omega) - 2 < lambda₂ (fam N) (by omega) := by
  refine ⟨fam_connected N, ?_⟩
  have h1 := mu₁_fam_le N
  have h2 := lambda₂_fam_ge N
  linarith

/-- The same, with the uniform gap `13/888`. -/
theorem family_gap (N : ℕ) :
    13 / 888 ≤ lambda₂ (fam N) (by omega) - (mu₁ (fam N) (by omega) - 2) := by
  have h1 := mu₁_fam_le N
  have h2 := lambda₂_fam_ge N
  linarith

/-- **A counterexample on every number of vertices `n ≥ 11`**: there is a connected simple graph
on `Fin n` with `μ₁ − 2 < λ₂`. -/
theorem exists_counterexample (n : ℕ) (hn : 11 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ mu₁ G (by omega) - 2 < lambda₂ G (by omega) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 + 8 := ⟨n - 11, by omega⟩
  exact ⟨fam N, inferInstance, family_counterexample N⟩

/-- **Conjecture 2 fails on `n` vertices for every `n ≥ 11`.** -/
theorem conjecture_two_false_of_card (n : ℕ) (hn : 11 ≤ n) :
    ¬ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → lambda₂ G (by omega) ≤ mu₁ G (by omega) - 2 := by
  intro hconj
  obtain ⟨G, inst, hc, hlt⟩ := exists_counterexample n hn
  have h := hconj G hc
  linarith

/-! ### The first member of the family is `G₁₁` -/

/-- Renaming of the vertices of `G₁₁` (`Conj2.G11`: diamonds on `0, …, 7`, path `8, 9, 10`) into
those of `D 0` (path `0, 1, 2`, diamonds on `3, …, 10`). -/
def toFamZero : Fin 11 → Fin (0 + 3 + 8) := ![3, 4, 5, 6, 7, 8, 9, 10, 0, 1, 2]

lemma toFamZero_injective : Function.Injective toFamZero := by decide

/-- `D 0` is `G₁₁` with its vertices renamed by `toFamZero`. -/
theorem fam_zero_eq_G11 :
    ∀ i j : Fin 11, G11.Adj i j ↔ (fam 0).Adj (toFamZero i) (toFamZero j) := by
  decide

end Family
end Conj2
