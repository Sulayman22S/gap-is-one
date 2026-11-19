import Conj2.PathLemmas
import Conj2.SharpLemmas
import Conj2.Transfer

/-!
# The constant `1` in `λ₂ ≤ μ₁ − 1` is best possible

For `m, t : ℕ` let `T m t` (`Conj2.Sharp.sg m t`) be the following graph.

* A *cluster* is a complete split graph: a clique on `m` vertices together with `t + 1` further
  vertices, each joined to every clique vertex and to nothing else.
* `T m t` consists of two clusters and one *connector* vertex, which is joined to one
  non-clique vertex of each cluster (the *attachment* vertices).

Its maximum degree is `Δ = m + t`, and with `s = t + 1`:

* `μ₁ ≤ m + s + 3/s = Δ + 1 + 3/s` (`lap_quadForm_le`): the Laplacian form of a cluster, plus
  twice the square at its attachment vertex, is at most `(m + s + 3/s)‖z‖²` (`cluster_le`);
* `λ₂ ≥ (m(m−1) + 2ms)/(m+s)` (`le_lambda₂`): the indicator vectors of the two clusters, whose
  Rayleigh quotient is the average degree of a cluster.

Hence `μ₁ − λ₂ ≤ 1 + 3/s + (s² − s)/(m + s)`, which tends to `1` for `s → ∞`, `m = s³`.

The graph is described on the structured vertex set `Vx m t = Option (Fin 2 × (Fin m ⊕ Fin (t+1)))`
and moved to `Fin n` with `Conj2.Transfer`.
-/

open Matrix SimpleGraph Finset

namespace Conj2
namespace Sharp

/-- Vertices of a cluster: a clique `Fin m` (`Sum.inl`) and `t + 1` further vertices
(`Sum.inr`), of which `Sum.inr 0` is the attachment vertex. -/
abbrev Cl (m t : ℕ) : Type := Fin m ⊕ Fin (t + 1)

/-- Vertices of `T m t`: the connector `none`, and two clusters `some (i, x)`, `i : Fin 2`. -/
abbrev Vx (m t : ℕ) : Type := Option (Fin 2 × Cl m t)

/-! ### A cluster -/

/-- Adjacency inside a cluster: the complete split graph. -/
def crel (m t : ℕ) : Cl m t → Cl m t → Prop
  | .inl c, .inl c' => c ≠ c'
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr _, .inr _ => False

instance crelDecidable (m t : ℕ) : DecidableRel (crel m t) := fun x y =>
  match x, y with
  | .inl c, .inl c' => inferInstanceAs (Decidable (c ≠ c'))
  | .inl _, .inr _ => inferInstanceAs (Decidable True)
  | .inr _, .inl _ => inferInstanceAs (Decidable True)
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

lemma crel_ll (m t : ℕ) (c c' : Fin m) : crel m t (.inl c) (.inl c') ↔ c ≠ c' := Iff.rfl

lemma crel_lr (m t : ℕ) (c : Fin m) (v : Fin (t + 1)) : crel m t (.inl c) (.inr v) ↔ True :=
  Iff.rfl

lemma crel_rl (m t : ℕ) (v : Fin (t + 1)) (c : Fin m) : crel m t (.inr v) (.inl c) ↔ True :=
  Iff.rfl

lemma crel_rr (m t : ℕ) (v v' : Fin (t + 1)) : crel m t (.inr v) (.inr v') ↔ False := Iff.rfl

lemma crel_symm (m t : ℕ) : ∀ x y, crel m t x y → crel m t y x := by
  rintro (c | v) (c' | v') h
  · exact Ne.symm h
  · exact trivial
  · exact trivial
  · exact h

lemma crel_irrefl (m t : ℕ) : ∀ x, ¬crel m t x x := by
  rintro (c | v) h
  · exact h rfl
  · exact h

/-- A sum over ordered adjacent pairs of a cluster: pairs of distinct clique vertices, and
clique–non-clique pairs in both directions. -/
lemma sum_crel (m t : ℕ) (K : Cl m t → Cl m t → ℝ) :
    ∑ x, ∑ y, (if crel m t x y then K x y else 0)
      = (∑ c : Fin m, ∑ c' : Fin m, if c ≠ c' then K (.inl c) (.inl c') else 0)
        + ∑ c : Fin m, ∑ v : Fin (t + 1), K (.inl c) (.inr v)
        + ∑ v : Fin (t + 1), ∑ c : Fin m, K (.inr v) (.inl c) := by
  simp only [Fintype.sum_sum_type, crel_ll, crel_lr, crel_rl, crel_rr, ite_true, ite_false,
    sum_const_zero, add_zero, sum_add_distrib]
  ring

/-- The number of ordered adjacent pairs of a cluster. -/
lemma crel_count (m t : ℕ) :
    ∑ x, ∑ y, (if crel m t x y then (1 : ℝ) else 0)
      = (m : ℝ) * (m - 1) + 2 * m * (t + 1) := by
  rw [sum_crel, sum_sum_ne]
  simp
  ring

/-- The Laplacian double sum of a cluster, in terms of the sums over the clique and over the
other vertices. -/
lemma cluster_lap_sum (m t : ℕ) (z : Cl m t → ℝ) :
    ∑ x, ∑ y, (if crel m t x y then (z x - z y) ^ 2 else 0)
      = 2 * (((m : ℝ) * ∑ c, z (.inl c) ^ 2 - (∑ c, z (.inl c)) ^ 2)
          + (((t : ℝ) + 1) * ∑ c, z (.inl c) ^ 2 - 2 * (∑ c, z (.inl c)) * (∑ v, z (.inr v))
              + (m : ℝ) * ∑ v, z (.inr v) ^ 2)) := by
  rw [sum_crel, sum_sum_ne, sum_sum_sq_sub (fun c => z (.inl c)),
    sum_sum_sq_sub_two (fun c => z (.inl c)) (fun v => z (.inr v)),
    sum_sum_sq_sub_two (fun v => z (.inr v)) (fun c => z (.inl c))]
  simp
  ring

/-- **The cluster inequality.** The Laplacian form of a cluster plus twice the square at its
attachment vertex is at most `(m + s + 3/s) ‖z‖²`, where `s = t + 1`. -/
lemma cluster_le (m t : ℕ) (ht : 1 ≤ t) (z : Cl m t → ℝ) :
    (∑ x, ∑ y, (if crel m t x y then (z x - z y) ^ 2 else 0)) / 2 + 2 * z (.inr 0) ^ 2
      ≤ ((m : ℝ) + ((t : ℝ) + 1) + 3 / ((t : ℝ) + 1)) * ∑ x, z x ^ 2 := by
  rw [cluster_lap_sum, Fintype.sum_sum_type,
    Fin.sum_univ_succ (fun v => z (.inr v) ^ 2), Fin.sum_univ_succ (fun v => z (.inr v))]
  have hCS := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin t)))
    (f := fun v => z (.inr v.succ))
  simp only [card_univ, Fintype.card_fin] at hCS
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hη : 3 / ((t : ℝ) + 1) * ((t : ℝ) + 1) = 3 := by
    field_simp
  have h := cluster_core (m : ℝ) ((t : ℝ) + 1) (3 / ((t : ℝ) + 1)) (∑ c, z (.inl c) ^ 2)
    (∑ c, z (.inl c)) (z (.inr 0)) (∑ v : Fin t, z (.inr v.succ))
    (∑ v : Fin t, z (.inr v.succ) ^ 2) (by linarith) hη
    (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
    (by simpa using hCS)
  linarith

/-! ### The graph `T m t` -/

/-- Adjacency of `T m t`: the connector is joined to the attachment vertex `Sum.inr 0` of each
cluster; inside a cluster the adjacency is `crel`; there are no other edges. -/
def srel (m t : ℕ) : Vx m t → Vx m t → Prop
  | none, none => False
  | none, some (_, x) => x = .inr 0
  | some (_, x), none => x = .inr 0
  | some (i, x), some (j, y) => i = j ∧ crel m t x y

instance srelDecidable (m t : ℕ) : DecidableRel (srel m t) := fun u v =>
  match u, v with
  | none, none => inferInstanceAs (Decidable False)
  | none, some (_, x) => inferInstanceAs (Decidable (x = .inr 0))
  | some (_, x), none => inferInstanceAs (Decidable (x = .inr 0))
  | some (i, x), some (j, y) => inferInstanceAs (Decidable (i = j ∧ crel m t x y))

lemma srel_symm (m t : ℕ) : ∀ u v, srel m t u v → srel m t v u := by
  rintro (_ | ⟨i, x⟩) (_ | ⟨j, y⟩) h
  · exact h
  · exact h
  · exact h
  · exact ⟨h.1.symm, crel_symm m t _ _ h.2⟩

lemma srel_irrefl (m t : ℕ) : ∀ u, ¬srel m t u u := by
  rintro (_ | ⟨i, x⟩) h
  · exact h
  · exact crel_irrefl m t x h.2

/-- `T m t`: two complete split graphs `K_m ∨ (t+1 isolated vertices)` and a connector vertex
joined to one non-clique vertex of each. It has `2 (m + t + 1) + 1` vertices. -/
def sg (m t : ℕ) : SimpleGraph (Vx m t) where
  Adj := srel m t
  symm := ⟨srel_symm m t⟩
  loopless := ⟨srel_irrefl m t⟩

instance (m t : ℕ) : DecidableRel (sg m t).Adj := srelDecidable m t

lemma adj_none_none (m t : ℕ) : (sg m t).Adj none none ↔ False := Iff.rfl

lemma adj_none_some (m t : ℕ) (i : Fin 2) (x : Cl m t) :
    (sg m t).Adj none (some (i, x)) ↔ x = .inr 0 := Iff.rfl

lemma adj_some_none (m t : ℕ) (i : Fin 2) (x : Cl m t) :
    (sg m t).Adj (some (i, x)) none ↔ x = .inr 0 := Iff.rfl

lemma adj_some_some (m t : ℕ) (i j : Fin 2) (x y : Cl m t) :
    (sg m t).Adj (some (i, x)) (some (j, y)) ↔ i = j ∧ crel m t x y := Iff.rfl

/-- A sum over ordered adjacent pairs of `T m t`: the two connector edges in both directions,
and the two clusters. -/
lemma sum_srel (m t : ℕ) (F : Vx m t → Vx m t → ℝ) :
    ∑ u, ∑ v, (if (sg m t).Adj u v then F u v else 0)
      = (F none (some (0, .inr 0)) + F none (some (1, .inr 0)))
        + (F (some (0, .inr 0)) none + F (some (1, .inr 0)) none)
        + ((∑ x, ∑ y, if crel m t x y then F (some (0, x)) (some (0, y)) else 0)
          + ∑ x, ∑ y, if crel m t x y then F (some (1, x)) (some (1, y)) else 0) := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_two, adj_none_none,
    adj_none_some, adj_some_none, adj_some_some]
  simp [sum_add_distrib]
  ring

/-- The Laplacian quadratic form of `T m t`. -/
lemma lap_form (m t : ℕ) (z : Vx m t → ℝ) :
    z ⬝ᵥ ((sg m t).lapMatrix ℝ *ᵥ z)
      = (z none - z (some (0, .inr 0))) ^ 2 + (z none - z (some (1, .inr 0))) ^ 2
        + (∑ x, ∑ y, if crel m t x y then (z (some (0, x)) - z (some (0, y))) ^ 2 else 0) / 2
        + (∑ x, ∑ y, if crel m t x y then (z (some (1, x)) - z (some (1, y))) ^ 2 else 0) / 2 := by
  rw [← Matrix.toLinearMap₂'_apply', lapMatrix_toLinearMap₂', sum_srel]
  ring

/-- The squared norm on the vertex set of `T m t`. -/
lemma dot_self (m t : ℕ) (z : Vx m t → ℝ) :
    z ⬝ᵥ z = z none ^ 2 + ∑ x, z (some (0, x)) ^ 2 + ∑ x, z (some (1, x)) ^ 2 := by
  simp only [dotProduct, ← sq, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- `zᵀ L z ≤ (m + s + 3/s) ‖z‖²` for the Laplacian of `T m t`, where `s = t + 1`. -/
lemma lap_quadForm_le (m t : ℕ) (hm : 2 ≤ m) (ht : 1 ≤ t) (z : Vx m t → ℝ) :
    z ⬝ᵥ ((sg m t).lapMatrix ℝ *ᵥ z)
      ≤ ((m : ℝ) + ((t : ℝ) + 1) + 3 / ((t : ℝ) + 1)) * (z ⬝ᵥ z) := by
  rw [lap_form, dot_self]
  have h0 := cluster_le m t ht (fun x => z (some (0, x)))
  have h1 := cluster_le m t ht (fun x => z (some (1, x)))
  have e0 := sq_sub_le_two (z none) (z (some (0, .inr 0)))
  have e1 := sq_sub_le_two (z none) (z (some (1, .inr 0)))
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hfrac : (0 : ℝ) ≤ 3 / ((t : ℝ) + 1) := by positivity
  have hM : 0 ≤ ((m : ℝ) + ((t : ℝ) + 1) + 3 / ((t : ℝ) + 1) - 4) * z none ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith

/-! ### The adjacency bound -/

/-- The indicator vector of cluster `i`. -/
def ind (m t : ℕ) (i : Fin 2) : Vx m t → ℝ
  | none => 0
  | some (j, _) => if j = i then 1 else 0

lemma ind_none (m t : ℕ) (i : Fin 2) : ind m t i none = 0 := rfl

lemma ind_some (m t : ℕ) (i j : Fin 2) (x : Cl m t) :
    ind m t i (some (j, x)) = if j = i then 1 else 0 := rfl

lemma ind_zero_dot (m t : ℕ) : ind m t 0 ⬝ᵥ ind m t 0 = (m : ℝ) + ((t : ℝ) + 1) := by
  simp [dotProduct, Fintype.sum_option, Fintype.sum_prod_type, ind_none, ind_some]

lemma ind_one_dot (m t : ℕ) : ind m t 1 ⬝ᵥ ind m t 1 = (m : ℝ) + ((t : ℝ) + 1) := by
  simp [dotProduct, Fintype.sum_option, Fintype.sum_prod_type, ind_none, ind_some]

lemma ind_zero_dot_one (m t : ℕ) : ind m t 0 ⬝ᵥ ind m t 1 = 0 := by
  simp [dotProduct, Fintype.sum_option, Fintype.sum_prod_type, ind_none, ind_some]

/-- The adjacency form on the cluster indicators: the number of ordered adjacent pairs of a
cluster on the diagonal, zero off the diagonal (there is no edge between the clusters). -/
lemma ind_adj_zero_zero (m t : ℕ) :
    ind m t 0 ⬝ᵥ ((sg m t).adjMatrix ℝ *ᵥ ind m t 0)
      = (m : ℝ) * (m - 1) + 2 * m * (t + 1) := by
  rw [dotProduct_mulVec_adjMatrix, sum_srel]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [ind_none, ind_some, ite_true, h10, ite_false, mul_one, mul_zero,
    ite_self, sum_const_zero, add_zero, zero_add, crel_count]

lemma ind_adj_one_one (m t : ℕ) :
    ind m t 1 ⬝ᵥ ((sg m t).adjMatrix ℝ *ᵥ ind m t 1)
      = (m : ℝ) * (m - 1) + 2 * m * (t + 1) := by
  rw [dotProduct_mulVec_adjMatrix, sum_srel]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp only [ind_none, ind_some, ite_true, h01, ite_false, mul_one, mul_zero,
    ite_self, sum_const_zero, add_zero, zero_add, crel_count]

lemma ind_adj_zero_one (m t : ℕ) :
    ind m t 0 ⬝ᵥ ((sg m t).adjMatrix ℝ *ᵥ ind m t 1) = 0 := by
  rw [dotProduct_mulVec_adjMatrix, sum_srel]
  simp [ind_none, ind_some]

lemma ind_adj_one_zero (m t : ℕ) :
    ind m t 1 ⬝ᵥ ((sg m t).adjMatrix ℝ *ᵥ ind m t 0) = 0 := by
  rw [dotProduct_mulVec_adjMatrix, sum_srel]
  simp [ind_none, ind_some]

/-! ### Connectivity -/

/-- `T m t` is connected as soon as the cliques are non-empty. -/
theorem sg_connected (m t : ℕ) (hm : 1 ≤ m) : (sg m t).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨none, fun w => ?_⟩
  have ha : ∀ i : Fin 2, (sg m t).Reachable none (some (i, .inr 0)) := fun i =>
    Adj.reachable ((adj_none_some m t i _).mpr rfl)
  have hc : ∀ (i : Fin 2) (c : Fin m), (sg m t).Reachable none (some (i, .inl c)) := fun i c =>
    (ha i).trans
      (Adj.reachable ((adj_some_some m t i i _ _).mpr ⟨rfl, (crel_rl m t 0 c).mpr trivial⟩))
  have hv : ∀ (i : Fin 2) (v : Fin (t + 1)), (sg m t).Reachable none (some (i, .inr v)) :=
    fun i v => (hc i ⟨0, hm⟩).trans
      (Adj.reachable ((adj_some_some m t i i _ _).mpr ⟨rfl, (crel_lr m t ⟨0, hm⟩ v).mpr trivial⟩))
  rcases w with _ | ⟨i, c | v⟩
  · exact Reachable.refl _
  · exact hc i c
  · exact hv i v

/-! ### The gap `μ₁ − λ₂` -/

/-- The number of vertices of `T m t`. -/
lemma card_Vx (m t : ℕ) : Fintype.card (Vx m t) = 2 * (m + (t + 1)) + 1 := by
  simp [Vx, Cl]

/-- **The gap bound for `T m t`**, stated for the graph with numbered vertices: with `s = t + 1`,
`μ₁ − λ₂ ≤ 1 + 3/s + (s² − s)/(m + s)`. -/
theorem exists_gap_le (m t : ℕ) (hm : 2 ≤ m) (ht : 1 ≤ t) :
    ∃ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧
        mu₁ G hn - lambda₂ G hn
          ≤ 1 + 3 / ((t : ℝ) + 1)
            + (((t : ℝ) + 1) ^ 2 - ((t : ℝ) + 1)) / ((m : ℝ) + ((t : ℝ) + 1)) := by
  have hn : 2 ≤ Fintype.card (Vx m t) := by
    rw [card_Vx]
    omega
  let e : Fin (Fintype.card (Vx m t)) ≃ Vx m t := (Fintype.equivFin (Vx m t)).symm
  refine ⟨Fintype.card (Vx m t), hn, (sg m t).comap e, inferInstance,
    connected_comap (sg m t) e (sg_connected m t (by omega)), ?_⟩
  have hpos : (0 : ℝ) < (m : ℝ) + ((t : ℝ) + 1) := by positivity
  have hD : (m : ℝ) + ((t : ℝ) + 1) ≠ 0 := hpos.ne'
  have h1 : mu₁ ((sg m t).comap e) hn ≤ (m : ℝ) + ((t : ℝ) + 1) + 3 / ((t : ℝ) + 1) :=
    mu₁_comap_le (sg m t) e hn (lap_quadForm_le m t hm ht)
  have h2 : ((m : ℝ) * (m - 1) + 2 * m * (t + 1)) / ((m : ℝ) + ((t : ℝ) + 1))
      ≤ lambda₂ ((sg m t).comap e) hn := by
    refine le_lambda₂_comap (sg m t) e hn (ind m t 0) (ind m t 1) ?_ ?_
      (ind_adj_zero_one m t) (ind_adj_one_zero m t) (ind_zero_dot_one m t) ?_ ?_
    · rw [ind_zero_dot, ind_adj_zero_zero]
      exact le_of_eq (by field_simp)
    · rw [ind_one_dot, ind_adj_one_one]
      exact le_of_eq (by field_simp)
    · rw [ind_zero_dot]
      exact hpos
    · rw [ind_one_dot]
      exact hpos
  have key : (m : ℝ) + ((t : ℝ) + 1)
      - ((m : ℝ) * (m - 1) + 2 * m * (t + 1)) / ((m : ℝ) + ((t : ℝ) + 1))
      = 1 + (((t : ℝ) + 1) ^ 2 - ((t : ℝ) + 1)) / ((m : ℝ) + ((t : ℝ) + 1)) := by
    field_simp
    ring
  linarith

/-- **The gap `μ₁ − λ₂` can be made arbitrarily close to `1`**: for every `ε > 0` there is a
connected graph with `μ₁ − λ₂ < 1 + ε`. -/
theorem exists_gap_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.Connected ∧ mu₁ G hn - lambda₂ G hn < 1 + ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
  have hm : 2 ≤ (k + 2) ^ 3 :=
    le_trans (by omega : 2 ≤ k + 2) (Nat.le_self_pow (by norm_num) (k + 2))
  obtain ⟨n, hn, G, inst, hc, hgap⟩ := exists_gap_le ((k + 2) ^ 3) (k + 1) hm (by omega)
  refine ⟨n, hn, G, inst, hc, lt_of_le_of_lt hgap ?_⟩
  have hS : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by
    push_cast
    ring
  have hm' : (((k + 2) ^ 3 : ℕ) : ℝ) = ((k : ℝ) + 2) ^ 3 := by
    push_cast
    ring
  rw [hS, hm']
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hSpos : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  have h4 : 4 < ε * ((k : ℝ) + 2) := by
    have h := mul_lt_mul_of_pos_left (lt_trans hk (by linarith : (k : ℝ) < (k : ℝ) + 2)) hε
    have e4 : ε * (4 / ε) = 4 := by field_simp
    linarith
  have hDpos : (0 : ℝ) < ((k : ℝ) + 2) ^ 3 + ((k : ℝ) + 2) := by positivity
  have e1 : ε - (3 / ((k : ℝ) + 2)
        + (((k : ℝ) + 2) ^ 2 - ((k : ℝ) + 2)) / (((k : ℝ) + 2) ^ 3 + ((k : ℝ) + 2)))
      = (ε * (((k : ℝ) + 2) * (((k : ℝ) + 2) ^ 3 + ((k : ℝ) + 2)))
          - (4 * ((k : ℝ) + 2) ^ 3 - ((k : ℝ) + 2) ^ 2 + 3 * ((k : ℝ) + 2)))
        / (((k : ℝ) + 2) * (((k : ℝ) + 2) ^ 3 + ((k : ℝ) + 2))) := by
    field_simp
    ring
  have hnum : 0 < ε * (((k : ℝ) + 2) * (((k : ℝ) + 2) ^ 3 + ((k : ℝ) + 2)))
      - (4 * ((k : ℝ) + 2) ^ 3 - ((k : ℝ) + 2) ^ 2 + 3 * ((k : ℝ) + 2)) := by
    have a := mul_lt_mul_of_pos_right h4 (pow_pos hSpos 3)
    have b := mul_lt_mul_of_pos_right h4 hSpos
    nlinarith [sq_nonneg ((k : ℝ) + 2)]
  have hpos := div_pos hnum (mul_pos hSpos hDpos)
  rw [← e1] at hpos
  linarith

/-! ### Consequences -/

/-- **No constant larger than `1` works**: for every `c > 1`, it is false that
`λ₂(G) ≤ μ₁(G) − c` for all connected simple graphs `G` on `n ≥ 2` vertices. -/
theorem no_constant_above_one (c : ℝ) (hc : 1 < c) :
    ¬ ∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → lambda₂ G hn ≤ mu₁ G hn - c := by
  intro h
  obtain ⟨n, hn, G, inst, hconn, hgap⟩ := exists_gap_lt (c - 1) (by linarith)
  have h' := h n hn G hconn
  linarith

/-- The inequality `λ₂ ≤ μ₁ − √2` (conjecture #121082 of the Duhamel–Cazenave corpus) is
false. -/
theorem conjecture_sqrt_two_false :
    ¬ ∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → lambda₂ G hn ≤ mu₁ G hn - Real.sqrt 2 :=
  no_constant_above_one _ Real.one_lt_sqrt_two

/-- The inequality `λ₂ ≤ μ₁ − √√2` (conjecture #717992 of the Duhamel–Cazenave corpus) is
false. -/
theorem conjecture_fourth_root_two_false :
    ¬ ∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → lambda₂ G hn ≤ mu₁ G hn - Real.sqrt (Real.sqrt 2) :=
  no_constant_above_one _
    ((Real.lt_sqrt (by norm_num)).mpr (by simpa using Real.one_lt_sqrt_two))

end Sharp
end Conj2
