import Conj2

/-! Negative controls for the sharp-constant part. Every `example` marked FALSE states something
untrue and must be REJECTED; the ones marked TRUE must be accepted. Expected: exactly 5 errors. -/

open Matrix SimpleGraph Finset Conj2 Conj2.Sharp

-- TRUE: the constant 3/2 fails.
example : ¬ ∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → lambda₂ G hn ≤ mu₁ G hn - 3 / 2 :=
  no_constant_above_one _ (by norm_num)

-- TRUE: a cluster with clique size 3 and 2 further vertices has 18 ordered adjacent pairs.
example : ∑ x, ∑ y, (if crel 3 1 x y then (1 : ℝ) else 0) = 18 := by
  rw [crel_count]
  norm_num

-- FALSE 1: the same count claimed to be 20.
example : ∑ x, ∑ y, (if crel 3 1 x y then (1 : ℝ) else 0) = 20 := by
  rw [crel_count]
  norm_num

-- FALSE 2: the constant 1 itself claimed to fail.
example : ¬ ∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → lambda₂ G hn ≤ mu₁ G hn - 1 :=
  no_constant_above_one _ (by norm_num)

-- FALSE 3: Conjecture 2 claimed to be true, via the best-constant theorem.
example : ∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → lambda₂ G hn ≤ mu₁ G hn - 2 :=
  (best_constant 2).mpr (by norm_num)

-- FALSE 4: the connector adjacent to a clique vertex.
example : (sg 3 1).Adj none (some (0, Sum.inl 0)) :=
  (adj_none_some 3 1 0 _).mpr rfl

-- FALSE 5: the squared-difference identity with a wrong coefficient.
example (f : Fin 3 → ℝ) :
    ∑ i, ∑ j, (f i - f j) ^ 2 = 3 * (3 : ℝ) * ∑ i, f i ^ 2 - 2 * (∑ i, f i) ^ 2 := by
  rw [sum_sum_sq_sub]
  simp
