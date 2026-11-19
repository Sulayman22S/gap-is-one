import Conj2

/-! Audit file: prints the main statements and the axioms they depend on.
Run with `lake env lean Check.lean`. Expected axioms: `propext`, `Classical.choice`, `Quot.sound`. -/

-- the best constant
#check @Conj2.best_constant
#check @Conj2.lambda₂_le_mu₁_sub_one
#check @Conj2.Sharp.no_constant_above_one
#check @Conj2.Sharp.exists_gap_lt
#check @Conj2.Sharp.exists_gap_le
#check @Conj2.Sharp.conjecture_sqrt_two_false
#check @Conj2.Sharp.conjecture_fourth_root_two_false
#print axioms Conj2.best_constant
#print axioms Conj2.lambda₂_le_mu₁_sub_one
#print axioms Conj2.Sharp.no_constant_above_one
#print axioms Conj2.Sharp.exists_gap_lt
#print axioms Conj2.Sharp.exists_gap_le
#print axioms Conj2.Sharp.conjecture_sqrt_two_false
#print axioms Conj2.Sharp.conjecture_fourth_root_two_false

-- the single counterexample `G₁₁`
#check @Conj2.conjecture_two_false
#check @Conj2.counterexample
#check @Conj2.mu₁_G11_le
#check @Conj2.lambda₂_G11_ge
#check @Conj2.counterexample_gap
#check @Conj2.adj_iff_edges
#check @Conj2.G11_connected
#print axioms Conj2.conjecture_two_false
#print axioms Conj2.counterexample
#print axioms Conj2.counterexample_gap
#print axioms Conj2.adj_iff_edges

-- the infinite family `D N`
#check @Conj2.Family.family_counterexample
#check @Conj2.Family.family_gap
#check @Conj2.Family.exists_counterexample
#check @Conj2.Family.conjecture_two_false_of_card
#check @Conj2.Family.mu₁_fam_le
#check @Conj2.Family.lambda₂_fam_ge
#check @Conj2.Family.fam_connected
#check @Conj2.Family.adj_pp
#check @Conj2.Family.adj_pd
#check @Conj2.Family.adj_dd
#check @Conj2.Family.fam_zero_eq_G11
#check @Conj2.Family.toFamZero_injective
#print axioms Conj2.Family.family_counterexample
#print axioms Conj2.Family.family_gap
#print axioms Conj2.Family.exists_counterexample
#print axioms Conj2.Family.conjecture_two_false_of_card
#print axioms Conj2.Family.fam_zero_eq_G11
