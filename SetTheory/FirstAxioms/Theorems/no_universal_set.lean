import SetTheory.FirstAxioms.Axioms.Index

theorem no_universal_set : ¬(∃A: Set, ∀x: Set, x∈A) := by
  intro A_exists
  /-apply Exists.elim A_exists
  intro A every_set_is_in_A
  -/
  have ⟨A, every_set_is_in_A⟩ := A_exists
  have B_exists := subset_axiom A (fun x => x ∉ x)
  have ⟨B, in_B_if_member_of_itself⟩ := B_exists
  have B_in_B_iff := in_B_if_member_of_itself B
  have B_in_A := every_set_is_in_A B
  have B_not_in_B : B∉B := by
    intro B_in_B
    have B_in_A_not_inB := B_in_B_iff.mp B_in_B
    have B_not_in_B := B_in_A_not_inB.right
    exact B_not_in_B B_in_B
  have B_in_B := B_in_B_iff.mpr ⟨B_in_A, B_not_in_B⟩
  exact B_not_in_B B_in_B
