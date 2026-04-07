import SetTheory.FirstAxioms.Axioms.Index

noncomputable def subset_definition (F: Set) : Set :=
  Classical.choose (power_set_axiom F)

notation "P("F")" => subset_definition F

theorem power_set (F x: Set) : x∈P(F) ↔ x⊆F := by
  exact Classical.choose_spec (power_set_axiom F) x
