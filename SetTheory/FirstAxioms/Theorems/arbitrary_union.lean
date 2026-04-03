import SetTheory.FirstAxioms.Axioms.Index

noncomputable def arbitrary_union_definition (F: Set): Set :=
  Classical.choose (union_axiom F)
prefix:max "⋃" => arbitrary_union_definition

theorem arbitrary_union (F : Set) (x : Set) :
  x ∈ ⋃F ↔ ∃ A : Set, A ∈ F ∧ x ∈ A := by
  exact Classical.choose_spec (union_axiom F) x
