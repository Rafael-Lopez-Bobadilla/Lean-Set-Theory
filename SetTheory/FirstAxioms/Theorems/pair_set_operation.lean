import SetTheory.FirstAxioms.Axioms.Index

noncomputable def pair_set_definition (a b: Set): Set :=
  Classical.choose (pairing_axiom a b)
notation (priority := high) "{" a "," b "}" => pair_set_definition a b

theorem pair_set (a b x: Set) :
  x ∈ {a, b} ↔ x=a ∨ x=b := by
  exact Classical.choose_spec (pairing_axiom a b) x
