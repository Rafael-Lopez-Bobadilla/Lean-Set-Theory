import SetTheory.FirstAxioms.Axioms.Index

noncomputable def arbitrary_union_definition (F: Set): Set :=
  Classical.choose (union_axiom F)
prefix:max "⋃" => arbitrary_union_definition

theorem arbitrary_union (F x: Set) :
  x ∈ ⋃F ↔ ∃ A : Set, A ∈ F ∧ x ∈ A := by
  exact Classical.choose_spec (union_axiom F) x

theorem arbitrary_union_equiv (A B: Set):
A=B → ⋃A=⋃B := by
  intro h1
  apply (extensionality ⋃A ⋃B).mpr
  intro x
  constructor
  intro h2
  have ⟨C,h3,h4⟩ := (arbitrary_union A x).mp h2
  have h5: C∈B := ((extensionality A B).mp h1 C).mp h3
  exact (arbitrary_union B x).mpr ⟨C,h5,h4⟩
  intro h3
  have ⟨C,h4,h5⟩ := (arbitrary_union B x).mp h3
  have h6: C∈A := ((extensionality A B).mp h1 C).mpr h4
  exact (arbitrary_union A x).mpr ⟨C,h6,h5⟩
