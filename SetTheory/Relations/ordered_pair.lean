import SetTheory.FirstAxioms.Index

theorem ordered_pair_exists (a b: Set) :
  ∃ordered: Set, ∀x: Set, x∈ordered ↔ x={a,a} ∨ x={a,b} := by
  have ⟨ordered, h1⟩ := pairing_axiom {a,a} {a,b}
  apply Exists.intro ordered
  exact h1

noncomputable def ordered_pair_operation (a b: Set) : Set :=
  Classical.choose (ordered_pair_exists a b)
notation (priority := high) "("a","b")" => ordered_pair_operation a b

theorem ordered_pair (a b x: Set) : x∈(a,b) ↔ x={a,a} ∨ x={a,b} := by
  exact Classical.choose_spec (ordered_pair_exists a b) x
