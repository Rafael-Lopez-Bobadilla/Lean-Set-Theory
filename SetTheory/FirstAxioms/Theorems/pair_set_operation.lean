import SetTheory.FirstAxioms.Axioms.Index

noncomputable def pair_set_definition (a b: Set): Set :=
  Classical.choose (pairing_axiom a b)
notation (priority := high) "{" a "," b "}" => pair_set_definition a b

theorem pair_set (a b x: Set) :
  x ∈ {a, b} ↔ x=a ∨ x=b := by
  exact Classical.choose_spec (pairing_axiom a b) x

theorem singleton_exists (a: Set):
∃s: Set, ∀x: Set, x∈s ↔ x=a := by
  have ⟨pair,h1⟩ := pairing_axiom a a
  apply Exists.intro pair
  intro x
  constructor
  intro h2
  have h3 := (h1 x).mp h2
  cases h3 with
  |inl h4 =>
    exact h4
  |inr h5 =>
    exact h5
  intro h3
  exact (h1 x).mpr (Or.inl h3)

noncomputable def singleton_op (a: Set) : Set :=
  Classical.choose (singleton_exists a)
notation (priority := high) "{"a:max"}" => singleton_op a

theorem singleton (a: Set) :
∀x: Set, x∈{a} ↔ x=a := by
  exact Classical.choose_spec (singleton_exists a)
