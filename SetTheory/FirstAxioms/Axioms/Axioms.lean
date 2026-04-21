import SetTheory.FirstAxioms.Axioms.Definitions

axiom extensionality (A B : Set) :
  A=B ↔ (∀ x : Set, x ∈ A ↔ x ∈ B)

axiom empty : Set
notation "∅" => empty
axiom empty_axiom (x : Set ) : x ∉ ∅

axiom subset_axiom (A : Set) (P : Set → Prop) :
  ∃ B : Set, ∀ d : Set, d ∈ B ↔ (d ∈ A ∧ P d)

axiom pairing_axiom (A B: Set) : ∃Pair: Set, ∀x: Set, x∈Pair ↔ x=A ∨ x=B

axiom union_axiom (F: Set) : ∃Union: Set, ∀x: Set, x∈Union ↔ ∃A: Set, A∈F ∧ x∈A

axiom power_set_axiom (F: Set) : ∃Power: Set, ∀x: Set, x∈Power ↔ x⊆F
