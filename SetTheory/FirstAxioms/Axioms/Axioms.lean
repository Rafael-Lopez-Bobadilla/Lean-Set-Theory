import SetTheory.FirstAxioms.Axioms.Definitions

axiom extensionality (A B : Set) :
  (∀ x : Set, x ∈ A ↔ x ∈ B) → A = B

axiom empty : Set
notation "∅" => empty
axiom empty_axiom { x : Set } : x ∉ ∅

axiom subset_axiom (A : Set) (P : Set → Prop) :
  ∃ B : Set, ∀ x : Set, x ∈ B ↔ (x ∈ A ∧ P x)

axiom pairing_axiom (A B: Set) : ∃Pair: Set, ∀x: Set, x∈Pair ↔ x=A ∨ x=B

axiom union_axiom (F: Set) : ∃Union: Set, ∀x: Set, x∈Union ↔ ∃A: Set, A∈F ∧ x∈A
