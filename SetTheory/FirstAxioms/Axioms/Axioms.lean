import SetTheory.FirstAxioms.Axioms.Definitions

axiom extensionality {A B : Set} :
  (∀ x : Set, x ∈ A ↔ x ∈ B) → A = B

axiom empty : Set
notation "∅" => empty
axiom empty_axiom { x : Set } : x ∉ ∅

axiom subset_axiom (A : Set) (P : Set → Prop) :
  ∃ B : Set, ∀ x : Set, x ∈ B ↔ (x ∈ A ∧ P x)
