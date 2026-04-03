import SetTheory.FirstAxioms.Axioms.Index

theorem subset_construction (P : Set → Prop) (A: Set) :
  (∀x: Set, P x → x∈A) → (∃S: Set, ∀x: Set, x∈S ↔ P x) := by
  have subset_exists := subset_axiom A P
  have ⟨S, in_S_iff⟩ := subset_exists
  intro px_implies_in_A
  apply Exists.intro S
  intro x
  constructor
  intro x_in_S
  have x_in_A_and_px := (in_S_iff x).mp x_in_S
  exact x_in_A_and_px.right
  intro px
  have x_in_A := (px_implies_in_A x) px
  exact (in_S_iff x).mpr ⟨x_in_A, px⟩
