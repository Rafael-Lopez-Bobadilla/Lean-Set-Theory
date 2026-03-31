import SetTheory.FirstAxioms.Axioms.Index

theorem difference_exists (A B : Set) :
  ∃ I : Set, ∀ x : Set, x ∈ I ↔ x ∈ A ∧ x ∉ B := by
  have h := subset_axiom A (fun x => x ∉ B)
  exact h

noncomputable def difference_operation (A B : Set) : Set :=
  Classical.choose (difference_exists A B)
infixl:70 "\\" => difference_operation

theorem difference (A B : Set) : ∀ x : Set, x ∈ A\B ↔ x ∈ A ∧ x ∉ B :=
  Classical.choose_spec (difference_exists A B)

theorem diff_test (A B x: Set) : x∈A\B → x ∉ B := by
  intro x_in_int
  have h_and := (difference A B x).mp x_in_int
  exact h_and.right
