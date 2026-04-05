import SetTheory.FirstAxioms.Axioms.Index

theorem intersection_exists (A B : Set) :
  ∃ I : Set, ∀ x : Set, x ∈ I ↔ x ∈ A ∧ x ∈ B := by
  have h := subset_axiom A (fun x => x ∈ B)
  exact h

noncomputable def intersection_operation (A B : Set) : Set :=
  Classical.choose (intersection_exists A B)
infix:70 "∩" => intersection_operation

theorem intersection {A B : Set} : ∀ x : Set, x ∈ A∩B ↔ x ∈ A ∧ x ∈ B :=
  Classical.choose_spec (intersection_exists A B)

theorem inter_test (A B x: Set) : x∈A∩B → x ∈ A := by
  intro x_in_int
  have h_and := (intersection x).mp x_in_int
  exact h_and.left
