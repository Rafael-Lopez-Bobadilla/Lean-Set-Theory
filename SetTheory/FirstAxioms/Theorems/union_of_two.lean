import SetTheory.FirstAxioms.Axioms.Index

theorem union_of_two_exists (A B: Set) :
  ∃Union: Set, ∀x: Set, x∈Union ↔ x∈A ∨ x∈B := by
  have ⟨pair_AB, pair_member⟩ := pairing_axiom A B
  have ⟨union_pair, union_pair_member⟩ := union_axiom pair_AB
  apply Exists.intro union_pair
  intro x
  constructor
  intro x_in_union_pair
  have ⟨D, D_in_and⟩ := (union_pair_member x).mp x_in_union_pair
  have D_in_pair := (pair_member D).mp D_in_and.left
  cases D_in_pair with
  | inl D_is_A =>
    exact Or.inl (D_is_A ▸ D_in_and.right)
  | inr D_is_B =>
    exact Or.inr (D_is_B ▸ D_in_and.right)
  intro x_in_or
  cases x_in_or with
  | inl x_in_A =>
    have A_in_pair : A ∈ pair_AB := (pair_member A).mpr (Or.inl rfl)
    have exists_cond : ∃ D : Set, D ∈ pair_AB ∧ x ∈ D :=
      Exists.intro A ⟨A_in_pair, x_in_A⟩
    exact (union_pair_member x).mpr exists_cond
  | inr x_in_B =>
    have B_in_pair : B ∈ pair_AB := (pair_member B).mpr (Or.inr rfl)
    have exists_cond : ∃ D : Set, D ∈ pair_AB ∧ x ∈ D :=
      Exists.intro B ⟨B_in_pair, x_in_B⟩
    exact (union_pair_member x).mpr exists_cond

noncomputable def union_of_two_definition (A B: Set) : Set :=
  Classical.choose (union_of_two_exists A B)
infix:70 "∪" => union_of_two_definition

theorem union_of_two (A B: Set): ∀x: Set, x∈A∪B ↔ (x∈A ∨ x∈B) :=
  Classical.choose_spec (union_of_two_exists A B)

theorem union_test_1 (A B x: Set): x∈A → x∈A∪B := by
  intro x_in_A
  exact (union_of_two A B x).mpr (Or.inl x_in_A)
