import SetTheory.FirstAxioms.Axioms.Index
import SetTheory.FirstAxioms.Theorems.intersection
import SetTheory.FirstAxioms.Theorems.difference

theorem inter_diff_equiv (A B C: Set) : A ∩ (B \ C) = (A ∩ B) \ C := by
  apply extensionality
  intro x
  constructor
  intro x_in_A_int_diff
  have x_in_A_and_diff := (intersection A (B\C) x).mp x_in_A_int_diff
  have x_in_A := x_in_A_and_diff.left
  have x_in_B_and_not_C := (difference B C x).mp x_in_A_and_diff.right
  have x_in_B := x_in_B_and_not_C.left
  --have x_in_A_and_B: x∈A ∧ x∈B := ⟨x_in_A, x_in_B⟩
  have x_in_AB_int := (intersection A B x).mpr ⟨x_in_A, x_in_B⟩
  have x_not_in_C := x_in_B_and_not_C.right
  have x_in_int_minus_C := (difference (A∩B) C x).mpr ⟨x_in_AB_int, x_not_in_C⟩
  exact x_in_int_minus_C
  intro x_in_int_minus_C
  have x_in_int_and_not_C := (difference (A∩B) C x).mp x_in_int_minus_C
  have x_in_A_and_B := (intersection A B x).mp x_in_int_and_not_C.left
  have x_in_A := x_in_A_and_B.left
  have x_in_B := x_in_A_and_B.right
  have x_not_in_C := x_in_int_and_not_C.right
  have x_in_B_minus_C := (difference B C x).mpr ⟨x_in_B, x_not_in_C⟩
  have x_in_A_int_diff := (intersection A (B\C) x).mpr ⟨x_in_A, x_in_B_minus_C⟩
  exact x_in_A_int_diff

theorem inter_diff_equiv_2 (A B C : Set) : A ∩ (B \ C) = (A ∩ B) \ C := by
  apply extensionality
  intro x
  rw [intersection] -- Goal: x ∈ A ∧ x ∈ B \ C ↔ ...
  rw [difference]       -- Goal: x ∈ A ∧ (x ∈ B ∧ x ∉ C) ↔ ...
  rw [difference]       -- Goal: x ∈ A ∧ (x ∈ B ∧ x ∉ C) ↔ x ∈ A ∩ B ∧ x ∉ C
  rw [intersection] -- Goal: x ∈ A ∧ (x ∈ B ∧ x ∉ C) ↔ (x ∈ A ∧ x ∈ B) ∧ x ∉ C
  constructor
  intro h
  exact ⟨⟨h.left, h.right.left⟩, h.right.right⟩
  intro h
  exact ⟨h.left.left, ⟨h.left.right, h.right⟩⟩
