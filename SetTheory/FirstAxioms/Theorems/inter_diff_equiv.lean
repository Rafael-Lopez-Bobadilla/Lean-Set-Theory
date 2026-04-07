import SetTheory.FirstAxioms.Axioms.Index
import SetTheory.FirstAxioms.Theorems.intersection
import SetTheory.FirstAxioms.Theorems.difference

theorem inter_diff_equiv (A B C: Set) : A ∩ (B \ C) = (A ∩ B) \ C := by
  apply extensionality
  intro x
  constructor
  intro h1
  have h2: x∈A ∧ x∈(B\C) := (intersection A (B\C) x).mp h1
  have h3: x∈B ∧ x∉C := (difference B C x).mp h2.right
  --have x_in_A_and_B: x∈A ∧ x∈B := ⟨x_in_A, x_in_B⟩
  have h5: x∈A∩B := (intersection A B x).mpr ⟨h2.left, h3.left⟩
  have h6: x ∈ A∩B\C := (difference (A∩B) C x).mpr ⟨h5, h3.right⟩
  exact h6
  intro h1
  have h2: x ∈ A∩B ∧ x ∉ C := (difference (A∩B) C x).mp h1
  have h3:  x ∈ A ∧ x ∈ B := (intersection A B x).mp h2.left
  have h4: x ∈ B\C := (difference B C x).mpr ⟨h3.right, h2.right⟩
  have h5: x ∈ A∩(B\C) := (intersection A (B\C) x).mpr ⟨h3.left, h4⟩
  exact h5

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
