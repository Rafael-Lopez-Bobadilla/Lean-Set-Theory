import SetTheory.FirstAxioms.Axioms.Index
import SetTheory.FirstAxioms.Theorems.difference
import SetTheory.FirstAxioms.Theorems.intersection
import SetTheory.FirstAxioms.Theorems.power_set

theorem subset_transitivity (A B C: Set) : A⊆B ∧ B⊆C → A⊆C := by
  intro h1 x h2
  have h3: x∈B := h1.left x h2
  exact h1.right x h3

theorem two_e_four (A B C: Set) : B⊆C → (A\C ⊆ A\B) := by
  intro h1 x h2
  have h3: x∈A ∧ x∉C := (difference A C x).mp h2
  have h4: x∉B := by
    intro h4_1
    have h4_2: x∈C := h1 x h4_1
    exact h3.right h4_2
  exact (difference A B x).mpr ⟨h3.left, h4⟩

theorem two_e_five (A: Set) : ∃x: Set, x∉A := by
  have ⟨B, h1⟩ := subset_axiom A (fun x => x∉x)
  apply Exists.intro B
  intro h2
  have h3: B∉B := by
    intro h3_1
    exact ((h1 B).mp h3_1).right h3_1
  have h4: B∈B := (h1 B).mpr ⟨h2,h3⟩
  exact h3 h4

theorem two_e_eighteen (A B C: Set) :
  A⊆B ∧ B∩C=∅ → A⊆(B\C) := by
  intro h1 x h2
  have h3: x∈B := h1.left x h2
  have h4: x∉C := by
    intro h4_1
    have h4_2 : x∈B∩C := (intersection B C x).mpr ⟨h3, h4_1⟩
    have h4_3 : x∉B∩C := h1.right ▸ empty_axiom x
    exact h4_3 h4_2
  exact (difference B C x).mpr ⟨h3, h4⟩

theorem two_e_nineteen (A B C: Set):
  (A\B)⊆C ∧ A⊈C → A∩B≠∅ := by
  intro h1 h2
  have h4: ∀x: Set, x∈A → x∉B := by
    intro x h4_1 h4_2
    have h4_3: x∈A∩B := (intersection A B x).mpr ⟨h4_1,h4_2⟩
    exact (h2 ▸ empty_axiom x) h4_3
  have h5: A⊆C := by
    intro x h5_1
    have h5_2: x∉B := h4 x h5_1
    have h5_3: x∈A\B := (difference A B x).mpr ⟨h5_1, h5_2⟩
    exact h1.left x h5_3
  exact h1.right h5

theorem two_e_twenty (A B: Set): P(A)⊆P(B) → A⊆B := by
  intro h1 x h2
  have ⟨single, h3⟩ := pairing_axiom x x
  have h4: single⊆A := by
    intro d h4_1
    have h4_2: d=x := by
      have h4_2_1 := (h3 d).mp h4_1
      cases h4_2_1 with
      | inl left =>
        exact left
      | inr right =>
        exact right
    exact h4_2 ▸ h2
  have h5: single∈P(A) := (power_set A single).mpr h4
  have h6: single∈P(B) := h1 single h5
  have h7: single⊆B := (power_set B single).mp h6
  exact h7 x ((h3 x).mpr (Or.inl rfl))
