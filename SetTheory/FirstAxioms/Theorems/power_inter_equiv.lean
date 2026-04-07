import SetTheory.FirstAxioms.Axioms.Index
import SetTheory.FirstAxioms.Theorems.power_set
import SetTheory.FirstAxioms.Theorems.intersection

theorem power_inter_equiv (A B: Set) : P(A∩B) = P(A)∩P(B) := by
  apply extensionality
  intro x
  constructor
  intro h1
  have h2: x⊆A∩B := (power_set (A∩B) x).mp h1
  have h3: x⊆A := by
    intro d h3_1
    have h3_2: d∈A∩B := h2 d h3_1
    exact ((intersection A B d).mp h3_2).left
  have h4: x⊆B := by
    intro d h4_1
    have h4_2: d∈A∩B := h2 d h4_1
    exact ((intersection A B d).mp h4_2).right
  have h5: x∈P(A) := (power_set A x).mpr h3
  have h6: x∈P(B) := (power_set B x).mpr h4
  exact (intersection P(A) P(B) x).mpr ⟨h5, h6⟩
  intro h7
  have h8: x∈P(A) ∧ x∈P(B) := (intersection P(A) P(B) x).mp h7
  have h9: x⊆A := (power_set A x).mp h8.left
  have h10: x⊆B := (power_set B x).mp h8.right
  have h11: x⊆(A∩B) := by
    intro d h12
    exact (intersection A B d).mpr ⟨h9 d h12, h10 d h12⟩
  exact (power_set (A∩B) x).mpr h11
