import SetTheory.Relations.Index
import SetTheory.Functions.functions

theorem one_to_one_inverse (F: Set) (h0: F is one to one)
  (h1 := h0.left.left) :
  F[h1]⁻¹ is one to one := by
  have sv: F[h1]⁻¹ is single valued := by
    have h2: ∀x y z: Set,
      (x,y)∈F[h1]⁻¹ ∧ (x,z)∈F[h1]⁻¹ → y=z := by
      intro x y z ⟨h3, h4⟩
      have h5: (y,x)∈F := (inverse_xy F x y h1).mp h3
      have h6: (z,x)∈F := (inverse_xy F x z h1).mp h4
      have h7 := h0.right.right y x z ⟨h5,h6⟩
      exact h7 ▸ h7
    exact ⟨(inverse_is_relation F h1), h2⟩
  have h2: F[h1]⁻¹ is single rooted := by

    sorry
  sorry
