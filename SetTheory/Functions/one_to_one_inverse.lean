import SetTheory.Relations.Index
import SetTheory.Functions.functions

theorem one_to_one_inverse (F: Set) (h0: F is one to one) :
  F[h0.left.left]⁻¹ is one to one := by
  have h1: F[h0.left.left]⁻¹ is single valued := by
    have h2: ∀x y z: Set,
      (x,y)∈F[h0.left.left]⁻¹ ∧ (x,z)∈F[h0.left.left]⁻¹ → y=z := by
      intro x y z ⟨h3, h4⟩
      have h5: (y,x)∈F := sorry
      sorry
    sorry
  sorry
