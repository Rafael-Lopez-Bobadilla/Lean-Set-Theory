import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.Index
import SetTheory.Relations.Operations.inverse

theorem inverse_is_relation (R: Set)(h0: R is a relation) :
  R[h0]⁻¹ is a relation := by
  intro d h1
  have ⟨x,y,h2,h3⟩ := (inverse R h0 d).mp h1
  exact ⟨y,x,h3 ▸ h3⟩

theorem double_inverse
  (R: Set)(h0: R is a relation) (h1 := inverse_is_relation R h0) :
  R[h0]⁻¹[h1]⁻¹=R := by
  apply (extensionality (R[h0]⁻¹[h1]⁻¹) R).mpr
  intro d
  constructor
  intro h2
  have ⟨x,y,h3,h4⟩ := (inverse R[h0]⁻¹ h1 d).mp h2
  have ⟨x2,y2,h5,h6⟩ := (inverse R h0 (x,y)).mp h3
  have ⟨h7,h8⟩ := (ordered_pair_equiv x y y2 x2).mp h6
  have h9 := h7 ▸ h8 ▸ h5
  exact h4 ▸ h9
  intro h3
  have ⟨x,y,h4⟩ := h0 d h3
  have h5: (y,x)∈R[h0]⁻¹ := (inverse R h0 (y,x)).mpr ⟨x,y,h4▸h3,rfl⟩
  have h6: (x,y)∈R[h0]⁻¹[h1]⁻¹ := (inverse R[h0]⁻¹ h1 (x,y)).mpr ⟨y,x,h5,rfl⟩
  exact h4 ▸ h6
