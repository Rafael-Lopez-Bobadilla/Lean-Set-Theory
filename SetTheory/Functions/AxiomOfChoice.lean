import SetTheory.Functions.composition
import SetTheory.Functions.identity

axiom axiom_of_choice (F I B: Set)
(h0: F maps I onto B)
(h1: ∀Y: Set, Y∈B → ∃d: Set, d∈Y) :
∃C X: Set, (C maps I onto X) ∧
∀i d: Set, (i,d)∈C → ∃Y: Set, (i,Y)∈F ∧ d∈Y

theorem choice_function_C_to_UC (C: Set)
(h0: ∀A: Set, A∈C → ∃d: Set, d∈A) :
∃H: Set, (H is a function from C to ⋃C) ∧
∀A d: Set, (A,d)∈H → d∈A := by
  have h1: I[C] maps C onto C := identity_is_surjection C
  have ⟨H,UC,⟨h9,h10⟩⟩ := axiom_of_choice I[C] C C h1 h0
  have h11: UC⊆⋃C := by
    intro d h12
    have ⟨x,h13⟩ := (h9.right d h12)
    have ⟨Y,h14,h15⟩ := h10 x d h13
    have h16 := xy_in_A_to_B I[C] C C h1.left.right.right x Y h14
    exact (arbitrary_union C d).mpr ⟨Y,h16.right,h15⟩
  have h12: H⊆C×⋃C := by
    intro d h13
    have h14 := h9.left.right.right.right d h13
    have ⟨x,y,h15,h16,h17⟩ := (cartesian_product C UC d).mp h14
    have h18: y∈⋃C := h11 y h16
    exact (cartesian_product C ⋃C d).mpr ⟨x,y,h15,h18,h17⟩
  have h13: H is a function from C to ⋃C :=
    ⟨h9.left.left,h9.left.right.left,⟨h9.left.left.left,h12⟩⟩
  have h14: ∀A d: Set, (A,d)∈H → d∈A := by
    intro A d h15
    have ⟨Y,h16,h17⟩:= (h10 A d h15)
    have ⟨h18,⟨x,h19⟩⟩ := (identity C (A,Y)).mp h16
    have ⟨h20,h21⟩ := (ordered_pair_equiv A Y x x).mp h19
    have h22 := h20▸h21
    exact h22▸h17
  exact ⟨H,h13,h14⟩

theorem choice_function_t (F I B: Set) (h0: F maps I onto B)
(h1: ∀Y: Set, Y∈B → ∃d: Set, d∈Y) :
∃C X: Set, (C maps I onto X) ∧
∀i d: Set, (i,d)∈C → ∃Y: Set, (i,Y)∈F ∧ d∈Y := by
  have ⟨H,⟨h2,h3⟩⟩ := choice_function_C_to_UC B h1
  have h4: H is a relation := h2.left.left
  have h5: F is a relation := h0.left.left.left
  let HF: Set := [h4,h5]H∘F
  have h5: ∀i d: Set, (i,d)∈HF → ∃Y: Set, (i,Y)∈F ∧ d∈Y := by
    intro i d h6
    have ⟨t,h7,h8⟩ := (composition_xy H F h4 h5 i d).mp h6
    have h9 := h3 t d h8
    exact ⟨t,h7,h9⟩
  have h6 := comp_is_function_AB H F I B ⋃B h0.left h2
  have h7 := surjection_on_range HF I ⋃B h6
  exact ⟨HF,ran(HF)[h6.left.left],h7,h5⟩
