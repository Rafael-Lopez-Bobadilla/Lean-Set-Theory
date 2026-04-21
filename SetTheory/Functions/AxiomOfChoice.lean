import SetTheory.Functions.composition

axiom axiom_of_choice (F I B: Set)
(h0: F maps I onto B)
(h1: ∀Y: Set, Y∈B → ∃d: Set, d∈Y) :
∃C X: Set, (C maps I onto X) ∧
∀i d: Set, (i,d)∈C → ∃Y: Set, (i,Y)∈F ∧ d∈Y

theorem choice_function_C_to_UC (C: Set)
(h0: ∀A: Set, A∈C → ∃d: Set, d∈A) :
∃H: Set, (H is a function from C to ⋃C) ∧
∀A d: Set, (A,d)∈H → d∈A := by
  have ⟨I,h1⟩ := subset_axiom (C×C) (fun d => ∃x: Set, d=(x,x))
  have h2 : ∀x y z: Set, (x,y)∈I ∧ (x,z)∈I → y=z := by
    intro x y z ⟨h3,h4⟩
    have ⟨h5,⟨x2,h6⟩⟩ := (h1 (x,y)).mp h3
    have ⟨h7,⟨x3,h8⟩⟩ := (h1 (x,z)).mp h4
    have h9 := (ordered_pair_equiv x y x2 x2).mp h6
    have h10 := (ordered_pair_equiv x z x3 x3).mp h8
    have h11 := h10.left▸h9.left▸h9.right
    exact h10.right▸h11
  have h3 : ∀x: Set, x∈C → ∃y: Set, (x,y)∈I := by
    intro x h4
    have h5 := (cartesian_product_xy C C x x).mpr ⟨h4,h4⟩
    have h6 := (h1 (x,x)).mpr ⟨h5,x,rfl⟩
    exact ⟨x,h6⟩
  have h4 : I⊆C×C := by
    intro d h5
    exact ((h1 d).mp h5).left
  have h5 : ∀y: Set, y∈C → ∃x: Set, (x,y)∈I := by
    intro y h6
    have h7 := (cartesian_product_xy C C y y).mpr ⟨h6,h6⟩
    have h8 := (h1 (y,y)).mpr ⟨h7,y,rfl⟩
    exact ⟨y,h8⟩
  have h6 : I is a relation := by
    intro d h7
    have ⟨h8,⟨x,h9⟩⟩ := (h1 d).mp h7
    exact ⟨x,x,h9⟩
  have h7: I is a function from C to C := ⟨⟨h6,h2⟩,h3,⟨h6,h4⟩⟩
  have h8 : I maps C onto C := ⟨h7,h5⟩
  have ⟨H,UC,⟨h9,h10⟩⟩ := axiom_of_choice I C C h8 h0
  have h11: UC⊆⋃C := by
    intro d h12
    have ⟨x,h13⟩ := (h9.right d h12)
    have ⟨Y,h14,h15⟩ := h10 x d h13
    have h16 := xy_in_A_to_B I C C h8.left.right.right x Y h14
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
    have ⟨h18,⟨x,h19⟩⟩ := (h1 (A,Y)).mp h16
    have ⟨h20,h21⟩ := (ordered_pair_equiv A Y x x).mp h19
    have h22 := h20▸h21
    exact h22▸h17
  exact ⟨H,h13,h14⟩
