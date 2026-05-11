import SetTheory.Functions.Index

theorem three_five_one
(R A: Set)(h0: R is an equivalence relation on A)
(F: Set)(h1: F is a function from A to A):
(∃G: Set, (G is a function from [h0]A/R to [h0]A/R) ∧
∀x y z: Set, (h2: x∈A ∧ z∈A) →
([R,A,h0,h2.left]class(x),y)∈G ↔
((x,z)∈F ∧ [R,A,h0,h2.right]class(z)=y)) ↔
∀x y: Set, (x,y)∈R → ∃r s: Set, (x,r)∈F ∧ (y,s)∈F ∧ (r,s)∈R := by
  constructor
  intro ⟨G,⟨h4,h5⟩⟩
  intro x y (h6: (x,y)∈R)
  have ⟨h7,h8⟩ := xy_in_A R A h0.left x y h6
  have h9 := (three_two_sixteen R A x y h0 h7 h8).mpr h6
  let xc: Set := [R,A,h0,h7]class(x)
  have h10 := (quotient_set R A h0 xc).mpr ⟨x,h7,rfl⟩
  have ⟨rc,h11⟩ := h4.right.left xc h10
  have ⟨r,h12⟩ := h1.right.left x h7
  have h13 := xy_in_A_to_B F A A h1.right.right x r h12
  have ⟨h14,h15⟩ := (h5 x rc r ⟨h7,h13.right⟩).mp h11
  let yc: Set := [R,A,h0,h8]class(y)
  have h16 := (quotient_set R A h0 yc).mpr ⟨y,h8,rfl⟩
  have ⟨sc,h17⟩ := h4.right.left yc h16
  have ⟨s,h18⟩ := h1.right.left y h8
  have h19 := xy_in_A_to_B F A A h1.right.right y s h18
  have ⟨h20,h21⟩ := (h5 y sc s ⟨h8,h19.right⟩).mp h17
  have h22 := h4.left.right [R,A,h0,h7]class(x) rc sc ⟨h11,h9▸h17⟩
  have h23 := (three_two_sixteen R A r s h0 h13.right h19.right).mp (h15 ▸ h21 ▸ h22)
  exact ⟨r,s,h12,h18,h23⟩
  intro h4

  sorry
