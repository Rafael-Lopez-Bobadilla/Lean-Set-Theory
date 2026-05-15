import SetTheory.Functions.Index

theorem three_five_one
(R A: Set)(h0: R is an equivalence relation on A)
(F: Set)(h1: F is a function from A to A):
(∃G: Set, (G is a function from A/R to A/R) ∧
∀x: Set, x∈A → G([R,A]class(x))=[R,A]class(F(x))) ↔
∀x y: Set, (x,y)∈R → (F(x),F(y))∈R := by
  constructor
  intro ⟨G,h2,h3⟩ x y h4
  let xc: Set := [R,A]class(x)
  let yc: Set := [R,A]class(y)
  have ⟨h5,h6⟩ := xy_in_A R A h0.left x y h4
  have h7: xc=yc := (three_two_sixteen R A x y h0 h5 h6).mpr h4
  have h8: G(xc) = [R,A]class(F(x)) := h3 x h5
  have h9: G(yc) = [R,A]class(F(y)) := h3 y h6
  have h10: xc ∈ A/R := (quotient_set R A h0 xc).mpr ⟨x,h5,rfl⟩
  have h11: xc ∈ dom(G) := x_in_dom G A/R A/R h2 xc h10
  have h12: yc ∈ A/R := (quotient_set R A h0 yc).mpr ⟨y,h6,rfl⟩
  have h13: yc ∈ dom(G) := x_in_dom G A/R A/R h2 yc h12
  have h14: G(xc) = G(yc) := fx_fy_equiv G xc yc h2.left h11 h13 h7
  have h15: G(yc) = [R,A]class(F(x)) := h14 ▸ h8
  have h16: [R,A]class(F(y)) = [R,A]class(F(x)) := h9 ▸ h15
  have h17 := fx_on_A F A A h1 x h5
  have h18 := fx_on_A F A A h1 y h6
  exact (three_two_sixteen R A F(x) F(y) h0 h17 h18).mp (h16▸h16)
  intro h2
  let P := (fun xc fxc => ∃x: Set, x∈A ∧ xc=[R,A]class(x) ∧ fxc=[R,A]class(F(x)))
  have ⟨G, h3,h4⟩ := relation_construction A/R A/R P
  have h5: ∀xc: Set, xc∈A/R → ∃y: Set, (xc,y)∈G := by
    intro xc h6
    have ⟨x,h7⟩ := (quotient_set R A h0 xc).mp h6
    have h8 := fx_on_A F A A h1 x h7.left
    let fxc := [R,A]class(F(x))
    have h8 := (quotient_set R A h0 fxc).mpr ⟨F(x),h8,rfl⟩
    have h9 := (cartesian_product_xy A/R A/R xc fxc).mpr ⟨h6,h8⟩
    have h10 := (h3 xc fxc).mpr ⟨h9,⟨x,h7.left,h7.right,rfl⟩⟩
    exact ⟨fxc,h10⟩
  have h6: ∀x y z: Set, (x,y)∈G ∧ (x,z)∈G → y=z := by
    intro x y z ⟨h7,h8⟩
    have ⟨h9,⟨r,h10,h11,h12⟩⟩ := (h3 x y).mp h7
    have ⟨h13,⟨s,h14,h15,h16⟩⟩ := (h3 x z).mp h8
    have h17 := (three_two_sixteen R A r s h0 h10 h14).mp (h11▸h15)
    have h18 := h2 r s h17
    have h19 := fx_on_A F A A h1 r h10
    have h20 := fx_on_A F A A h1 s h14
    have h21 := (three_two_sixteen R A F(r) F(s) h0 h19 h20).mpr h18
    have h22 := h12 ▸ h21
    exact h16▸h22
  have h7: G is a function := ⟨h4.left,h6⟩
  have h8: G is a function from A/R to A/R := ⟨h7, h5, h4⟩
  have h9: ∀x: Set, x∈A → G([R,A]class(x))=[R,A]class(F(x)) := by
    intro x h10
    let xc := [R,A]class(x)
    have h11 := (quotient_set R A h0 xc).mpr ⟨x,h10,rfl⟩
    have h12 := x_in_dom G A/R A/R h8 xc h11
    have h13 := f_of_x G xc h7 h12
    have ⟨h14,⟨r,h15,h16,h17⟩⟩ := (h3 xc G(xc)).mp h13
    have h18 := (three_two_sixteen R A x r h0 h10 h15).mp h16
    have h19 := h2 x r h18
    have h20 := fx_on_A F A A h1 x h10
    have h21 := fx_on_A F A A h1 r h15
    have h20 := (three_two_sixteen R A F(x) F(r) h0 h20 h21).mpr h19
    exact h20 ▸ h17
  exact ⟨G,h8,h9⟩
