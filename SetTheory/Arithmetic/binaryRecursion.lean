import SetTheory.NaturalNumbers.index

theorem binary_recursion_on_w
(g f m: Set)(h0: g is a function from w to w)
(h1: f is a function from w×w to w)(h2: m∈w) :
∃h: Set, (h is a function from w×w to w) ∧
((m,∅),g(m))∈h ∧
∀n u: Set, ((m,n),u)∈h → ((m,n⁺),f((u,m)))∈h := by
  let P1 := (fun x y => ∃d: Set, x=d ∧ y=f((d,m)))
  have ⟨fAlt,h3⟩ := relation_construction w w P1
  have h4: (∀x: Set, x∈w → ∃y: Set, (x,y)∈fAlt) := by
    intro x h5
    have h6 := (cartesian_product_xy w w x m).mpr ⟨h5,h2⟩
    have h7 := fx_on_A f (w×w) w h1 (x,m) h6
    have h8 := (cartesian_product_xy w w x f((x,m))).mpr ⟨h5,h7⟩
    have h9 := (h3.left x f((x,m))).mpr ⟨h8,⟨x,rfl,rfl⟩⟩
    exact ⟨f((x,m)),h9⟩
  have h5 : ∀x y z: Set, (x,y)∈fAlt ∧ (x,z)∈fAlt → y=z := by
    intro x y z ⟨h5,h6⟩
    have ⟨d,h7,h8⟩ := ((h3.left x y).mp h5).right
    have ⟨r,h9,h10⟩ := ((h3.left x z).mp h6).right
    have h11 := h7▸h9
    have h12 := h11 ▸ h8
    exact h10 ▸ h12
  have fAltfun : fAlt is a function from w to w := ⟨⟨h3.right.left,h5⟩,h4,h3.right⟩
  have h4: g(m)∈w := fx_on_A g w w h0 m h2
  have ⟨pm,h5,h6,h7⟩ := recursion_on_w w fAlt g(m) h4 fAltfun
  let P2 := (fun x y => ∃n: Set, x=(m,n) ∧ y=pm(n))
  have ⟨h,h8,h9⟩ := relation_construction (w×w) w P2
  apply Exists.intro h
  have h10: ∀n u: Set, ((m,n),u)∈h → ((m,n⁺),f((u,m)))∈h := by
    intro n u h10
    have ⟨h11,⟨d,h12,h13⟩⟩ := (h8 (m,n) u).mp h10
    have h14 := (ordered_pair_equiv m n m d).mp h12
    have h15: u=pm(n) := h14.right ▸ h13
    have h16 := (cartesian_product_xy (w×w) w (m,n) u).mp h11
    have h17 := (cartesian_product_xy w w m n).mp h16.left
    have h18 := (domain pm h5.left.left n).mpr (h5.right.left n h17.right)
    have h19: (n,pm(n))∈pm := f_of_x pm n h5.left h18
    have h20: (n,u)∈pm := h15 ▸ h19
    have h21: (n⁺,fAlt(u))∈pm := h7 n u h20
    have h22 := (domain fAlt h3.right.left u).mpr (fAltfun.right.left u h16.right)
    have h22: (u,fAlt(u))∈fAlt := f_of_x fAlt u fAltfun.left h22
    have h23 := (h3.left u fAlt(u)).mp h22
    have ⟨t,h24,h25⟩ := h23.right
    have h26: fAlt(u)=f((u,m)) := h24 ▸ h24 ▸ h25
    have nw := (succ_in_w n h17.right)
    have h27 := (domain pm h5.left.left n⁺).mpr (h5.right.left n⁺ nw)
    have h28: (n⁺,pm(n⁺))∈pm := f_of_x pm n⁺ h5.left h27
    have h29: fAlt(u)=pm(n⁺) := h5.left.right n⁺ fAlt(u) pm(n⁺) ⟨h21,h28⟩
    have h30: pm(n⁺)=f((u,m)) := h29▸h26
    have h31 := (cartesian_product_xy w w m n⁺).mpr ⟨h17.left,nw⟩
    have h32 := (cartesian_product_xy w w u m).mpr ⟨h16.right,h17.left⟩
    have h33 := fx_on_A f (w×w) w h1 (u,m) h32
    have h34 := (cartesian_product_xy (w×w) w (m,n⁺) f((u,m))).mpr ⟨h31,h33⟩
    exact (h8 (m,n⁺) f((u,m))).mpr ⟨h34,⟨n⁺,rfl,h30.symm⟩⟩
  have h11 := (cartesian_product_xy w w m ∅).mpr ⟨h2,zero_in_w⟩
  have h12 := fx_on_A g w w h0 m h2
  have h13 := (cartesian_product_xy (w×w) w (m,∅) g(m)).mpr ⟨h11,h12⟩
  have h14 := (domain pm h5.left.left ∅).mpr (h5.right.left ∅ zero_in_w)
  have h14 := f_of_x pm ∅ h5.left h14
  have h15: g(m)=pm(∅) := h5.left.right ∅ g(m) pm(∅) ⟨h6,h14⟩
  have h16: ((m,∅),g(m))∈h := (h8 (m,∅) g(m)).mpr ⟨h13,⟨∅,rfl,h15⟩⟩
  have h17: ∀x y z: Set, (x,y)∈h ∧ (x,z)∈h → y=z := by
    intro x y z ⟨h17,h18⟩
    have h19 := (h8 x y).mp h17
    have ⟨d,h20,h21⟩ := h19.right
    have h22 := (h8 x z).mp h18
    have ⟨n,h23,h24⟩ := h22.right
    have h25 := h20 ▸ h23
    have h26 := (ordered_pair_equiv m d m n).mp h25
    have h27 := h26.right ▸ h21
    have h28 := h27 ▸ h24
    exact h28.symm
  have h18: (∀x: Set, x∈(w×w) → ∃y: Set, (x,y)∈h) := by
    intro x h18
    have ⟨n,d,h19⟩ := (cartesian_product w w x).mp h18
    have ⟨y,h20⟩ := (h5.right.left d h19.right.left)
    have h21 := f_of_x pm d h5.left ((domain pm h5.left.left d).mpr ⟨y,h20⟩)
    have h22: y=pm(d) := (h5.left.right d y pm(d) ⟨h20,h21⟩)
    have h23 := fx_on_A pm w w h5 d h19.right.left
    have h24 := h22 ▸ h23
    have h25 := (cartesian_product_xy (w×w) w x y).mpr ⟨h18,h24⟩
    --exact (h8 x y).mpr ⟨h25,⟨d,rfl,h22⟩⟩
    --(fun x y => ∃n: Set, x=(m,n) ∧ y=pm(n))
    -- ∃n d, x=(n,d) -> n∈w ∧ d∈w
    -- ∃t, (d,t)∈pm
    sorry
  sorry
