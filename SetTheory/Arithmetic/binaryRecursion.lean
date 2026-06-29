import SetTheory.NaturalNumbers.index

theorem binary_to_recursion_exists (f gm: Set)
(h0: f is a function from w×w to w)(h1: gm∈w):
∀m: Set, m∈w → (∃pm: Set, (pm is a function from w to w) ∧
(∅,gm)∈pm ∧
∀n u : Set, (n,u) ∈ pm → (n⁺,f((u,m))) ∈ pm) := by
  intro m h2
  let P1 := (fun x y => ∃d: Set, x=d ∧ y=f((d,m)))
  have ⟨fAlt,h3⟩ := relation_construction w w P1
  have h4: (∀x: Set, x∈w → ∃y: Set, (x,y)∈fAlt) := by
    intro x h5
    have h6 := (cartesian_product_xy w w x m).mpr ⟨h5,h2⟩
    have h7 := fx_on_A f (w×w) w h0 (x,m) h6
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
  have h6 : fAlt is a function from w to w := ⟨⟨h3.right.left,h5⟩,h4,h3.right⟩
  have ⟨pm,h7,h8,h9⟩ := recursion_on_w w fAlt gm h1 h6
  have h10: ∀n u : Set, (n,u) ∈ pm → (n⁺,f((u,m))) ∈ pm := by
    intro n u h10
    have h11: (n⁺,fAlt(u))∈pm := h9 n u h10
    have h12 := xy_in_A_to_B pm w w h7.right.right n u h10
    have h13 := (domain fAlt h6.left.left u).mpr (h6.right.left u h12.right)
    have h14 := f_of_x fAlt u h6.left h13
    have h15 := (h3.left u fAlt(u)).mp h14
    have ⟨d,h16,h17⟩ := h15.right
    have h18 := h16 ▸ h16 ▸ h17
    exact h18 ▸ h11
  exact ⟨pm,h7,h8,h10⟩

open Classical
noncomputable def binary_to_recursion_op (f gm m: Set) : Set :=
  if h0: (f is a function from w×w to w) ∧ gm∈w ∧ m∈w then
    choose (binary_to_recursion_exists f gm h0.left h0.right.left m h0.right.right)
  else
    ∅
notation:max "pm["f","gm","m"]" => binary_to_recursion_op f gm m

theorem binary_to_recursion (f gm m: Set)
(h0: f is a function from w×w to w)(h1: gm∈w)(h2: m∈w):
(pm[f,gm,m] is a function from w to w) ∧
(∅,gm)∈pm[f,gm,m] ∧
∀n u : Set, (n,u) ∈ pm[f,gm,m] → (n⁺,f((u,m))) ∈ pm[f,gm,m] := by
  simp [binary_to_recursion_op, h0,h1,h2]
  exact choose_spec (binary_to_recursion_exists f gm h0 h1 m h2)

theorem binary_recursion_on_w
(g f: Set)(h0: g is a function from w to w)
(h1: f is a function from w×w to w) :
∃h: Set, (h is a function from w×w to w) ∧
∀m: Set, m∈w → (h((m,∅))=g(m) ∧
∀n: Set, n∈w → h((m,n⁺))=f((h((m,n)),m))) := by
  let P := (fun x y => ∃m n: Set, (m,n)∈w×w ∧ x=(m,n) ∧ y=pm[f,g(m),m](n))
  have ⟨h,h2,h3⟩ := relation_construction (w×w) w P
  have h4: ∀m: Set, m∈w → (((m,∅),g(m))∈h ∧
  ∀n u: Set, ((m,n),u)∈h → ((m,n⁺),f((u,m)))∈h) := by
    intro m h4
    have h5 := (cartesian_product_xy w w m ∅).mpr ⟨h4,zero_in_w⟩
    have h6 := fx_on_A g w w h0 m h4
    have h7 := (cartesian_product_xy (w×w) w (m,∅) g(m)).mpr ⟨h5,h6⟩
    have ⟨h8,h9,h10⟩ := (binary_to_recursion f g(m) m h1 h6 h4)
    have h11 := (domain pm[f,g(m),m] h8.left.left ∅).mpr (h8.right.left ∅ zero_in_w)
    have h12 := f_of_x pm[f,g(m),m] ∅ h8.left h11
    have h13: g(m)=pm[f,g(m),m](∅) := h8.left.right ∅ g(m) pm[f,g(m),m](∅) ⟨h9,h12⟩
    have h14: ((m,∅),g(m))∈h := (h2 (m,∅) g(m)).mpr ⟨h7,⟨m,∅,h5,rfl,h13⟩⟩
    have h15: ∀n u: Set, ((m,n),u)∈h → ((m,n⁺),f((u,m)))∈h := by
      intro n u h15
      have ⟨h16,h17⟩ := (h2 (m,n) u).mp h15
      have ⟨r,s,h18,h19,h20⟩ := h17
      have h21: m=r ∧ n=s := (ordered_pair_equiv m n r s).mp h19
      have h22: u=pm[f,g(m),m](n) := h21.left ▸ h21.right ▸ h20
      have h23 := (cartesian_product_xy w w r s).mp h18
      have h24 := h21.right ▸ h23
      have h25 := (domain pm[f,g(m),m] h8.left.left n).mpr (h8.right.left n h24.right)
      have h26 := f_of_x pm[f,g(m),m] n h8.left h25
      have h27: (n,u)∈pm[f,g(m),m] := h22 ▸ h26
      have h28: (n⁺,f((u,m)))∈pm[f,g(m),m] := h10 n u h27
      have h29 := (domain pm[f,g(m),m] h8.left.left n⁺).mpr (h8.right.left n⁺ (succ_in_w n h24.right))
      have h30 := f_of_x pm[f,g(m),m] n⁺ h8.left h29
      have h31: f((u,m))=pm[f,g(m),m](n⁺) := h8.left.right n⁺ f((u,m)) pm[f,g(m),m](n⁺) ⟨h28,h30⟩
      have h32 := (cartesian_product_xy w w m n⁺).mpr ⟨h4,(succ_in_w n h24.right)⟩
      have h33 := (cartesian_product_xy (w×w) w (m,n) u).mp h16
      have h34 := (cartesian_product_xy w w u m).mpr ⟨h33.right,h4⟩
      have h35 := fx_on_A f (w×w) w h1 (u,m) h34
      have h36 := (cartesian_product_xy (w×w) w (m,n⁺) f((u,m))).mpr ⟨h32,h35⟩
      exact (h2 (m,n⁺) f((u,m))).mpr ⟨h36,⟨m,n⁺,h32,rfl,h31⟩⟩
    exact ⟨h14,h15⟩
  have h5: (∀x: Set, x∈w×w → ∃y: Set, (x,y)∈h) := by
    intro x h5
    have ⟨m,n,h6,h7,h8⟩ := (cartesian_product w w x).mp h5
    have h9 := h8 ▸ h5
    have h10 := fx_on_A g w w h0 m h6
    have ⟨h11,h12,h13⟩ := (binary_to_recursion f g(m) m h1 h10 h6)
    have h14 := fx_on_A pm[f,g(m),m] w w h11 n h7
    have h15 := (cartesian_product_xy (w×w) w (m,n) pm[f,g(m),m](n)).mpr ⟨h9,h14⟩
    have h16 := (h2 (m,n) pm[f,g(m),m](n)).mpr ⟨h15,m,n,h9,rfl,rfl⟩
    have h17 := h8 ▸ h16
    exact ⟨pm[f,g(m),m](n),h17⟩
  have h6: ∀x y z: Set, (x,y)∈h ∧ (x,z)∈h → y=z := by
    intro x y z ⟨h6,h7⟩
    have ⟨h8,h9⟩ := (h2 x y).mp h6
    have ⟨h10,h11⟩ := (h2 x z).mp h7
    have ⟨m,n,h12,h13,h14⟩ := h9
    have ⟨r,s,h15,h16,h17⟩ := h11
    have h18 := h13 ▸ h16
    have ⟨h19,h20⟩ := (ordered_pair_equiv m n r s).mp h18
    have h21 := h19 ▸ h20 ▸ h17
    have h22 := h14 ▸ h21
    exact h22.symm
  have h7: h is a function from w×w to w := ⟨⟨h3.left,h6⟩,h5,h3⟩
  have h8: ∀m: Set, m∈w → (h((m,∅))=g(m) ∧
  ∀n: Set, n∈w → h((m,n⁺))=f((h((m,n)),m))) := by
    intro m h8
    have h9 := (h4 m h8).left
    have h10 := (domain h h7.left.left (m,∅)).mpr ⟨g(m),(h4 m h8).left⟩
    have h11 := f_of_x h (m,∅) h7.left h10
    have h12 := h7.left.right (m,∅) g(m) h((m,∅)) ⟨h9,h11⟩
    have h13: ∀n: Set, n∈w → h((m,n⁺))=f((h((m,n)),m)) := by
      intro n h13
      have h14 := (cartesian_product_xy w w m n).mpr ⟨h8,h13⟩
      have h15 := (domain h h7.left.left (m,n)).mpr (h7.right.left (m,n) h14)
      have h16 := f_of_x h (m,n) h7.left h15
      have h17: ((m,n⁺),f((h((m,n)),m)))∈h := (h4 m h8).right n h((m,n)) h16
      have h18 := (cartesian_product_xy w w m n⁺).mpr ⟨h8,(succ_in_w n h13)⟩
      have h19 := (domain h h7.left.left (m,n⁺)).mpr (h7.right.left (m,n⁺) h18)
      have h20 := f_of_x h (m,n⁺) h7.left h19
      have h21 := h7.left.right (m,n⁺) f((h((m,n)),m)) h((m,n⁺)) ⟨h17,h20⟩
      exact h21.symm
    exact ⟨h12.symm,h13⟩
  exact ⟨h,h7,h8⟩

theorem binary_recursion_on_w_relation_form
(g f: Set)(h0: g is a function from w to w)
(h1: f is a function from w×w to w) :
∃h: Set, (h is a function from w×w to w) ∧
∀m: Set, m∈w → (((m,∅),g(m))∈h ∧
∀n u: Set, ((m,n),u)∈h → ((m,n⁺),f((u,m)))∈h) := by
  let P := (fun x y => ∃m n: Set, (m,n)∈w×w ∧ x=(m,n) ∧ y=pm[f,g(m),m](n))
  have ⟨h,h2,h3⟩ := relation_construction (w×w) w P
  have h4: ∀m: Set, m∈w → (((m,∅),g(m))∈h ∧
  ∀n u: Set, ((m,n),u)∈h → ((m,n⁺),f((u,m)))∈h) := by
    intro m h4
    have h5 := (cartesian_product_xy w w m ∅).mpr ⟨h4,zero_in_w⟩
    have h6 := fx_on_A g w w h0 m h4
    have h7 := (cartesian_product_xy (w×w) w (m,∅) g(m)).mpr ⟨h5,h6⟩
    have ⟨h8,h9,h10⟩ := (binary_to_recursion f g(m) m h1 h6 h4)
    have h11 := (domain pm[f,g(m),m] h8.left.left ∅).mpr (h8.right.left ∅ zero_in_w)
    have h12 := f_of_x pm[f,g(m),m] ∅ h8.left h11
    have h13: g(m)=pm[f,g(m),m](∅) := h8.left.right ∅ g(m) pm[f,g(m),m](∅) ⟨h9,h12⟩
    have h14: ((m,∅),g(m))∈h := (h2 (m,∅) g(m)).mpr ⟨h7,⟨m,∅,h5,rfl,h13⟩⟩
    have h15: ∀n u: Set, ((m,n),u)∈h → ((m,n⁺),f((u,m)))∈h := by
      intro n u h15
      have ⟨h16,h17⟩ := (h2 (m,n) u).mp h15
      have ⟨r,s,h18,h19,h20⟩ := h17
      have h21: m=r ∧ n=s := (ordered_pair_equiv m n r s).mp h19
      have h22: u=pm[f,g(m),m](n) := h21.left ▸ h21.right ▸ h20
      have h23 := (cartesian_product_xy w w r s).mp h18
      have h24 := h21.right ▸ h23
      have h25 := (domain pm[f,g(m),m] h8.left.left n).mpr (h8.right.left n h24.right)
      have h26 := f_of_x pm[f,g(m),m] n h8.left h25
      have h27: (n,u)∈pm[f,g(m),m] := h22 ▸ h26
      have h28: (n⁺,f((u,m)))∈pm[f,g(m),m] := h10 n u h27
      have h29 := (domain pm[f,g(m),m] h8.left.left n⁺).mpr (h8.right.left n⁺ (succ_in_w n h24.right))
      have h30 := f_of_x pm[f,g(m),m] n⁺ h8.left h29
      have h31: f((u,m))=pm[f,g(m),m](n⁺) := h8.left.right n⁺ f((u,m)) pm[f,g(m),m](n⁺) ⟨h28,h30⟩
      have h32 := (cartesian_product_xy w w m n⁺).mpr ⟨h4,(succ_in_w n h24.right)⟩
      have h33 := (cartesian_product_xy (w×w) w (m,n) u).mp h16
      have h34 := (cartesian_product_xy w w u m).mpr ⟨h33.right,h4⟩
      have h35 := fx_on_A f (w×w) w h1 (u,m) h34
      have h36 := (cartesian_product_xy (w×w) w (m,n⁺) f((u,m))).mpr ⟨h32,h35⟩
      exact (h2 (m,n⁺) f((u,m))).mpr ⟨h36,⟨m,n⁺,h32,rfl,h31⟩⟩
    exact ⟨h14,h15⟩
  have h5: (∀x: Set, x∈w×w → ∃y: Set, (x,y)∈h) := by
    intro x h5
    have ⟨m,n,h6,h7,h8⟩ := (cartesian_product w w x).mp h5
    have h9 := h8 ▸ h5
    have h10 := fx_on_A g w w h0 m h6
    have ⟨h11,h12,h13⟩ := (binary_to_recursion f g(m) m h1 h10 h6)
    have h14 := fx_on_A pm[f,g(m),m] w w h11 n h7
    have h15 := (cartesian_product_xy (w×w) w (m,n) pm[f,g(m),m](n)).mpr ⟨h9,h14⟩
    have h16 := (h2 (m,n) pm[f,g(m),m](n)).mpr ⟨h15,m,n,h9,rfl,rfl⟩
    have h17 := h8 ▸ h16
    exact ⟨pm[f,g(m),m](n),h17⟩
  have h6: ∀x y z: Set, (x,y)∈h ∧ (x,z)∈h → y=z := by
    intro x y z ⟨h6,h7⟩
    have ⟨h8,h9⟩ := (h2 x y).mp h6
    have ⟨h10,h11⟩ := (h2 x z).mp h7
    have ⟨m,n,h12,h13,h14⟩ := h9
    have ⟨r,s,h15,h16,h17⟩ := h11
    have h18 := h13 ▸ h16
    have ⟨h19,h20⟩ := (ordered_pair_equiv m n r s).mp h18
    have h21 := h19 ▸ h20 ▸ h17
    have h22 := h14 ▸ h21
    exact h22.symm
  have h7: h is a function from w×w to w := ⟨⟨h3.left,h6⟩,h5,h3⟩
  exact ⟨h,h7,h4⟩
