import SetTheory.NaturalNumbers.transitive

theorem recursion_on_w (A F x: Set)
(h0: x∈A)(h1: F is a function from A to A) :
∃h: Set, (h is a function from w to A) ∧
(∅,x)∈h ∧ (∀n u: Set, (n,u)∈h → (n⁺,F(u))∈h) := by
  let P := (fun R => R is a relation ∧ (∅,x)∈R ∧
  (∀n u: Set, (n,u)∈R → (n⁺,F(u))∈R))
  let wA := w×A
  have ⟨S,h2⟩ := subset_axiom P(w×A) P
  have h3 := (cartesian_product_xy w A ∅ x).mpr ⟨zero_in_w,h0⟩
  have h4 : (∀n u: Set, (n,u)∈w×A → (n⁺,F(u))∈w×A) := by
    intro n u h5
    have ⟨h6,h7⟩ := (cartesian_product_xy w A n u).mp h5
    have h8: F(u)∈A := fx_on_A F A A h1 u h7
    exact (cartesian_product_xy w A n⁺ F(u)).mpr ⟨succ_in_w n h6,h8⟩
  have h5 := cartesian_is_relation w A
  have h6 := (power_set wA wA).mpr (subset_of_itself wA)
  -- wA∈S
  have h7 := (h2 wA).mpr ⟨h6,⟨h5,h3,h4⟩⟩
  let h := ⋂S
  have h8: (h is a relation) := by
    intro d h9
    have h10 := (arbitrary_intersection S ⟨wA,h7⟩ d).mp h9
    have h11 := h10 wA h7
    have ⟨x,y,h12,h13,h14⟩ := (cartesian_product w A d).mp h11
    exact ⟨x,y,h14⟩
  have h9: ∀B: Set, B∈S → (∅,x)∈B := by
    intro B h10
    have h11 := (h2 B).mp h10
    exact h11.right.right.left
  let ex := (∅,x)
  -- (0,x)∈h
  have h10 := (arbitrary_intersection S ⟨wA,h7⟩ ex).mpr h9
  have h11 : (∀n u: Set, (n,u)∈h → (n⁺,F(u))∈h) := by
    intro n u h12
    let nu := (n,u)
    let nFu := (n⁺,F(u))
    have h13: ∀B: Set, B∈S → nFu∈B := by
      intro B h14
      have PB := (h2 B).mp h14
      have h13 := (arbitrary_intersection S ⟨B,h14⟩ nu).mp h12 B h14
      exact PB.right.right.right n u h13
    exact (arbitrary_intersection S ⟨wA,h7⟩ nFu).mpr h13
  have h12: h⊆w×A := by
    intro d h9
    have h10 := (arbitrary_intersection S ⟨wA,h7⟩ d).mp h9
    exact h10 wA h7
  have h_w_to_A: h is a relation from w to A := ⟨h8,h12⟩
  let Ph := (fun n => ∃y: Set, (n,y)∈h ∧ ∀z: Set, (n,z)∈h → y=z)
  have ⟨I, h13⟩ := subset_axiom w Ph
  have h14: ∀z: Set, (∅,z)∈h → x=z := by
    intro z h14
    let zpair := (∅,z)
    let R := h\{zpair}
    have h15 := relation_diff_is_relation h w A {zpair} ⟨h8,h12⟩
    have h16 := (power_set (w×A) R).mpr h15.right
    apply Classical.byContradiction
    intro h17
    have h18 := mt (fun h => ((ordered_pair_equiv ∅ x ∅ z).mp h).right) h17
    have h19 := mt (fun h => (singleton zpair ex).mp h) h18
    have h20 := (difference h {zpair} ex).mpr ⟨h10,h19⟩
    have h21: (∀n u: Set, (n,u)∈R → (n⁺,F(u))∈R) := by
      intro n u h21
      let nu := (n,u)
      have h22 := (difference h {zpair} nu).mp h21
      have h23 := h11 n u h22.left
      have h24 := zero_not_succ n
      have h25 := mt (fun h => ((ordered_pair_equiv ∅ z n⁺ F(u)).mp h).left) h24
      let nuplus := (n⁺,F(u))
      have h26 := mt (fun h => (singleton zpair nuplus).mp h) (Ne.symm h25)
      exact (difference h {zpair} nuplus).mpr ⟨h23,h26⟩
    have h22 := (h2 R).mpr ⟨h16,⟨h15.left,h20,h21⟩⟩
    have h23 := (arbitrary_intersection S ⟨R,h22⟩ zpair).mp h14 R h22
    have h24 := (singleton zpair zpair).mpr rfl
    have h25 : zpair ∉ R := fun hy => ((difference h {zpair} zpair).mp hy).right h24
    exact h25 h23
  have h15 : ∅∈I := (h13 ∅).mpr ⟨zero_in_w, ⟨x,h10,h14⟩⟩
  have h16: ∀n: Set, n∈I → n⁺∈I := by
    intro n h16
    have ⟨h17,⟨y,h18,h19⟩⟩ := (h13 n).mp h16
    have h20: (n⁺,F(y))∈h := h11 n y h18
    have h21: ∀z: Set, (n⁺,z)∈h → F(y)=z := by
      intro z h21
      let zpair := (n⁺,z)
      let R := h\{zpair}
      have h22 := zero_not_succ n
      have h23 := mt (fun h => ((ordered_pair_equiv ∅ x n⁺ z).mp h).left) h22
      have h24 := mt (fun h => (singleton zpair ex).mp h) h23
      have h25: (∅,x) ∈ R := (difference h {zpair} ex).mpr ⟨h10,h24⟩
      apply Classical.byContradiction
      intro (Fyz: F(y)≠z)
      have h26: (∀m u: Set, (m,u)∈R → (m⁺,F(u))∈R) := by
        intro m u h21
        let mu := (m,u)
        -- h22: (m,u)∈h
        have ⟨h22,h23⟩ := (difference h {zpair} mu).mp h21
        have h24: (m⁺,F(u))∈h := h11 m u h22
        have h25: (m⁺,F(u))≠(n⁺,z) := by
          intro h25
          -- m⁺=n⁺ ∧ F(u)=z
          have ⟨h26,h27⟩ := (ordered_pair_equiv m⁺ F(u) n⁺ z).mp h25
          have h28 := xy_in_A_to_B h w A h_w_to_A m u h22
          have h29 := xy_in_A_to_B h w A h_w_to_A n y h18
          have h32 := successor_equiv n m ⟨h28.left,h29.left,h26⟩
          have h33: mu=(n,u) := (ordered_pair_equiv m u n u).mpr ⟨h32,rfl⟩
          have h34 := h33 ▸ h22
          have h35 := h19 u h34
          have h36 := x_in_dom F A A h1 u h28.right
          have h37 := x_in_dom F A A h1 y h29.right
          have h38: F(y)=F(u) := (fx_fy_equiv F y u h1.left h37 h36 h35)
          have h39 := h38 ▸ h27
          exact Fyz h39
        have h26 := mt (fun h => (singleton zpair (m⁺,F(u))).mp h) h25
        exact (difference h {zpair} (m⁺,F(u))).mpr ⟨h24,h26⟩
      have h27 := relation_diff_is_relation h w A {zpair} ⟨h8,h12⟩
      have h28 := (power_set (w×A) R).mpr h27.right
      have h29 := (h2 R).mpr ⟨h28,⟨h27.left,h25,h26⟩⟩
      have h30 := (arbitrary_intersection S ⟨R,h29⟩ zpair).mp h21 R h29
      have h31 := (singleton zpair zpair).mpr rfl
      have h32 : zpair ∉ R := fun hy => ((difference h {zpair} zpair).mp hy).right h31
      exact h32 h30
    have h22 := xy_in_A_to_B h w A h_w_to_A n y h18
    have h23 := succ_in_w n h22.left
    exact (h13 n⁺).mpr ⟨h23,F(y),h20,h21⟩
  have h18 := induction_principle I Ph h13 ⟨h15,h16⟩
  --h10 (∅,x)∈h
  -- h is single valued
  have h19: ∀x y z: Set, (x,y)∈h ∧ (x,z)∈h → y=z := by
    intro x y z ⟨h19,h20⟩
    have h22 := xy_in_A_to_B h w A h_w_to_A x y h19
    have ⟨d,h23,h24⟩ := h18 x h22.left
    have h25 := h24 y h19
    have h26 := h24 z h20
    exact h25 ▸ h26
  --n∈w → (fun n => ∃y: Set, (n,y)∈h ∧ ∀z: Set, (n,z)∈h → y=z)
  have h20 : (∀x: Set, x∈w → ∃y: Set, (x,y)∈h) := by
    intro x h21
    have ⟨y,h22,h23⟩ := h18 x h21
    exact ⟨y,h22⟩
  have h21: h is a function from w to A := ⟨⟨h8,h19⟩,h20,⟨h8,h12⟩⟩
  exact ⟨h,h21,h10,h11⟩

theorem recursion_on_w_function_def (A F x: Set)
(h0: x∈A)(h1: F is a function from A to A) :
∃h: Set, (h is a function from w to A) ∧
h(∅)=x ∧ ∀n: Set, n∈w → h(n⁺)=F(h(n)) := by
  let P := (fun R => R is a relation ∧ (∅,x)∈R ∧
  (∀n u: Set, (n,u)∈R → (n⁺,F(u))∈R))
  let wA := w×A
  have ⟨S,h2⟩ := subset_axiom P(w×A) P
  have h3 := (cartesian_product_xy w A ∅ x).mpr ⟨zero_in_w,h0⟩
  have h4 : (∀n u: Set, (n,u)∈w×A → (n⁺,F(u))∈w×A) := by
    intro n u h5
    have ⟨h6,h7⟩ := (cartesian_product_xy w A n u).mp h5
    have h8: F(u)∈A := fx_on_A F A A h1 u h7
    exact (cartesian_product_xy w A n⁺ F(u)).mpr ⟨succ_in_w n h6,h8⟩
  have h5 := cartesian_is_relation w A
  have h6 := (power_set wA wA).mpr (subset_of_itself wA)
  -- wA∈S
  have h7 := (h2 wA).mpr ⟨h6,⟨h5,h3,h4⟩⟩
  let h := ⋂S
  have h8: (h is a relation) := by
    intro d h9
    have h10 := (arbitrary_intersection S ⟨wA,h7⟩ d).mp h9
    have h11 := h10 wA h7
    have ⟨x,y,h12,h13,h14⟩ := (cartesian_product w A d).mp h11
    exact ⟨x,y,h14⟩
  have h9: ∀B: Set, B∈S → (∅,x)∈B := by
    intro B h10
    have h11 := (h2 B).mp h10
    exact h11.right.right.left
  let ex := (∅,x)
  -- (0,x)∈h
  have h10 := (arbitrary_intersection S ⟨wA,h7⟩ ex).mpr h9
  have h11 : (∀n u: Set, (n,u)∈h → (n⁺,F(u))∈h) := by
    intro n u h12
    let nu := (n,u)
    let nFu := (n⁺,F(u))
    have h13: ∀B: Set, B∈S → nFu∈B := by
      intro B h14
      have PB := (h2 B).mp h14
      have h13 := (arbitrary_intersection S ⟨B,h14⟩ nu).mp h12 B h14
      exact PB.right.right.right n u h13
    exact (arbitrary_intersection S ⟨wA,h7⟩ nFu).mpr h13
  have h12: h⊆w×A := by
    intro d h9
    have h10 := (arbitrary_intersection S ⟨wA,h7⟩ d).mp h9
    exact h10 wA h7
  have h_w_to_A: h is a relation from w to A := ⟨h8,h12⟩
  let Ph := (fun n => ∃y: Set, (n,y)∈h ∧ ∀z: Set, (n,z)∈h → y=z)
  have ⟨I, h13⟩ := subset_axiom w Ph
  have h14: ∀z: Set, (∅,z)∈h → x=z := by
    intro z h14
    let zpair := (∅,z)
    let R := h\{zpair}
    have h15 := relation_diff_is_relation h w A {zpair} ⟨h8,h12⟩
    have h16 := (power_set (w×A) R).mpr h15.right
    apply Classical.byContradiction
    intro h17
    have h18 := mt (fun h => ((ordered_pair_equiv ∅ x ∅ z).mp h).right) h17
    have h19 := mt (fun h => (singleton zpair ex).mp h) h18
    have h20 := (difference h {zpair} ex).mpr ⟨h10,h19⟩
    have h21: (∀n u: Set, (n,u)∈R → (n⁺,F(u))∈R) := by
      intro n u h21
      let nu := (n,u)
      have h22 := (difference h {zpair} nu).mp h21
      have h23 := h11 n u h22.left
      have h24 := zero_not_succ n
      have h25 := mt (fun h => ((ordered_pair_equiv ∅ z n⁺ F(u)).mp h).left) h24
      let nuplus := (n⁺,F(u))
      have h26 := mt (fun h => (singleton zpair nuplus).mp h) (Ne.symm h25)
      exact (difference h {zpair} nuplus).mpr ⟨h23,h26⟩
    have h22 := (h2 R).mpr ⟨h16,⟨h15.left,h20,h21⟩⟩
    have h23 := (arbitrary_intersection S ⟨R,h22⟩ zpair).mp h14 R h22
    have h24 := (singleton zpair zpair).mpr rfl
    have h25 : zpair ∉ R := fun hy => ((difference h {zpair} zpair).mp hy).right h24
    exact h25 h23
  have h15 : ∅∈I := (h13 ∅).mpr ⟨zero_in_w, ⟨x,h10,h14⟩⟩
  have h16: ∀n: Set, n∈I → n⁺∈I := by
    intro n h16
    have ⟨h17,⟨y,h18,h19⟩⟩ := (h13 n).mp h16
    have h20: (n⁺,F(y))∈h := h11 n y h18
    have h21: ∀z: Set, (n⁺,z)∈h → F(y)=z := by
      intro z h21
      let zpair := (n⁺,z)
      let R := h\{zpair}
      have h22 := zero_not_succ n
      have h23 := mt (fun h => ((ordered_pair_equiv ∅ x n⁺ z).mp h).left) h22
      have h24 := mt (fun h => (singleton zpair ex).mp h) h23
      have h25: (∅,x) ∈ R := (difference h {zpair} ex).mpr ⟨h10,h24⟩
      apply Classical.byContradiction
      intro (Fyz: F(y)≠z)
      have h26: (∀m u: Set, (m,u)∈R → (m⁺,F(u))∈R) := by
        intro m u h21
        let mu := (m,u)
        -- h22: (m,u)∈h
        have ⟨h22,h23⟩ := (difference h {zpair} mu).mp h21
        have h24: (m⁺,F(u))∈h := h11 m u h22
        have h25: (m⁺,F(u))≠(n⁺,z) := by
          intro h25
          -- m⁺=n⁺ ∧ F(u)=z
          have ⟨h26,h27⟩ := (ordered_pair_equiv m⁺ F(u) n⁺ z).mp h25
          have h28 := xy_in_A_to_B h w A h_w_to_A m u h22
          have h29 := xy_in_A_to_B h w A h_w_to_A n y h18
          have h32 := successor_equiv n m ⟨h28.left,h29.left,h26⟩
          have h33: mu=(n,u) := (ordered_pair_equiv m u n u).mpr ⟨h32,rfl⟩
          have h34 := h33 ▸ h22
          have h35 := h19 u h34
          have h36 := x_in_dom F A A h1 u h28.right
          have h37 := x_in_dom F A A h1 y h29.right
          have h38: F(y)=F(u) := (fx_fy_equiv F y u h1.left h37 h36 h35)
          have h39 := h38 ▸ h27
          exact Fyz h39
        have h26 := mt (fun h => (singleton zpair (m⁺,F(u))).mp h) h25
        exact (difference h {zpair} (m⁺,F(u))).mpr ⟨h24,h26⟩
      have h27 := relation_diff_is_relation h w A {zpair} ⟨h8,h12⟩
      have h28 := (power_set (w×A) R).mpr h27.right
      have h29 := (h2 R).mpr ⟨h28,⟨h27.left,h25,h26⟩⟩
      have h30 := (arbitrary_intersection S ⟨R,h29⟩ zpair).mp h21 R h29
      have h31 := (singleton zpair zpair).mpr rfl
      have h32 : zpair ∉ R := fun hy => ((difference h {zpair} zpair).mp hy).right h31
      exact h32 h30
    have h22 := xy_in_A_to_B h w A h_w_to_A n y h18
    have h23 := succ_in_w n h22.left
    exact (h13 n⁺).mpr ⟨h23,F(y),h20,h21⟩
  have h18 := induction_principle I Ph h13 ⟨h15,h16⟩
  --h10 (∅,x)∈h
  -- h is single valued
  have h19: ∀x y z: Set, (x,y)∈h ∧ (x,z)∈h → y=z := by
    intro x y z ⟨h19,h20⟩
    have h22 := xy_in_A_to_B h w A h_w_to_A x y h19
    have ⟨d,h23,h24⟩ := h18 x h22.left
    have h25 := h24 y h19
    have h26 := h24 z h20
    exact h25 ▸ h26
  --n∈w → (fun n => ∃y: Set, (n,y)∈h ∧ ∀z: Set, (n,z)∈h → y=z)
  have h20 : (∀x: Set, x∈w → ∃y: Set, (x,y)∈h) := by
    intro x h21
    have ⟨y,h22,h23⟩ := h18 x h21
    exact ⟨y,h22⟩
  have h21: h is a function from w to A := ⟨⟨h8,h19⟩,h20,⟨h8,h12⟩⟩
  have h22 := (domain h h21.left.left ∅).mpr ⟨x,h10⟩
  have h23 := f_of_x h ∅ h21.left h22
  -- h(0)=x
  have h24 := (h21.left.right ∅ x h(∅) ⟨h10,h23⟩).symm
  have h25: ∀n: Set, n∈w → h(n⁺)=F(h(n)) := by
    intro n h25
    have h26 := (domain h h21.left.left n⁺).mpr (h21.right.left n⁺ (succ_in_w n h25))
    have h27: (n⁺,h(n⁺))∈h := f_of_x h n⁺ h21.left h26
    have h28 := (domain h h21.left.left n).mpr (h21.right.left n h25)
    have h29: (n,h(n))∈h := f_of_x h n h21.left h28
    -- (∀n u: Set, (n,u)∈h → (n⁺,F(u))∈h)
    have h30: (n⁺,F(h(n)))∈h := h11 n h(n) h29
    have h31 := h21.left.right n⁺ h(n⁺) F(h(n)) ⟨h27,h30⟩
    exact h31
  exact ⟨h,h21,h24,h25⟩
