import SetTheory.Arithmetic.binaryRecursion

theorem addition_function_exists :
∃A: Set, (A is a function from w×w to w) ∧
∀m: Set, m∈w → (A((m,∅)) = m ∧
∀n: Set, n∈w → A((m,n⁺))=A((m,n))⁺) := by
  have h1 := identity_is_functionAA w
  let P1 := (fun x y => ∃k m: Set, x=(k,m) ∧ y=k⁺)
  have ⟨f,h2,h3⟩ := relation_construction (w×w) w P1
  have h4: (∀x: Set, x∈w×w → ∃y: Set, (x,y)∈f) := by
    intro x h4
    have ⟨k,m,h5,h6,h7⟩ := (cartesian_product w w x).mp h4
    have h8 := succ_in_w k h5
    have h9 := (cartesian_product_xy (w×w) w x k⁺).mpr ⟨h4,h8⟩
    have h8 := (h2 x k⁺).mpr ⟨h9,⟨k,m,h7,rfl⟩⟩
    exact ⟨k⁺,h8⟩
  have h5: ∀x y z: Set, (x,y)∈f ∧ (x,z)∈f → y=z := by
    intro x y z ⟨h5,h6⟩
    have ⟨h7,⟨k,m,h8,h9⟩⟩ := (h2 x y).mp h5
    have ⟨h10,⟨r,s,h11,h12⟩⟩ := (h2 x z).mp h6
    have h14 := h8 ▸ h11
    have h15 := (ordered_pair_equiv k m r s).mp h14
    have h16 := h15.left ▸ h9
    have h17 := h16 ▸ h12
    exact h17.symm
  have h6: f is a function from w×w to w := ⟨⟨h3.left,h5⟩,h4,h3⟩
  have ⟨A,h7,h8⟩ := binary_recursion_on_w I[w] f h1 h6
  have h9 : ∀m: Set, m∈w → (A((m,∅)) = m ∧
  ∀n: Set, n∈w → A((m,n⁺))=A((m,n))⁺) := by
    intro m h9
    have ⟨h10,h11⟩ := h8 m h9
    have h12 := f_of_indentity w m h9
    have h13 := (h12 ▸ h10)
    have h14 := (cartesian_product_xy w w m ∅).mpr ⟨h9,zero_in_w⟩
    have h15 := (domain A h7.left.left (m,∅)).mpr (h7.right.left (m,∅) h14)
    have h16: ((m,∅),A((m,∅)))∈A := f_of_x A (m,∅) h7.left h15
    have h17 := h7.left.right (m,∅) m A((m,∅)) ⟨h13,h16⟩
    have h18 := h17.symm
    have h19: ∀n: Set, n∈w → A((m,n⁺))=A((m,n))⁺ := by
      intro n h20
      have h21 := (cartesian_product_xy w w m n).mpr ⟨h9,h20⟩
      have h22 := (domain A h7.left.left (m,n)).mpr (h7.right.left (m,n) h21)
      have h23: ((m,n),A((m,n)))∈A := f_of_x A (m,n) h7.left h22
      have h24: ((m,n⁺),f((A((m,n)),m)))∈A := (h8 m h9).right n A((m,n)) h23
      have h25 := xy_in_A_to_B A (w×w) w h7.right.right (m,n) A((m,n)) h23
      have h26 := (cartesian_product_xy w w A((m,n)) m).mpr ⟨h25.right,h9⟩
      have h27 := (domain f h6.left.left (A((m,n)),m)).mpr (h6.right.left (A((m,n)),m) h26)
      have h28 := f_of_x f (A((m,n)),m) h6.left h27
      have ⟨x,y,h29,h30⟩ := ((h2 (A((m,n)),m) f((A((m,n)),m))).mp h28).right
      have ⟨h31,h32⟩ := (ordered_pair_equiv A((m,n)) m x y).mp h29
      have h33 := h31 ▸ h31 ▸ h30
      have h34: ((m,n⁺),A((m,n))⁺)∈A := h33 ▸ h24
      have h35 := (cartesian_product_xy w w m n⁺).mpr ⟨h9,(succ_in_w n h20)⟩
      have h36 := (domain A h7.left.left (m,n⁺)).mpr (h7.right.left (m,n⁺) h35)
      have h37 := f_of_x A (m,n⁺) h7.left h36
      have h38 := h7.left.right (m,n⁺) A((m,n))⁺ A((m,n⁺)) ⟨h34,h37⟩
      exact h38.symm
    exact ⟨h18,h19⟩
  exact ⟨A,h7,h9⟩

noncomputable def addition_function_op : Set := Classical.choose (addition_function_exists)
notation "Add" => addition_function_op

theorem addition_function : (Add is a function from w×w to w) ∧
∀m: Set, m∈w → (Add((m,∅)) = m ∧
∀n: Set, n∈w → Add((m,n⁺))=Add((m,n))⁺) := by
  exact Classical.choose_spec (addition_function_exists)

noncomputable def addition_op (m n: Set) : Set := Add((m,n))
notation:max m:max"+"n:max => addition_op m n

theorem addition (m n: Set)(h1: m∈w)(h2: n∈w) :
m+∅=m ∧ m+n⁺=(m+n)⁺ := by
  have h3 := (addition_function.right m h1).left
  have h4 := (addition_function.right m h1).right n h2
  exact ⟨h3,h4⟩

notation "one" => ∅⁺
theorem m_plus_one (m : Set) (h1 : m ∈ w) : m + one = m⁺ := by
  have ⟨h2,(h3: m+one=(m+∅)⁺)⟩ := (addition m ∅ h1 zero_in_w)
  have h4 := h2 ▸ h3
  exact h4

theorem addition_in_w (m n: Set) (h1: m∈w)(h2: n∈w) :
m+n∈w := by
  have h3 := (cartesian_product_xy w w m n).mpr ⟨h1,h2⟩
  exact fx_on_A Add (w×w) w addition_function.left (m,n) h3
