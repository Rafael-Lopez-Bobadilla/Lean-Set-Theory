import SetTheory.Arithmetic.addition

theorem multiplication_function_exists :
∃M: Set, (M is a function from w×w to w) ∧
∀m: Set, m∈w → (M((m,∅)) = ∅ ∧
∀n: Set, n∈w → M((m,n⁺))=M((m,n))+m) := by
  let P1 := (fun x y => x∈w ∧ y=∅)
  have ⟨g,h1⟩ := relation_construction w w P1
  have h2: ∀x y z: Set, (x,y)∈g ∧ (x,z)∈g → y=z := by
    intro x y z ⟨h2,h3⟩
    have ⟨h4,h5,h6⟩ := (h1.left x y).mp h2
    have ⟨h7,h8,h9⟩ := (h1.left x z).mp h3
    have h8 := h6 ▸ h9
    exact h8.symm
  have h3: (∀x: Set, x∈w → ∃y: Set, (x,y)∈g) := by
    intro x h3
    have h4 := (cartesian_product_xy w w x ∅).mpr ⟨h3,zero_in_w⟩
    have h5 := (h1.left x ∅).mpr ⟨h4,⟨h3,rfl⟩⟩
    exact ⟨∅,h5⟩
  have h4: g is a function from w to w := ⟨⟨h1.right.left,h2⟩,h3,h1.right⟩
  have hg: ∀m: Set, m∈w → g(m)=∅ := by
    intro m h5
    have h6 := (domain g h4.left.left m).mpr (h4.right.left m h5)
    have h7 := f_of_x g m h4.left h6
    have ⟨h8,h9,h10⟩ := (h1.left m g(m)).mp h7
    exact h10
  let P2 := (fun x y => ∃k m: Set, x=(k,m) ∧ y=k+m)
  have ⟨f,h5⟩ := relation_construction (w×w) w P2
  have h6: (∀x: Set, x∈w×w → ∃y: Set, (x,y)∈f) := by
    intro x h6
    have ⟨k,m,h7,h8,h9⟩ := (cartesian_product w w x).mp h6
    have h10 := (cartesian_product_xy (w×w) w x k+m).mpr ⟨h6,(addition_in_w k m h7 h8)⟩
    have h11 := (h5.left x (k+m)).mpr ⟨h10,⟨k,m,h9,rfl⟩⟩
    exact ⟨k+m,h11⟩
  have h7: ∀x y z: Set, (x,y)∈f ∧ (x,z)∈f → y=z := by
    intro x y z ⟨h7,h8⟩
    have ⟨h9,k,m,h10,h11⟩ := (h5.left x y).mp h7
    have ⟨h12,k2,m2,h13,h14⟩ := (h5.left x z).mp h8
    have h15 := h10 ▸ h13
    have ⟨h16,h17⟩ := (ordered_pair_equiv k m k2 m2).mp h15
    have h18 := h16 ▸ h17 ▸ h11
    have h19 := h18 ▸ h14
    exact h19.symm
  have h8: f is a function from (w×w) to w := ⟨⟨h5.right.left,h7⟩,h6,h5.right⟩
  have hf: ∀k m: Set, (k∈w ∧ m∈w) → f((k,m))=k+m := by
    intro k m ⟨h9,h10⟩
    have h11 := (cartesian_product_xy w w k m).mpr ⟨h9,h10⟩
    have h12 := (domain f h8.left.left (k,m)).mpr (h8.right.left (k,m) h11)
    have h13 := f_of_x f (k,m) h8.left h12
    have ⟨h14,x,y,h15,h16⟩ := (h5.left (k,m) f((k,m))).mp h13
    have ⟨h17,h18⟩ := (ordered_pair_equiv k m x y).mp h15
    have h19 := h17.symm ▸ h18.symm ▸ h16
    exact h19
  have ⟨M,h9,h10⟩ := binary_recursion_on_w g f h4 h8
  have h11: ∀m: Set, m∈w → (M((m,∅)) = ∅ ∧
  ∀n: Set, n∈w → M((m,n⁺))=M((m,n))+m) := by
    intro m h11
    have h12 := (h10 m h11).left
    have h13 := hg m h11
    have h14 := h13 ▸ h12
    have h24: ∀n: Set, n∈w → M((m,n⁺))=M((m,n))+m := by
      intro n h24
      have h25 := (cartesian_product_xy w w m n).mpr ⟨h11,h24⟩
      have h27 := fx_on_A M (w×w) w h9 (m,n) h25
      have h28 := hf M((m,n)) m ⟨h27,h11⟩
      have h29 := (h10 m h11).right n h24
      exact h28 ▸ h29
    exact ⟨h14,h24⟩
  exact ⟨M,h9,h11⟩

noncomputable def multiplication_function_op : Set :=
Classical.choose (multiplication_function_exists)
notation "Mult" => multiplication_function_op

theorem multiplication_function : (Mult is a function from w×w to w) ∧
∀m: Set, m∈w → (Mult((m,∅)) = ∅ ∧
∀n: Set, n∈w → Mult((m,n⁺))=Mult((m,n))+m) := by
  exact Classical.choose_spec (multiplication_function_exists)

noncomputable def multiplication_op (m n: Set) : Set := Mult((m,n))
notation:max m:max"·"n:max => multiplication_op m n

theorem multiplication (m n: Set)(h1: m∈w)(h2: n∈w) :
m·∅=∅ ∧ m·n⁺=(m·n)+m := by
  have h3 := (multiplication_function.right m h1).left
  have h4 := (multiplication_function.right m h1).right n h2
  exact ⟨h3,h4⟩

theorem multiplication_in_w (m n: Set) (h1: m∈w)(h2: n∈w) :
m·n∈w := by
  have h3 := (cartesian_product_xy w w m n).mpr ⟨h1,h2⟩
  exact fx_on_A Mult (w×w) w multiplication_function.left (m,n) h3
