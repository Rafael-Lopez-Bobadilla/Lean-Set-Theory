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
  have ⟨M,h9,h10⟩ := binary_recursion_on_w g f h4 h8
  have h11: ∀m: Set, m∈w → (M((m,∅)) = ∅ ∧
  ∀n: Set, n∈w → M((m,n⁺))=M((m,n))+m) := by
    intro m h11
    have h12: ((m,∅),g(m))∈M := (h10 m h11).left
    have h13 := (domain g h4.left.left m).mpr (h4.right.left m h11)
    have h14: (m,g(m))∈g := f_of_x g m h4.left h13
    have h15 := (h1.left m g(m)).mp h14
    have ⟨h16,h17⟩ := h15.right
    have h18 := (cartesian_product_xy w w m ∅).mpr ⟨h11,zero_in_w⟩
    have h19 := (domain M h9.left.left (m,∅)).mpr (h9.right.left (m,∅) h18)
    have h20: ((m,∅),M((m,∅)))∈M := f_of_x M (m,∅) h9.left h19
    have h21 := h9.left.right (m,∅) g(m) M((m,∅)) ⟨h12,h20⟩
    have h22 := h17 ▸ h21
    have h23: M((m,∅))=∅ := h22.symm
    have h24: ∀n: Set, n∈w → M((m,n⁺))=M((m,n))+m := by
      intro n h24
      have h25 := (cartesian_product_xy w w m n).mpr ⟨h11,h24⟩
      have h26 := (domain M h9.left.left (m,n)).mpr (h9.right.left (m,n) h25)
      have h27: ((m,n),M((m,n)))∈M := f_of_x M (m,n) h9.left h26
      have h28: ((m,n⁺),f((M((m,n)),m)))∈M := (h10 m h11).right n M((m,n)) h27
      have h29 := fx_on_A M (w×w) w h9 (m,n) h25
      have h30 := (cartesian_product_xy w w M((m,n)) m).mpr ⟨h29,h11⟩
      have h31 := (domain f h8.left.left (M((m,n)),m)).mpr (h8.right.left (M((m,n)),m) h30)
      have h32 := f_of_x f (M((m,n)),m) h8.left h31
      have ⟨h33,k,r,h34,h35⟩ := (h5.left (M((m,n)),m) f((M((m,n)),m))).mp h32
      have ⟨h36,h37⟩ := (ordered_pair_equiv M((m,n)) m k r).mp h34
      have h38 := h36 ▸ h36 ▸ h37 ▸ h37 ▸ h35
      have h39 := h38 ▸ h28
      have h40 := (cartesian_product_xy w w m n⁺).mpr ⟨h11,succ_in_w n h24⟩
      have h41 := (domain M h9.left.left (m,n⁺)).mpr (h9.right.left (m,n⁺) h40)
      have h42 := f_of_x M (m,n⁺) h9.left h41
      have h43 := (h9.left.right (m,n⁺) M((m,n))+m M((m,n⁺)) ⟨h39,h42⟩)
      exact h43.symm
    exact ⟨h23,h24⟩
  exact ⟨M,h9,h11⟩
