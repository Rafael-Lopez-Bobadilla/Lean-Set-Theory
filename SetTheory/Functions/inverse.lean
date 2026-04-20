import SetTheory.Functions.functions

theorem one_to_one_inverse (F: Set) (h0: F is one to one)
  (h1 := h0.left.left) :
  F[h1]⁻¹ is one to one := by
  have sv: F[h1]⁻¹ is single valued := by
    have h2: ∀x y z: Set,
      (x,y)∈F[h1]⁻¹ ∧ (x,z)∈F[h1]⁻¹ → y=z := by
      intro x y z ⟨h3, h4⟩
      have h5: (y,x)∈F := (inverse_xy F x y h1).mp h3
      have h6: (z,x)∈F := (inverse_xy F x z h1).mp h4
      have h7 := h0.right.right y x z ⟨h5,h6⟩
      exact h7 ▸ h7
    exact ⟨(inverse_is_relation F h1), h2⟩
  have sr: F[h1]⁻¹ is single rooted := by
    have h3: ∀x y z: Set, (x,y)∈F[h1]⁻¹ ∧ (z,y)∈F[h1]⁻¹ → z=x := by
      intro x y z ⟨h4,h5⟩
      have h6: (y,x)∈F := (inverse_xy F x y h1).mp h4
      have h7: (y,z)∈F := (inverse_xy F z y h1).mp h5
      have h8 := (h0.left.right y x z ⟨h6,h7⟩)
      exact h8▸h8
    exact ⟨(inverse_is_relation F h1), h3⟩
  exact ⟨sv,sr⟩

theorem bijection_inverse (F A B: Set)
  (h0: F is a bijection from A to B)
  (h1 := h0.left.left.left) :
  F[h1]⁻¹ is a bijection from B to A := by
  have h2 : F[h1]⁻¹ is one to one := (one_to_one_inverse F h0.left)
  have h3 : F[h1]⁻¹ maps B onto A := by
    have h4: F[h1]⁻¹ is a function from B to A := by
      have h5 : ∀x: Set, x∈B → ∃y: Set, (x,y)∈F[h1]⁻¹ := by
        intro x h6
        have ⟨y,h7⟩ := (h0.right.right x h6)
        have h8: (x,y)∈F[h1]⁻¹ := (inverse_xy F x y h1).mpr h7
        exact ⟨y,h8⟩
      have h6: F[h1]⁻¹ is a relation from B to A :=
        (inverse_AB F A B h0.right.left.right.right)
      exact ⟨h2.left,h5,h6⟩
    have h5: ∀y: Set, y∈A → ∃x: Set, (x,y)∈F[h1]⁻¹ := by
      intro y h6
      have ⟨x,h7⟩ := (h0.right.left.right.left y h6)
      have h8: (x,y)∈F[h1]⁻¹ := (inverse_xy F x y h1).mpr h7
      exact ⟨x,h8⟩
    exact ⟨h4,h5⟩
  exact ⟨h2,h3⟩
