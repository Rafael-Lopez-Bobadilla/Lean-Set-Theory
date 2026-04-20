import SetTheory.Functions.functions
import SetTheory.Functions.inverse

theorem comp_is_function (F G: Set)
 (h0: F is a function)
 (h1: G is a function)
 (h2:= h0.left)
 (h3:= h1.left) :
 ([h2,h3]F∘G) is a function := by
  let FG: Set := ([h2,h3]F∘G)
  have h4: ∀x y z: Set, (x,y)∈FG ∧ (x,z)∈FG → y=z := by
    intro x y z ⟨h5,h6⟩
    have ⟨t,h7,h8⟩ := (composition_xy F G h2 h3 x y).mp h5
    have ⟨d,h9,h10⟩ := (composition_xy F G h2 h3 x z).mp h6
    have h11 := (h1.right x t d ⟨h7,h9⟩)
    exact (h0.right t y z ⟨h11▸h8,h11▸h10⟩)
  exact ⟨(comp_is_relation F G h2 h3), h4⟩

theorem comp_is_function_AB (F G A B C: Set)
(h0: G is a function from A to B)
(h1: F is a function from B to C)
(h2:= h0.left.left)
(h3:= h1.left.left) :
([h3,h2]F∘G) is a function from A to C := by
  have h4: (∀x: Set, x∈A → ∃y: Set, (x,y)∈[h3,h2]F∘G) := by
    intro x h5
    have ⟨t,h6⟩ := h0.right.left x h5
    have ⟨h7,h8⟩ := xy_in_A_to_B G A B h0.right.right x t h6
    have ⟨y,h9⟩ := h1.right.left t h8
    have h10 := (composition_xy F G h3 h2 x y).mpr ⟨t, h6, h9⟩
    exact ⟨y,h10⟩
  have h5:= (comp_is_function F G h1.left h0.left)
  have h6 := (composition_ABC G F A B C h0.right.right h1.right.right)
  exact ⟨h5,h4,h6⟩

theorem one_to_one_comp (F G: Set)
  (h0: F is one to one)
  (h1: G is one to one)
  (h2:= h0.left.left)
  (h3:= h1.left.left)
  :
  (([h2,h3]F∘G) is one to one) := by
  let FG: Set := [h2,h3]F∘G
  have h6 := comp_is_function F G h0.left h1.left
  have h7: ∀x y z: Set, (x,y)∈FG ∧ (z,y)∈FG → z=x := by
    intro x y z ⟨h8,h9⟩
    have ⟨t,h10⟩ := (composition_xy F G h2 h3 x y).mp h8
    have ⟨r,h11⟩ := (composition_xy F G h2 h3 z y).mp h9
    have h12 := h0.right.right t y r ⟨h10.right,h11.right⟩
    exact h1.right.right x t z ⟨h12▸h10.left,h12▸h11.left⟩
  exact ⟨h6,⟨h6.left,h7⟩⟩

theorem surjection_comp (F G A B C: Set)
  (h0: F maps B onto C)
  (h1: G maps A onto B)
  (h2:= h0.left.left.left)
  (h3:= h1.left.left.left)
  :
  (([h2,h3]F∘G) maps A onto C) := by
  let FG: Set := [h2,h3]F∘G
  have h6 := comp_is_function_AB F G A B C h1.left h0.left
  have h7: ∀y: Set, y∈C → ∃x: Set, (x,y)∈FG := by
    intro y h8
    have ⟨t,h9⟩ := h0.right y h8
    have ⟨h10,h11⟩ := xy_in_A_to_B F B C h0.left.right.right t y h9
    have ⟨x,h12⟩ := h1.right t h10
    have h13 := (composition_xy F G h2 h3 x y).mpr ⟨t,h12,h9⟩
    exact ⟨x,h13⟩
  exact ⟨h6,h7⟩

theorem bijection_comp (F G A B C: Set)
  (h0: F is a bijection from B to C)
  (h1: G is a bijection from A to B)
  (h2:= h0.left.right.left)
  (h3:= h1.left.right.left)
  :
  (([h2,h3]F∘G) is a bijection from A to C) := by
  let FG: Set := [h2,h3]F∘G
  have h4 := one_to_one_comp F G h0.left h1.left
  have h5 := surjection_comp F G A B C h0.right h1.right
  exact ⟨h4,h5⟩
