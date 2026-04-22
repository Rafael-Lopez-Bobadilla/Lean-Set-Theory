import SetTheory.Functions.functions

theorem identity_exists (A: Set) :
∃I: Set, ∀d: Set, d∈I ↔ d∈A×A ∧ ∃x: Set, d=(x,x):= by
 exact subset_axiom (A×A) (fun d => ∃x: Set, d=(x,x))

noncomputable def identity_op (A: Set) : Set :=
  Classical.choose (identity_exists A)
notation:max "I["A:max"]" => identity_op A

theorem identity (A: Set) :
∀d: Set, d∈I[A] ↔ d∈A×A ∧ ∃x: Set, d=(x,x) :=
Classical.choose_spec (identity_exists A)

theorem identity_is_relation (A: Set) : I[A] is a relation := by
  intro d h1
  have ⟨h2,⟨x,h3⟩⟩ := (identity A d).mp h1
  exact ⟨x,x,h3⟩

theorem identity_is_relationAA (A: Set):
I[A] is a relation from A to A := by
  have h1 := identity_is_relation A
  have h2: I[A]⊆A×A := by
    intro d h3
    have h4 := (identity A d).mp h3
    exact h4.left
  exact ⟨h1,h2⟩

theorem identity_is_function (A: Set) :
I[A] is a function := by
  have h1 := identity_is_relation A
  have h2: ∀x y z: Set, (x,y)∈I[A] ∧ (x,z)∈I[A] → y=z := by
    intro x y z ⟨h3,h4⟩
    have ⟨h5,⟨x2,h6⟩⟩ := (identity A (x,y)).mp h3
    have ⟨h7,⟨x3,h8⟩⟩ := (identity A (x,z)).mp h4
    have h9 := (ordered_pair_equiv x y x2 x2).mp h6
    have h10 := (ordered_pair_equiv x z x3 x3).mp h8
    have h11 := h10.left▸h9.left▸h9.right
    exact h10.right▸h11
  exact ⟨h1,h2⟩

theorem identity_is_functionAA (A: Set):
I[A] is a function from A to A := by
  have h1 := identity_is_function A
  have h2 := identity_is_relationAA A
  have h3 : ∀x: Set, x∈A → ∃y: Set, (x,y)∈I[A] := by
    intro x h4
    have h5 := (cartesian_product_xy A A x x).mpr ⟨h4,h4⟩
    have h6 := (identity A (x,x)).mpr ⟨h5,x,rfl⟩
    exact ⟨x,h6⟩
  exact ⟨h1,h3,h2⟩

theorem identity_is_injection (A: Set) :
I[A] is one to one := by
  have h2:  ∀x y z: Set, (x,y)∈I[A] ∧ (z,y)∈I[A] → z=x := by
    intro x y z ⟨h3,h4⟩
    have ⟨h5,⟨x2,h6⟩⟩ := (identity A (x,y)).mp h3
    have ⟨h7,⟨x3,h8⟩⟩ := (identity A (z,y)).mp h4
    have h9 := (ordered_pair_equiv x y x2 x2).mp h6
    have h10 := (ordered_pair_equiv z y x3 x3).mp h8
    have h11 := h9.right▸h10.right▸h10.left
    exact h11▸h9.left▸h9.left
  have h3 : I[A] is a relation := identity_is_relation A
  have h4 : I[A] is a function := identity_is_function A
  exact ⟨h4,⟨h3,h2⟩⟩

 theorem identity_is_surjection (A: Set):
 I[A] maps A onto A := by
  have h5 : ∀y: Set, y∈A → ∃x: Set, (x,y)∈I[A] := by
    intro y h6
    have h7 := (cartesian_product_xy A A y y).mpr ⟨h6,h6⟩
    have h8 := (identity A (y,y)).mpr ⟨h7,y,rfl⟩
    exact ⟨y,h8⟩
  have h6 := identity_is_functionAA A
  exact ⟨h6,h5⟩

theorem identity_is_bijection (A: Set):
I[A] is a bijection from A to A := by
  have h1 := identity_is_injection A
  have h2 := identity_is_surjection A
  exact ⟨h1,h2⟩
