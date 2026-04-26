import SetTheory.Relations.OrderRelations.definitions

theorem strict_order_exists (R A: Set) (h0: R is a partial order on A) :
∃S: Set, ∀x y: Set, (x,y)∈S ↔ ((x,y)∈R ∧ x≠y) := by
  let P: Set → Set → Prop := (fun x y => (x,y)∈R ∧ x≠y)
  have ⟨S,h1⟩ := relation_contruction A A P
  have h2: ∀x y: Set, (x,y)∈S ↔ P x y:= by
    intro x y
    constructor
    intro h3
    exact ((h1.left x y).mp h3).right
    intro Pxy
    have ⟨h3,h4⟩ := Pxy
    have h5 := h0.left.left.right (x,y) h3
    exact (h1.left x y).mpr ⟨h5,Pxy⟩
  exact ⟨S,h2⟩

noncomputable def stric_order_op (R A: Set)(h0: R is a partial order on A): Set :=
  Classical.choose (strict_order_exists R A h0)
notation:max "strict("R","A")["h0"]" => stric_order_op R A h0

theorem strict_order (R A: Set)(h0: R is a partial order on A) :
∀x y: Set, (x,y)∈strict(R,A)[h0] ↔ (x,y)∈R ∧ x≠y :=
Classical.choose_spec (strict_order_exists R A h0)

theorem trichotomy_law
(R A: Set)
(h0: R is a total order on A)
(h1:= h0.left):
∀x y: Set, (x∈A ∧ y∈A) →
((x,y)∈strict(R,A)[h1] ∧ (y,x)∉strict(R,A)[h1] ∧ x≠y) ∨
((x,y)∉strict(R,A)[h1] ∧ (y,x)∈strict(R,A)[h1] ∧ x≠y) ∨
((x,y)∉strict(R,A)[h1] ∧ (y,x)∉strict(R,A)[h1] ∧ x=y) := by
  let strict: Set := strict(R,A)[h1]
  intro x y ⟨h2, h3⟩
  by_cases x=y
  next h4 =>
    have h5: (x,y)∉strict := by
      intro h6
      have h7 := (strict_order R A h1 x y).mp h6
      exact h7.right h4
    have h6: (y,x)∉strict := by
      intro h7
      have h8 := (strict_order R A h1 y x).mp h7
      exact h8.right h4.symm
    exact Or.inr (Or.inr ⟨h5,h6,h4⟩)
  next h5 =>
    have h6:= h0.right x y ⟨h2,h3⟩
    cases h6 with
    |inl h7 =>
      have h8: (y,x)∉strict := by
        intro h9
        have h10 := (strict_order R A h1 y x).mp h9
        have h11 := h1.right.left.right x y ⟨h7,h10.left⟩
        exact h5 h11
      have h9 := (strict_order R A h1 x y).mpr ⟨h7,h5⟩
      exact Or.inl ⟨h9,h8,h5⟩
    |inr h8 =>
      have h9: (x,y)∉strict := by
        intro h10
        have h11 := (strict_order R A h1 x y).mp h10
        have h12 := h1.right.left.right y x ⟨h8,h11.left⟩
        exact h5 h12.symm
      have h10 : y ≠ x := by
        intro h11
        exact h5 h11.symm
      have h10 := (strict_order R A h1 y x).mpr ⟨h8, h10⟩
      exact Or.inr (Or.inl ⟨h9,h10,h5⟩)
