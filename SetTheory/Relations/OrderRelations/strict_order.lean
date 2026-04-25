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
(h1:= h0.left)
(strict := strict(R,A)[h1]) :
∀x y: Set,
((x,y)∈strict ∧ (y,x)∉strict ∧ x≠y) ∨
((x,y)∉strict ∧ (y,x)∈strict ∧ x≠y) ∨
((x,y)∉strict ∧ (y,x)∉strict ∧ x=y) := by
  intro x y

  sorry
