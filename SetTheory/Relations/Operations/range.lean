import SetTheory.Relations.Operations.relation_on_union

theorem range_exists (R: Set) :
  (R is a relation) → ∃ran: Set, ∀y: Set, y∈ran ↔ ∃x: Set, (x,y)∈R := by
  intro h1
  let P: Set → Prop :=  (fun y => ∃x: Set, (x,y)∈R)
  have h2: ∀y: Set, P y → y∈⋃⋃R := by
    intro y P_y
    have ⟨x, h3⟩ := P_y
    have h4 := relation_on_UUR R h1 (x,y) h3
    have h5 := (cartesian_product_xy ⋃⋃R ⋃⋃R x y).mp h4
    exact h5.right
  exact subset_construction P ⋃⋃R h2

noncomputable def range_op
  (R: Set) (h0: R is a relation) : Set :=
  Classical.choose (range_exists R h0)
notation:max "ran("R")["h0"]" => range_op R h0

theorem range (R: Set) (h0: R is a relation) :
  ∀y: Set, y∈ran(R)[h0] ↔ ∃x: Set, (x,y)∈R :=
  Classical.choose_spec (range_exists R h0)
