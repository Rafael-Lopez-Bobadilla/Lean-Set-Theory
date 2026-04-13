import SetTheory.FirstAxioms.Index
import SetTheory.Relations.ordered_pair
import SetTheory.Relations.ordered_pair_equiv
import SetTheory.Relations.cartesian_product
import SetTheory.Relations.relations

theorem relation_range_exists (R: Set) :
  (R is a relation) → ∃ran: Set, ∀y: Set, y∈ran ↔ ∃x: Set, (x,y)∈R := by
  intro h1
  let P: Set → Prop :=  (fun y => ∃x: Set, (x,y)∈R)
  have h2: ∀y: Set, P y → y∈⋃⋃R := by
    intro y P_y
    have ⟨x, h3⟩ := P_y
    have h4 := relation_on_UUR R h1 (x,y) h3
    have ⟨x2,y2,h5⟩ := (cartesian_product ⋃⋃R ⋃⋃R (x,y)).mp h4
    have h6: y=y2 := ((ordered_pair_equiv x y x2 y2).mp h5.right.right).right
    exact h6 ▸ h5.right.left
  exact subset_construction P ⋃⋃R h2

noncomputable def relation_range_op
  (R: Set) (h0: R is a relation) : Set :=
  Classical.choose (relation_range_exists R h0)
notation:max "ran("R")["h0"]" => relation_range_op R h0

theorem relation_range (R: Set) (h0: R is a relation) :
  ∀y: Set, y∈ran(R)[h0] ↔ ∃x: Set, (x,y)∈R :=
  Classical.choose_spec (relation_range_exists R h0)
