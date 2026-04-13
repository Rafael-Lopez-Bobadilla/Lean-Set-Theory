import SetTheory.FirstAxioms.Index
import SetTheory.Relations.ordered_pair
import SetTheory.Relations.ordered_pair_equiv
import SetTheory.Relations.cartesian_product
import SetTheory.Relations.relations

theorem relation_domain_exists (R: Set) :
  (R is a relation) → ∃dom: Set, ∀x: Set, x∈dom ↔ ∃y: Set, (x,y)∈R := by
  intro h1
  let P: Set → Prop :=  (fun x => ∃y: Set, (x,y)∈R)
  have h2: ∀x: Set, P x → x∈⋃⋃R := by
    intro x P_x
    have ⟨y, h3⟩ := P_x
    have h4 := relation_on_UUR R h1 (x,y) h3
    have ⟨x2,y2,h5⟩ := (cartesian_product ⋃⋃R ⋃⋃R (x,y)).mp h4
    have h6: x=x2 := ((ordered_pair_equiv x y x2 y2).mp h5.right.right).left
    exact h6 ▸ h5.left
  exact subset_construction P ⋃⋃R h2

noncomputable def relation_domain_op
  (R: Set) (h0: R is a relation) : Set :=
  Classical.choose (relation_domain_exists R h0)
notation:max "dom("R")["h0"]" => relation_domain_op R h0

theorem relation_domain (R: Set) (h0: R is a relation) :
  ∀x: Set, x∈dom(R)[h0] ↔ ∃y: Set, (x,y)∈R :=
  Classical.choose_spec (relation_domain_exists R h0)
