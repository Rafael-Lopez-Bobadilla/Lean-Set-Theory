import SetTheory.FirstAxioms.Index
import SetTheory.Relations.ordered_pair
import SetTheory.Relations.cartesian_product
import SetTheory.Relations.relations

private theorem relation_domain_exists (R: Set) :
  (R is a relation) → ∃dom: Set, ∀x: Set, x∈dom ↔ ∃y: Set, (x,y)∈R := by
  intro h1
  let P: Set → Prop :=  (fun x => ∃y: Set, (x,y)∈R)
  have h2: ∀x: Set, P x → x∈⋃⋃R := by
    intro x P_x
    have ⟨y, h3⟩ := P_x
    have h4 := relation_on_UUR R h1 (x,y) h3
    --have ⟨a, b, h5⟩ := (cartesian_product ⋃⋃R ⋃⋃R (x,y)).mp h4
    sorry
  --have h2 := subset_construction ⋃⋃R
  sorry
