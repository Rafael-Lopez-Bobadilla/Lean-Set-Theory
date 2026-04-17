import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.Index
import SetTheory.Relations.Operations.relation_on_union
import SetTheory.Relations.Operations.relations

theorem domain_exists (R: Set) :
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

noncomputable def domain_op
  (R: Set) (h0: R is a relation) : Set :=
  Classical.choose (domain_exists R h0)
notation:max "dom("R")["h0"]" => domain_op R h0

theorem domain (R: Set) (h0: R is a relation) :
  ∀x: Set, x∈dom(R)[h0] ↔ ∃y: Set, (x,y)∈R :=
  Classical.choose_spec (domain_exists R h0)
