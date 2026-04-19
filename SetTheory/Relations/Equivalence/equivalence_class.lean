import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.Index
import SetTheory.Relations.Equivalence.definition

theorem equivalence_class_exists
  (R A y: Set) (h0: R is an equivalence relation on A)
  (_h1: y∈A) :
  ∃er: Set, ∀x: Set, x∈er ↔ (x,y)∈R := by
  let P: Set → Prop :=  (fun x => (x,y)∈R)
  have h2: ∀x: Set, P x → x∈A := by
    intro x P_x
    have h3: (x,y)∈A×A := h0.left.right (x,y) P_x
    have h4 := (cartesian_product_xy A A x y).mp h3
    exact h4.left
  exact subset_construction P A h2

noncomputable def equivalence_class_op
  (R A y: Set)
  (h0: R is an equivalence relation on A) (h1: y∈A) : Set :=
  Classical.choose (equivalence_class_exists R A y h0 h1)
notation:max "["R","A","h0","h1"]class("y")" =>
  equivalence_class_op R A y h0 h1

theorem equivalence_class (R A y: Set)
  (h0: R is an equivalence relation on A) (h1: y∈A) :
  ∀x: Set, x∈[R,A,h0,h1]class(y) ↔ (x,y)∈R :=
  Classical.choose_spec (equivalence_class_exists R A y h0 h1)
