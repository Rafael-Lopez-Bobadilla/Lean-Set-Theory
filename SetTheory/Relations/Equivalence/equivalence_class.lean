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

open Classical
noncomputable def equivalence_class_op (R A y: Set): Set :=
  if h0: (R is an equivalence relation on A) ∧ y∈A then
    choose (equivalence_class_exists R A y h0.left h0.right)
  else
    ∅
notation:max "["R:max","A:max"]class("y")" =>
  equivalence_class_op R A y

theorem equivalence_class (R A y: Set)
  (h0: R is an equivalence relation on A) (h1: y∈A) :
  ∀x: Set, x∈[R,A]class(y) ↔ (x,y)∈R := by
  simp [equivalence_class_op, h0,h1]
  exact choose_spec (equivalence_class_exists R A y h0 h1)
