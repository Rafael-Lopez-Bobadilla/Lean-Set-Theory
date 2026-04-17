import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.Index
import SetTheory.Relations.Equivalence.definition

theorem equivalence_class_exists
  (R A y: Set) (h0: R is an equivalence relation on A) :
  ∃er: Set, ∀x: Set, x∈er ↔ (x,y)∈R := by
  let P: Set → Prop :=  (fun x => (x,y)∈R)
  have h2: ∀x: Set, P x → x∈A := by
    intro x P_x
    have h3: (x,y)∈A×A := h0.left (x,y) P_x
    have ⟨x2, y2, h4, h5, h6⟩ := (cartesian_product A A (x,y)).mp h3
    have h7 := (ordered_pair_equiv x y x2 y2).mp h6
    exact h7.left ▸ h4
  exact subset_construction P A h2

noncomputable def equivalence_class_op
  (R A y: Set)
  (h0: (R is an equivalence relation on A) ∧ y∈A) : Set :=
  Classical.choose (equivalence_class_exists R A y h0.left)
notation:max "["R","A","h0"]class("y")" => equivalence_class_op R A y h0

theorem equivalence_class (R A y: Set)
  (h0: (R is an equivalence relation on A) ∧ y∈A) :
  ∀x: Set, x∈[R,A,h0]class(y) ↔ (x,y)∈R :=
  Classical.choose_spec (equivalence_class_exists R A y h0.left)
