import SetTheory.FirstAxioms.Index
import SetTheory.Relations.ordered_pair
import SetTheory.Relations.ordered_pair_equiv
import SetTheory.Relations.cartesian_product
import SetTheory.Relations.relations
import SetTheory.Relations.relation_domain
import SetTheory.Relations.relation_range

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

theorem three_two_sixteen
  (R A r s: Set)
  (h0: R is an equivalence relation on A)
  (h01: r∈A ∧ s∈A) :
  [R,A,⟨h0,h01.left⟩]class(r)=[R,A,⟨h0,h01.right⟩]class(s) ↔
  (r,s)∈R := by
  constructor
  intro h1
  have h2: (r,r)∈R := (h0.right.left).right r h01.left
  have h3 := (equivalence_class R A r ⟨h0, h01.left⟩ r).mpr h2
  have h4 := ((extensionality [R,A,⟨h0,h01.left⟩]class(r)
    [R,A,⟨h0,h01.right⟩]class(s)).mp h1 r).mp h3
  exact (equivalence_class R A s ⟨h0, h01.right⟩ r).mp h4
  intro h2
  apply (extensionality
    [R,A,⟨h0,h01.left⟩]class(r) [R,A,⟨h0,h01.right⟩]class(s)).mpr
  intro x
  constructor
  intro h3
  have h4: (x,r)∈R := (equivalence_class R A r ⟨h0, h01.left⟩ x).mp h3
  have h5: (x,s)∈R := (h0.right.right.right.right) x r s ⟨h4,h2⟩
  exact (equivalence_class R A s ⟨h0, h01.right⟩ x).mpr h5
  intro h4
  have h5: (x,s)∈R := (equivalence_class R A s ⟨h0, h01.right⟩ x).mp h4
  have h6: (s,r)∈R := (h0.right.right.left.right) r s h2
  have h7: (x,r)∈R := (h0.right.right.right.right) x s r ⟨h5,h6⟩
  exact (equivalence_class R A r ⟨h0, h01.left⟩ x).mpr h7
