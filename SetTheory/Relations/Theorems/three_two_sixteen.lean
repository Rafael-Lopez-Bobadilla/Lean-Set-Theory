import SetTheory.FirstAxioms.Index
import SetTheory.Relations.Theorems.ordered_pair_equiv
import SetTheory.Relations.SetDefinitions.ordered_pair
import SetTheory.Relations.SetDefinitions.cartesian_product
import SetTheory.Relations.SetDefinitions.equivalence_class
import SetTheory.Relations.PropDefinitions.Index

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
