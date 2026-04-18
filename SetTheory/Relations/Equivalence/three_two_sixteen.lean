import SetTheory.FirstAxioms.Index
import SetTheory.Relations.Operations.Index
import SetTheory.Relations.CartesianProduct.Index
import SetTheory.Relations.Equivalence.equivalence_class

theorem three_two_sixteen
  (R A r s: Set)
  (h0: R is an equivalence relation on A)
  (h01: r∈A) (h02: s∈A) :
  [R,A,h0,h01]class(r)=[R,A,h0,h02]class(s) ↔
  (r,s)∈R := by
  let rclass: Set := [R,A,h0,h01]class(r)
  let sclass : Set := [R,A,h0,h02]class(s)
  constructor
  intro h1
  have h2: (r,r)∈R := (h0.right.left).right r h01
  have h3 := (equivalence_class R A r h0 h01 r).mpr h2
  have h4 := ((extensionality rclass sclass).mp h1 r).mp h3
  exact (equivalence_class R A s h0 h02 r).mp h4
  intro h2
  apply (extensionality rclass sclass).mpr
  intro x
  constructor
  intro h3
  have h4: (x,r)∈R := (equivalence_class R A r h0 h01 x).mp h3
  have h5: (x,s)∈R := (h0.right.right.right.right) x r s ⟨h4,h2⟩
  exact (equivalence_class R A s h0 h02 x).mpr h5
  intro h4
  have h5: (x,s)∈R := (equivalence_class R A s h0 h02 x).mp h4
  have h6: (s,r)∈R := (h0.right.right.left.right) r s h2
  have h7: (x,r)∈R := (h0.right.right.right.right) x s r ⟨h5,h6⟩
  exact (equivalence_class R A r h0 h01 x).mpr h7
