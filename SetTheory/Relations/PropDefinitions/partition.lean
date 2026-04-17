import SetTheory.FirstAxioms.Index

def partition (A P: Set) : Prop :=
  (∀d: Set, d∈A → ∃S: Set, S∈P ∧ d∈S) ∧
  ∀S T: Set, S∈P ∧ T∈P ∧ S≠T → S∩T=∅
notation:max P "is ""a ""partition ""of "A => partition A P
