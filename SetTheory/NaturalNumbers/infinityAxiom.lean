import SetTheory.CongruenceAndPreorder.Index

notation:max x:max"⁺" => x∪{x}

axiom infinity_axiom:
∃infinite: Set, ∅∈infinite ∧ ∀x: Set, x∈infinite → x⁺∈infinite

def isInductive (I: Set) : Prop :=
  ∅∈I ∧ ∀x: Set, x∈I → x⁺∈I
notation I "is ""inductive" => isInductive I
