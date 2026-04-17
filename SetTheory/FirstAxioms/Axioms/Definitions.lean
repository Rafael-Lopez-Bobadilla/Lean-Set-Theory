axiom Set : Type
axiom member : Set → Set → Prop
infix:50 " ∈ " => member

def not_member (x y : Set) : Prop := ¬(x ∈ y)
infix:50 " ∉ " => not_member

def subset (A B : Set) : Prop :=
  ∀ x : Set, x ∈ A → x ∈ B
infix:50 " ⊆ " => subset

def not_subset (A B: Set) : Prop := ¬(A⊆B)
infix:50 "⊈" => not_subset
