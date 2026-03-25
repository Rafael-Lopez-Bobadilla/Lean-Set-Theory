-- 1. We declare an abstract universe of purely ZFC Sets
axiom ZFCSet : Type

-- 2. We declare the concept of membership (returns True or False)
axiom mem : ZFCSet → ZFCSet → Prop

-- 3. We define custom notation so it looks like pen-and-paper math
infix:50 " ∈ " => mem

-- 5. We create our own custom definition: Subset
def subset (A B : ZFCSet) : Prop :=
  ∀ x : ZFCSet, x ∈ A → x ∈ B

infix:50 " ⊆ " => subset

def not_mem (x y : ZFCSet) : Prop := ¬(x ∈ y)

-- And give it the standard math notation
infix:50 " ∉ " => not_mem

-- Postulate a specific set called 'empty'
axiom empty : ZFCSet

-- Assign the standard symbol to it
notation "∅" => empty
