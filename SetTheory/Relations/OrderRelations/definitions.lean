import SetTheory.Relations.Equivalence.Index

def antisymmetric (R: Set) : Prop :=
R is a relation ∧ ∀x y: Set, ((x,y)∈R ∧ (y,x)∈R) → x=y
notation:max R "is ""antisymmetric" => antisymmetric R

def partial_order (R A: Set): Prop :=
(R is reflexive on A) ∧
(R is antisymmetric) ∧
(R is a transitive relation)
notation:max R "is ""a ""partial ""order ""on "A => partial_order R A

def total_order (R A: Set): Prop :=
(R is a partial order on A) ∧
(∀x y: Set, (x∈A ∧ y∈A) → ((x,y)∈R ∨ (y,x)∈R))
notation:max R "is ""a ""total ""order ""on "A => total_order R A
