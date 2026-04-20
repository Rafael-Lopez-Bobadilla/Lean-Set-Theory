import SetTheory.Relations.Operations.Index

def reflexive (R A: Set) : Prop := (R is a relation on A) ∧ ∀x: Set, x∈A → (x,x)∈R
notation:max R "is ""reflexive ""on "A => reflexive R A

def symmetric (R: Set) : Prop := R is a relation ∧ ∀x y: Set, (x,y)∈R → (y,x)∈R
notation:max R "is ""symmetric" => symmetric R

def transitive_relation (R: Set) : Prop :=
  R is a relation ∧ ∀x y z: Set, (x,y)∈R ∧ (y,z)∈R → (x,z)∈R
notation:max R "is ""a ""transitive " "relation" => transitive_relation R

def equivalence_relation (R A: Set) : Prop :=
  (R is a relation on A) ∧
  (R is reflexive on A) ∧
  (R is symmetric) ∧
  (R is a transitive relation)
notation:max R "is ""an ""equivalence ""relation ""on "A => equivalence_relation R A
