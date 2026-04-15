import SetTheory.FirstAxioms.Index
import SetTheory.Relations.ordered_pair
import SetTheory.Relations.cartesian_product

def relation (R: Set) : Prop :=
  ∀d: Set, d∈R ↔ ∃x y: Set, (x,y)=d
notation:max R "is ""a ""relation" => relation R

def relation_A (R A: Set) : Prop := R⊆A×A
notation:max R "is ""a ""relation ""on "A => relation_A R A

def relation_AB (R A B: Set) : Prop := R⊆A×B
notation:max R "is ""a ""relation ""from "A "to "B => relation_A R A B

def single_rooted (R: Set) : Prop :=
  R is a relation ∧  ∀x y z: Set, (x,y)∈R ∧ (z,y)∈R → z=x
notation:max R "is ""single ""rooted" => single_rooted R

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
