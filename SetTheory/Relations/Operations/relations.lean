import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.Index

def relation (R: Set) : Prop :=
  ∀d: Set, d∈R → ∃x y: Set, (x,y)=d
notation:max R "is ""a ""relation" => relation R

def relation_A (R A: Set) : Prop := R⊆A×A
notation:max R "is ""a ""relation ""on "A => relation_A R A

def relation_AB (R A B: Set) : Prop := R⊆A×B
notation:max R "is ""a ""relation ""from "A "to "B => relation_A R A B

def single_rooted (R: Set) : Prop :=
  R is a relation ∧  ∀x y z: Set, (x,y)∈R ∧ (z,y)∈R → z=x
notation:max R "is ""single ""rooted" => single_rooted R

def single_valued (R: Set) : Prop :=
  R is a relation ∧  ∀x y z: Set, (x,y)∈R ∧ (x,z)∈R → y=z
notation:max R "is ""single ""valued" => single_valued R
