import SetTheory.Relations.CartesianProduct.Index

def relation (R: Set) : Prop :=
  ∀d: Set, d∈R → ∃x y: Set, d=(x,y)
notation:max R "is ""a ""relation" => relation R

def relation_A (R A: Set) : Prop :=
  R is a relation ∧
  R⊆A×A
notation:max R "is ""a ""relation ""on "A => relation_A R A

def relation_AB (R A B: Set) : Prop :=
  R is a relation ∧
  R⊆A×B
notation:max R "is ""a ""relation ""from "A "to "B => relation_AB R A B

def single_rooted (R: Set) : Prop :=
  R is a relation ∧  ∀x y z: Set, (x,y)∈R ∧ (z,y)∈R → z=x
notation:max R "is ""single ""rooted" => single_rooted R

def single_valued (R: Set) : Prop :=
  R is a relation ∧  ∀x y z: Set, (x,y)∈R ∧ (x,z)∈R → y=z
notation:max R "is ""single ""valued" => single_valued R

theorem xy_in_A_to_B (R A B: Set)(h0: R is a relation from A to B) :
∀x y: Set, (x,y)∈R → x∈A ∧ y∈B := by
  intro x y h1
  have h2 := h0.right (x,y) h1
  exact (cartesian_product_xy A B x y).mp h2
