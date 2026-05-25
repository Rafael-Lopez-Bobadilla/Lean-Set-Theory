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

theorem xy_in_A (R A: Set)(h0: R is a relation on A) :
∀x y: Set, (x,y)∈R → x∈A ∧ y∈A := by
  intro x y h1
  have h2 := h0.right (x,y) h1
  exact (cartesian_product_xy A A x y).mp h2

theorem relation_construction (A B: Set)(P: Set → Set → Prop) :
∃rel: Set,
(∀x y: Set, (x,y)∈rel ↔ (x,y)∈A×B ∧ P x y) ∧
rel is a relation from A to B := by
  let Pd: Set → Prop := (fun d => ∃x y: Set, P x y ∧ d=(x,y))
  have ⟨rel, h1⟩ := subset_axiom (A×B) Pd
  have h2: ∀x y: Set, (x,y)∈rel ↔ (x,y)∈A×B ∧ P x y := by
    intro x y
    constructor
    intro h3
    have ⟨h4,h5⟩ := (h1 (x,y)).mp h3
    have ⟨x2,y2,h6,h7⟩ :=h5
    have ⟨h8,h9⟩ := (ordered_pair_equiv x y x2 y2).mp h7
    have h10 := h8▸h9▸h6
    exact ⟨h4,h10⟩
    intro ⟨h5,h6⟩
    exact (h1 (x,y)).mpr ⟨h5,⟨x,y,h6,rfl⟩⟩
  have h3: rel⊆A×B := by
    intro d h4
    exact ((h1 d).mp h4).left
  have h4: rel is a relation := by
    intro d h5
    have h6 := h3 d h5
    have ⟨x,y,h7,h8,h9⟩ := (cartesian_product A B d).mp h6
    exact ⟨x,y,h9⟩
  exact ⟨rel,h2,⟨h4,h3⟩⟩

theorem cartesian_is_relation (A B: Set):
(A×B) is a relation := by
  intro d h1
  have ⟨x,y,h2,h3,h4⟩ := (cartesian_product A B d).mp h1
  exact ⟨x,y,h4⟩

theorem relation_diff_is_relation
(R A B d: Set)(h0: R is a relation from A to B):
(R\d) is a relation from A to B := by
  have h1: (R\d) is a relation := by
    intro p h1
    have ⟨h2,h3⟩ := (difference R d p).mp h1
    exact h0.left p h2
  have h2: (R\d)⊆A×B := by
    intro p h2
    have ⟨h2,h3⟩ := (difference R d p).mp h2
    exact h0.right p h2
  exact ⟨h1,h2⟩
