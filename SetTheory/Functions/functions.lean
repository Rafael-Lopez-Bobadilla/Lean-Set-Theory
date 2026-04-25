import SetTheory.Relations.Index

def function (F: Set) : Prop := F is single valued
notation:max F "is ""a ""function" => function F

def function_AB (F A B: Set) :=
  (F is a function) ∧
  (∀x: Set, x∈A → ∃y: Set, (x,y)∈F) ∧
  (F is a relation from A to B)
notation:max F "is ""a ""function ""from "A "to "B =>
  function_AB F A B

def one_to_one (F: Set) : Prop :=
  F is single valued ∧ F is single rooted
notation:max F "is ""one ""to ""one" => one_to_one F

def surjection (F A B: Set) : Prop :=
  (F is a function from A to B) ∧
  ∀y: Set, y∈B → ∃x: Set, (x,y)∈F
notation:max F "maps "A "onto "B => surjection F A B

def bijection (F A B: Set) : Prop :=
  (F is one to one) ∧
  (F maps A onto B)
notation:max F "is ""a ""bijection ""from "A "to "B =>
  bijection F A B

theorem surjection_on_range (F A B: Set)
(h0: F is a function from A to B)
(h1:= h0.left.left):
F maps A onto ran(F)[h1] := by
  have h2: F⊆A×ran(F)[h1] := by
    intro d h3
    have ⟨x,y,h4⟩ := h1 d h3
    have h5:= h0.right.right.right (x,y) (h4▸h3)
    have h6 := (cartesian_product_xy A B x y).mp h5
    have h7 := (range F h1 y).mpr ⟨x,(h4▸h3)⟩
    exact h4▸(cartesian_product_xy A ran(F)[h1] x y).mpr ⟨h6.left,h7⟩
  have h3: ∀y: Set, y∈ran(F)[h1] → ∃x: Set, (x,y)∈F := by
    intro y h4
    exact (range F h1 y).mp h4
  have h4 : F is a function from A to ran(F)[h1] :=
    ⟨h0.left,h0.right.left,⟨h1,h2⟩⟩
  exact ⟨h4,h3⟩
