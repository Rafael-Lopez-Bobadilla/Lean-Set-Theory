import SetTheory.Relations.Index

def function (F: Set) : Prop := F is single valued
notation:max F "is ""a ""function" => function F

def function_AB (F A B: Set) :=
  (F is a function) ∧
  (∀x: Set, x∈A → ∃y: Set, (x,y)∈F) ∧
  F⊆A×B
notation:max F "is ""a ""function ""from "A "to "B =>
  function_AB F A B

def one_to_one (F: Set) : Prop :=
  F is single valued ∧ F is single rooted
notation:max F "is ""one ""to ""one" => one_to_one F

def surjection (F A B: Set) : Prop :=
  (F is a function from A to B) ∧
  ∀y: Set, y∈B → ∃x: Set, (x,y)∈B
notation:max F "maps "A "onto "B => surjection F A B

def bijection (F A B: Set) : Prop :=
  (F is one to one) ∧
  (F maps A onto B)
notation:max F "is ""a ""bijection ""from "A "to "B =>
  bijection F A B
