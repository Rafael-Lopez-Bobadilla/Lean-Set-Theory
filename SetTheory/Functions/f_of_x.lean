import SetTheory.Relations.Index
import SetTheory.Functions.functions

theorem f_of_x_exists
  (F x: Set) (h0: F is a function) (h1: x∈dom(F)) :
  ∃fx: Set, (x,fx)∈F := by
  have ⟨fx, h2⟩ := (domain F h0.left x).mp h1
  apply Exists.intro fx
  exact h2

open Classical
noncomputable def f_of_x_op (F x: Set) : Set :=
  if h0: (F is a function) ∧ x∈dom(F) then
    choose (f_of_x_exists F x h0.left h0.right)
  else
    ∅
notation:max F:max"("x")" => f_of_x_op F x

theorem f_of_x (F x: Set) (h0: F is a function) (h1: x∈dom(F)):
  (x,F(x))∈F := by
  simp [f_of_x_op, h0,h1]
  exact choose_spec (f_of_x_exists F x h0 h1)
