import SetTheory.Relations.Index
import SetTheory.Functions.functions

theorem f_of_x_exists
  (F x: Set) (h0: F is a function) (h1: x∈dom(F)[h0.left]) :
  ∃fx: Set, (x,fx)∈F := by
  have ⟨fx, h2⟩ := (domain F h0.left x).mp h1
  apply Exists.intro fx
  exact h2

noncomputable def f_of_x_op
  (F x: Set) (h0: F is a function) (h1: x∈dom(F)[h0.left]) : Set :=
  Classical.choose (f_of_x_exists F x h0 h1)
notation:max "["h0","h1"]"F:max"("x")" => f_of_x_op F x h0 h1

theorem f_of_x (F x: Set) (h0: F is a function) (h1: x∈dom(F)[h0.left]):
  (x,[h0,h1]F(x))∈F :=
  Classical.choose_spec (f_of_x_exists F x h0 h1)
