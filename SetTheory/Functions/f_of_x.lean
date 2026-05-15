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

theorem fx_fy_equiv (F x y: Set)(h0: F is a function)
(h1: x∈dom(F))(h2: y∈dom(F)):
x=y → F(x)=F(y) := by
  intro h3
  have h4 := f_of_x F x h0 h1
  have h5 := f_of_x F y h0 h2
  have h6 := h0.right x F(x) F(y) ⟨h4,h3▸h5⟩
  exact h6

theorem fx_on_A (F A B: Set)(h0: F is a function from A to B):
∀x: Set, x∈A → F(x)∈B := by
  intro x h1
  have h2 := x_in_dom F A B h0 x h1
  have h3 := f_of_x F x h0.left h2
  have h4 := xy_in_A_to_B F A B h0.right.right x F(x) h3
  exact h4.right
