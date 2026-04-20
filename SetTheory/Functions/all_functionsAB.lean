import SetTheory.Relations.Index
import SetTheory.Functions.functions

theorem set_of_all_functions_exists (A B: Set) :
  ∃F: Set, ∀G: Set, G∈F ↔ (G is a function from A to B) := by
  let P: Set → Prop :=  (fun G => G is a function from A to B)
  have h1: ∀G: Set, P G → G∈P(A×B) := by
    intro G P_G
    exact (power_set (A×B) G).mpr P_G.right.right.right
  exact subset_construction P P(A×B) h1

noncomputable def set_of_all_functions_op (A B: Set) : Set :=
  Classical.choose (set_of_all_functions_exists A B)
notation "Maps("A","B")" => set_of_all_functions_op A B

theorem set_of_all_functions (A B: Set) :
  ∀G: Set, G∈Maps(A,B) ↔ G is a function from A to B :=
  Classical.choose_spec (set_of_all_functions_exists A B)
