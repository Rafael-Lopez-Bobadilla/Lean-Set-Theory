import SetTheory.FirstAxioms.Axioms.Index
import SetTheory.FirstAxioms.Theorems.subset_construction

theorem arbitrary_intersection_exists (F : Set) (F_nonempty : ∃ A : Set, A ∈ F) :
  ∃ D : Set, ∀ x : Set, x ∈ D ↔ (∀ y : Set, y ∈ F → x ∈ y) := by
  have ⟨A, A_in_F⟩ := F_nonempty
  let P: Set → Prop := fun x => ∀ y : Set, y ∈ F → x ∈ y
  have px_imp_x_in_A : ∀ x : Set, P x → x ∈ A := by
    intro x P_x
    exact (P_x A) A_in_F
  exact subset_construction P A px_imp_x_in_A

noncomputable def arbitrary_intersection_definition
  (F : Set) (F_nonempty : ∃ E : Set, E ∈ F) : Set :=
  Classical.choose (arbitrary_intersection_exists F F_nonempty)
notation "⋂[" h "] " F => arbitrary_intersection_definition F h

theorem arbitrary_intersection (F: Set) (F_nonempty : ∃ E : Set, E ∈ F) (x: Set):
  x ∈ (⋂[F_nonempty] F) ↔ ∀ y : Set, y ∈ F → x ∈ y := by
  exact Classical.choose_spec (arbitrary_intersection_exists F F_nonempty) x

theorem arb_int_test (F x: Set) (F_nonempty : ∃ E : Set, E ∈ F) :
  A∈F ∧ x∈(⋂[F_nonempty]F) → x∈A:= by
  intro h_and
  have in_all_of_F := (arbitrary_intersection F F_nonempty x).mp h_and.right
  exact in_all_of_F A h_and.left
