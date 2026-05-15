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

open Classical
noncomputable def arbitrary_intersection_definition (F : Set) : Set :=
  if h : ∃ E: Set, E ∈ F then
    choose (arbitrary_intersection_exists F h)
  else
    ∅ -- This is the "junk value"
notation:max "⋂"F:max => arbitrary_intersection_definition F

theorem arbitrary_intersection (F : Set) (h : ∃ E, E ∈ F) :
  ∀ x, x ∈ (⋂F) ↔ (∀ y, y ∈ F → x ∈ y) := by
  simp [arbitrary_intersection_definition, h]
  exact choose_spec (arbitrary_intersection_exists F h)

theorem arb_int_test (F x: Set) (F_nonempty : ∃ E : Set, E ∈ F) :
  ∀A: Set, (A∈F ∧ x∈⋂F) → x∈A:= by
  intro A h1
  have h2: ∀y: Set, y∈F → x∈y := (arbitrary_intersection F F_nonempty x).mp h1.right
  exact h2 A h1.left
