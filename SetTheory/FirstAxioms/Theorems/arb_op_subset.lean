import SetTheory.FirstAxioms.Axioms.Index
import SetTheory.FirstAxioms.Theorems.arbitrary_intersection
import SetTheory.FirstAxioms.Theorems.arbitrary_union

theorem subset_imp_union_subset (F G: Set) : F⊆G → ⋃F ⊆ ⋃G := by
  intro h1
  intro x h2
  have h3: ∃ A, A ∈ F ∧ x ∈ A := arbitrary_union.mp h2
  have ⟨A, h4, h5⟩ := h3
  have h6: A∈G := h1 A h4
  exact arbitrary_union.mpr ⟨A, h6, h5⟩

theorem subset_imp_int_subset
  (F G A: Set) (h0 : F ⊆ G) (h1 : A ∈ F) :
  have h2 := h0 A h1
  (⋂[⟨A, h2⟩] G) ⊆ (⋂[⟨A, h1⟩] F) := by
  intro h2I x h3
  have h4 : ∀ y : Set, y ∈ G → x ∈ y := arbitrary_intersection.mp h3
  have h5 : ∀ y : Set, y ∈ F → x ∈ y := by
    intro y h6
    have h7 := h0 y h6
    exact h4 y h7
  exact arbitrary_intersection.mpr h5
