import SetTheory.FirstAxioms.Axioms.Index

theorem arbitrary_intersection (F : Set) (h_nonempty : ∃ A : Set, A ∈ F) :
  ∃ I : Set, ∀ x : Set, x ∈ I ↔ (∀ Y : Set, Y ∈ F → x ∈ Y) := by

  -- 1. Extract an element A from the non-empty family F
  have ⟨A, hA_in_F⟩ := h_nonempty

  -- 2. Use our existential axiom on A
  have h_sep := subset_axiom A (fun x => ∀ Y : Set, Y ∈ F → x ∈ Y)

  -- 3. Extract the resulting set I and its defining property
  have ⟨I, hI⟩ := h_sep

  -- 4. Provide I as the witness for the existential goal
  apply Exists.intro I
  intro x

  -- 5. Prove the if-and-only-if
  constructor

  -- Forward direction (->)
  · intro hx_in_I
    have h_and := (hI x).mp hx_in_I
    exact h_and.right

  -- Backward direction (<-)
  · intro hx_in_all
    apply (hI x).mpr
    constructor
    · -- Left goal: Prove x ∈ A.
      exact hx_in_all A hA_in_F
    · -- Right goal: Prove x belongs to everything in F.
      exact hx_in_all
