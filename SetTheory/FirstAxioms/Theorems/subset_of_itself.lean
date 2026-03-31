import SetTheory.FirstAxioms.Axioms.Index

theorem subset_of_itself (A : Set) : A ⊆ A := by
  -- Let x be an arbitrary set
  intro x
  -- Assume x ∈ A
  intro h
  -- We need to prove x ∈ A, which is exactly our assumption
  exact h
