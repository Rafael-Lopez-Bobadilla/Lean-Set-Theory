import SetTheory.FirstAxioms.Axioms.Index

theorem subset_refl (A : ZFCSet) : A ⊆ A := by
  -- Let x be an arbitrary set
  intro x
  -- Assume x ∈ A
  intro h
  -- We need to prove x ∈ A, which is exactly our assumption
  exact h

theorem empty_subset (A : ZFCSet) : ∅ ⊆ A := by
  -- Let x be an arbitrary set, and assume x ∈ ∅
  intro x x_in_empty

-- Bring our global axiom into the local context for this specific x
  have x_not_in_empty: x ∉ ∅ := empty_ax
-- This is a contradiction, since we have both x ∈ ∅ and x ∉ ∅
  contradiction
