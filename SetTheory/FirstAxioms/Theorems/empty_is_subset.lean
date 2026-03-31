import SetTheory.FirstAxioms.Axioms.Index

theorem empty_is_subset (A : Set) : ∅ ⊆ A := by
  -- Let x be an arbitrary set, and assume x ∈ ∅
  intro x x_in_empty

-- Bring our global axiom into the local context for this specific x
  have x_not_in_empty: x ∉ ∅ := empty_axiom
-- This is a contradiction, since we have both x ∈ ∅ and x ∉ ∅
  contradiction
