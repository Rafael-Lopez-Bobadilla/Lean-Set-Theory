import SetTheory.FirstAxioms.Axioms.Definitions
-- 4. We state the Axiom of Extensionality
-- "Two sets are equal if and only if they have the same elements"
axiom extensionality (A B : ZFCSet) :
  (∀ x : ZFCSet, x ∈ A ↔ x ∈ B) → A = B

-- The Axiom: For any set x, x is not in ∅
axiom empty_ax { x : ZFCSet } : x ∉ ∅
