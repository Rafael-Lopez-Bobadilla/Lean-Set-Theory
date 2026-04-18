import SetTheory.FirstAxioms.Index
import SetTheory.Relations.Equivalence.quotient_set
import SetTheory.Relations.Equivalence.equivalence_class
import SetTheory.Relations.Equivalence.three_two_sixteen
import SetTheory.Relations.Equivalence.partition
import SetTheory.Relations.Equivalence.definition

theorem quotient_is_partition
  (R A: Set) (h0: R is an equivalence relation on A) :
  ([h0]A/R) is a partition of A := by
  have h1: ∀d: Set, d∈A → ∃S: Set, S∈([h0]A/R) ∧ d∈S := by
    intro d h2
    have h3: (d,d)∈R := (h0.right.left.right) d h2
    have h4 := (equivalence_class R A d h0 h2 d).mpr h3
    have h5 := (quotient_set R A h0 ([R,A,h0,h2]class(d))).mpr
      ⟨d, h2, rfl⟩
    exact ⟨[R,A,h0,h2]class(d), h5, h4⟩
  have h2: ∀S T: Set, S∈([h0]A/R) ∧ T∈([h0]A/R) ∧ S≠T → S∩T=∅ := by
    intro S T h3
    apply (extensionality (S∩T) ∅).mpr
    intro x
    constructor
    intro h4
    have ⟨s, h5, h6⟩ := (quotient_set R A h0 S).mp h3.left
    have ⟨t, h7, h8⟩ := (quotient_set R A h0 T).mp h3.right.left
    have h9: x∈S ∧ x∈T := (intersection S T x).mp h4
    have h10 := h6 ▸ h9.left
    have h11 := h8 ▸ h9.right
    have h12: (x,s)∈R := (equivalence_class R A s h0 h5 x).mp h10
    have h13: (x,t)∈R := (equivalence_class R A t h0 h7 x).mp h11
    have h14: (s,x)∈R := h0.right.right.left.right x s h12
    have h15: (s,t)∈R := h0.right.right.right.right s x t ⟨h14, h13⟩
    have h16 := (three_two_sixteen R A s t h0 h5 h7).mpr h15
    have h17 := h6 ▸ h8 ▸ h16
    exact absurd h17 (h3.right.right)
    intro h5
    have h6 := empty_axiom x
    contradiction
  exact ⟨h1, h2⟩
