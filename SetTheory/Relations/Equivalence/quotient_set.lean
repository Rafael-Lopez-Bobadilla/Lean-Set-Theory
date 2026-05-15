import SetTheory.Relations.Equivalence.equivalence_class

theorem quotient_set_exists
  (R A: Set) (h0: R is an equivalence relation on A) :
  ∃quotient: Set,
  ∀d: Set, d∈quotient ↔
  ∃x: Set, x∈A ∧ d=[R,A]class(x) := by
  let P: Set → Prop :=
  (fun d => ∃x: Set, x∈A ∧ d=[R,A]class(x))
  have h2: ∀d: Set, P d → d∈P(A) := by
    intro d P_d
    have ⟨x, h3, h4⟩ := P_d
    have h5: d⊆A := by
      intro r h6
      have h7 := h4 ▸ h6
      have h8: (r,x)∈R := (equivalence_class R A x h0 h3 r).mp h7
      have h9: (r,x)∈A×A := (h0.left.right (r,x) h8)
      have h10 := ((cartesian_product_xy A A r x).mp h9)
      exact h10.left
    exact (power_set A d).mpr h5
  exact subset_construction P P(A) h2

open Classical
noncomputable def quotient_set_op (R A: Set) : Set :=
  if h0: R is an equivalence relation on A then
    choose (quotient_set_exists R A h0)
  else
    ∅
notation:max A:max"/"R:max => quotient_set_op R A

theorem quotient_set
  (R A: Set) (h0: R is an equivalence relation on A) :
  ∀d: Set, d∈A/R ↔ ∃x: Set, x∈A ∧ d=[R,A]class(x) := by
  simp [quotient_set_op, h0]
  exact choose_spec (quotient_set_exists R A h0)
