import SetTheory.FirstAxioms.Index
import SetTheory.Relations.SetDefinitions.ordered_pair
import SetTheory.Relations.SetDefinitions.equivalence_class
import SetTheory.Relations.SetDefinitions.cartesian_product
import SetTheory.Relations.Theorems.ordered_pair_equiv
import SetTheory.Relations.PropDefinitions.Index

theorem quotient_set_exists
  (R A: Set) (h0: R is an equivalence relation on A) :
  ∃quotient: Set,
  ∀d: Set, d∈quotient ↔
  ∃(x: Set)(h1: x∈A), d=[R,A,⟨h0,h1⟩]class(x) := by
  let P: Set → Prop :=
  (fun d => ∃(x: Set)(h1: x∈A), d=[R,A,⟨h0,h1⟩]class(x))
  have h2: ∀d: Set, P d → d∈P(A) := by
    intro d P_d
    have ⟨x, h3, h4⟩ := P_d
    have h5: d⊆A := by
      intro r h6
      have h7 := h4 ▸ h6
      have h8: (r,x)∈R := (equivalence_class R A x ⟨h0,h3⟩ r).mp h7
      have h9: (r,x)∈A×A := (h0.left (r,x) h8)
      have ⟨h,j,h10,h11,h12⟩ := ((cartesian_product A A (r,x)).mp h9)
      have h13 := (ordered_pair_equiv r x h j).mp h12
      exact h13.left ▸ h10
    exact (power_set A d).mpr h5
  exact subset_construction P P(A) h2

noncomputable def quotient_set_op
  (R A: Set) (h0: R is an equivalence relation on A) : Set :=
  Classical.choose (quotient_set_exists R A h0)
notation:max "["h0"]"A:max"/"R:max => quotient_set_op R A h0

theorem quotient_set
  (R A: Set) (h0: R is an equivalence relation on A) :
  ∀d: Set, d∈[h0]A/R ↔ ∃(x: Set)(h1: x∈A), d=[R,A,⟨h0,h1⟩]class(x) :=
  Classical.choose_spec (quotient_set_exists R A h0)
