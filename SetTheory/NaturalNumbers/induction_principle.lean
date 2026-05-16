import SetTheory.NaturalNumbers.definitions

theorem w_inductive_subset (I: Set) :
I is inductive → w⊆I := by
  intro h1 x h2
  have h3 := (natural_numbers x).mp h2
  exact h3 I h1

theorem subset_is_w (I: Set) :
I⊆w ∧ I is inductive → I=w := by
  intro ⟨h1,h2⟩
  have h3 := w_inductive_subset I h2
  apply (extensionality I w).mpr
  intro x
  constructor
  intro h4
  exact h1 x h4
  intro h5
  exact h3 x h5

theorem created_is_subset (S D: Set)(P: Set → Prop) :
(∀x: Set, x ∈ S ↔ x ∈ D ∧ P x) → S⊆D:= by
  intro h1 s h2
  exact ((h1 s).mp h2).left

theorem induction_principle
(I: Set)(P: Set → Prop)(h0: ∀x: Set, x ∈ I ↔ x ∈ w ∧ P x) :
I is inductive → (∀n: Set, n∈w → P n) := by
  intro h1 n h2
  have h3 := created_is_subset I w P h0
  have h4 := subset_is_w I ⟨h3,h1⟩
  have h6 := h4▸h2
  exact ((h0 n).mp h6).right
