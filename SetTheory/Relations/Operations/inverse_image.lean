import SetTheory.Relations.Operations.domain

theorem inverse_image_exists (R A: Set) (h0: R is a relation) :
  ∃image: Set, ∀x: Set, x∈image ↔ ∃y: Set, y∈A ∧ (x,y)∈R := by
  let P: Set → Prop :=  (fun x => ∃y: Set, y∈A ∧ (x,y)∈R)
  have h2: ∀x: Set, P x → x∈dom(R) := by
    intro x P_x
    have ⟨y, h3, h4⟩ := P_x
    exact (domain R h0 x).mpr ⟨y, h4⟩
  exact subset_construction P dom(R) h2

open Classical
noncomputable def inverse_image_op (R A: Set): Set :=
  if h0: R is a relation then
    choose (inverse_image_exists R A h0)
  else
    ∅
notation:max R:max"⁻¹["A"]" => inverse_image_op R A

theorem inverse_image (R A: Set) (h0: R is a relation) :
  ∀x: Set, x∈R⁻¹[A] ↔ ∃y: Set, y∈A ∧ (x,y)∈R := by
  simp [inverse_image_op, h0]
  exact choose_spec (inverse_image_exists R A h0)
