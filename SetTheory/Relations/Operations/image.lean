import SetTheory.Relations.Operations.range

theorem image_exists (R A: Set) (h0: R is a relation) :
  ∃image: Set, ∀y: Set, y∈image ↔ ∃x: Set, x∈A ∧ (x,y)∈R := by
  let P: Set → Prop :=  (fun y => ∃x: Set, x∈A ∧ (x,y)∈R)
  have h2: ∀y: Set, P y → y∈ran(R) := by
    intro y P_y
    have ⟨x, h3, h4⟩ := P_y
    exact (range R h0 y).mpr ⟨x, h4⟩
  exact subset_construction P ran(R) h2

open Classical
noncomputable def image_op (R A: Set) : Set :=
  if h0: R is a relation then
    choose (image_exists R A h0)
  else
    ∅
notation:max R:max"["A"]" => image_op R A

theorem image (R A: Set) (h0: R is a relation) :
  ∀y: Set, y∈R[A] ↔ ∃x: Set, x∈A ∧ (x,y)∈R := by
  simp [image_op, h0]
  exact choose_spec (image_exists R A h0)
