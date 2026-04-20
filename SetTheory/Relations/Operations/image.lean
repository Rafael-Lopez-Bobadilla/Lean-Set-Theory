import SetTheory.Relations.Operations.range

theorem image_exists (R A: Set) (h0: R is a relation) :
  ∃image: Set, ∀y: Set, y∈image ↔ ∃x: Set, x∈A ∧ (x,y)∈R := by
  let P: Set → Prop :=  (fun y => ∃x: Set, x∈A ∧ (x,y)∈R)
  have h2: ∀y: Set, P y → y∈ran(R)[h0] := by
    intro y P_y
    have ⟨x, h3, h4⟩ := P_y
    exact (range R h0 y).mpr ⟨x, h4⟩
  exact subset_construction P ran(R)[h0] h2

noncomputable def image_op (R A: Set) (h0: R is a relation) : Set :=
  Classical.choose (image_exists R A h0)
notation:max "["h0"]"R:max"⟦"A"⟧" => image_op R A h0

theorem image (R A: Set) (h0: R is a relation) :
  ∀y: Set, y∈[h0]R⟦A⟧ ↔ ∃x: Set, x∈A ∧ (x,y)∈R :=
  Classical.choose_spec (image_exists R A h0)
