import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.Index
import SetTheory.Relations.Operations.domain
import SetTheory.Relations.Operations.relations

theorem inverse_image_exists (R A: Set) (h0: R is a relation) :
  ∃image: Set, ∀x: Set, x∈image ↔ ∃y: Set, y∈A ∧ (x,y)∈R := by
  let P: Set → Prop :=  (fun x => ∃y: Set, y∈A ∧ (x,y)∈R)
  have h2: ∀x: Set, P x → x∈dom(R)[h0] := by
    intro x P_x
    have ⟨y, h3, h4⟩ := P_x
    exact (domain R h0 x).mpr ⟨y, h4⟩
  exact subset_construction P dom(R)[h0] h2

noncomputable def inverse_image_op (R A: Set) (h0: R is a relation) : Set :=
  Classical.choose (inverse_image_exists R A h0)
notation:max "["h0"]"R:max"⁻¹⟦"A"⟧" => inverse_image_op R A h0

theorem inverse_image (R A: Set) (h0: R is a relation) :
  ∀x: Set, x∈[h0]R⁻¹⟦A⟧ ↔ ∃y: Set, y∈A ∧ (x,y)∈R :=
  Classical.choose_spec (inverse_image_exists R A h0)
