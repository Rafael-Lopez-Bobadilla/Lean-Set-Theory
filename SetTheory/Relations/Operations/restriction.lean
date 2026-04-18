import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.Index
import SetTheory.Relations.Operations.domain
import SetTheory.Relations.Operations.range
import SetTheory.Relations.Operations.relations

theorem restriction_exists (R A: Set) (h0: R is a relation) :
  ∃restriction: Set, ∀d: Set,
  d∈restriction ↔ ∃x y: Set, (x,y)∈R ∧ x∈A ∧ d=(x,y) := by
  let P: Set → Prop :=  (fun d => ∃x y: Set, (x,y)∈R ∧ x∈A ∧ d=(x,y))
  have h2: ∀d: Set, P d → d∈dom(R)[h0]×ran(R)[h0] := by
    intro d P_d
    have ⟨x, y, h3⟩ := P_d
    have h4: x∈dom(R)[h0] := (domain R h0 x).mpr ⟨y, h3.left⟩
    have h5: y∈ran(R)[h0] := (range R h0 y).mpr ⟨x, h3.left⟩
    exact (cartesian_product dom(R)[h0] ran(R)[h0] d).mpr ⟨x, y, h4, h5, h3.right.right⟩
  exact subset_construction P (dom(R)[h0]×ran(R)[h0]) h2

noncomputable def restriction_op
  (R A: Set) (h0: R is a relation) : Set :=
  Classical.choose (restriction_exists R A h0)
notation:max "["h0"]"R"↾"A:max => restriction_op R A h0

theorem restriction (R A: Set) (h0: R is a relation) :
  ∀d: Set, d∈[h0]R↾A ↔ ∃x y: Set, (x,y)∈R ∧ x∈A ∧ d=(x,y) :=
  Classical.choose_spec (restriction_exists R A h0)

theorem restriction_xy (R A: Set)(h0: R is a relation) :
  ∀x y: Set, (x,y)∈[h0]R↾A ↔ (x,y)∈R ∧ x∈A := by
  intro x y
  constructor
  intro h1
  have ⟨x2,y2,h2,h3,h4⟩ := (restriction R A h0 (x,y)).mp h1
  have ⟨h5,h6⟩ := (ordered_pair_equiv x y x2 y2).mp h4
  have h7 := h5 ▸ h6 ▸ h2
  exact ⟨h7, h5 ▸ h3⟩
  intro ⟨h2,h3⟩
  exact (restriction R A h0 (x,y)).mpr ⟨x,y,h2,h3,rfl⟩
