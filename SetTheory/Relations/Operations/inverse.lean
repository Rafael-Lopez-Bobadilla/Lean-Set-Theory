import SetTheory.Relations.Operations.domain
import SetTheory.Relations.Operations.range

theorem inverse_exists (R: Set) (h0: R is a relation) :
  ∃inverse: Set, ∀d: Set, d∈inverse ↔ ∃x y: Set, (x,y)∈R ∧ d=(y,x) := by
  let P: Set → Prop :=  (fun d => ∃x y: Set, (x,y)∈R ∧ d=(y,x))
  have h2: ∀d: Set, P d → d∈ran(R)×dom(R) := by
    intro d P_d
    have ⟨x, y, h3⟩ := P_d
    have h4: x∈dom(R) := (domain R h0 x).mpr ⟨y, h3.left⟩
    have h5: y∈ran(R) := (range R h0 y).mpr ⟨x, h3.left⟩
    exact (cartesian_product ran(R) dom(R) d).mpr ⟨y, x, h5, h4, h3.right⟩
  exact subset_construction P (ran(R)×dom(R)) h2

open Classical
noncomputable def inverse_op (R: Set) : Set :=
  if h0: R is a relation then
    choose (inverse_exists R h0)
  else
    ∅
notation:max R"⁻¹" => inverse_op R

theorem inverse (R: Set) (h0: R is a relation) :
  ∀d: Set, d∈R⁻¹ ↔ ∃x y: Set, (x,y)∈R ∧ d=(y,x) := by
  simp [inverse_op, h0]
  exact choose_spec (inverse_exists R h0)

theorem inverse_xy (R x y: Set) (h0: R is a relation):
  (x,y)∈R⁻¹ ↔ (y,x)∈R := by
  constructor
  intro h1
  have ⟨x2,y2,h2,h3⟩ := (inverse R h0 (x,y)).mp h1
  have ⟨h4,h5⟩ := (ordered_pair_equiv x y y2 x2).mp h3
  exact h4 ▸ h5 ▸ h2
  intro h2
  exact (inverse R h0 (x,y)).mpr ⟨y,x,h2,rfl⟩

theorem inverse_is_relation (R: Set)(h0: R is a relation) :
  R⁻¹ is a relation := by
  intro d h1
  have ⟨x,y,h2,h3⟩ := (inverse R h0 d).mp h1
  exact ⟨y,x,h3⟩

theorem inverse_AB (R A B: Set)(h0: R is a relation from A to B) :
  R⁻¹ is a relation from B to A := by
  have h1: R⁻¹⊆B×A := by
    intro d h2
    have ⟨x,y,h3,h4⟩ := (inverse R h0.left d).mp h2
    have h5: (x,y)∈A×B := h0.right (x,y) h3
    have h6 := (cartesian_product_xy A B x y).mp h5
    have h7 := (cartesian_product_xy B A y x).mpr ⟨h6.right,h6.left⟩
    exact h4▸h7
  exact ⟨(inverse_is_relation R h0.left),h1⟩
