import SetTheory.FirstAxioms.Index
import SetTheory.Relations.SetDefinitions.ordered_pair
import SetTheory.Relations.SetDefinitions.relation_domain
import SetTheory.Relations.SetDefinitions.relation_range
import SetTheory.Relations.SetDefinitions.cartesian_product
import SetTheory.Relations.Theorems.ordered_pair_equiv
import SetTheory.Relations.PropDefinitions.Index

theorem inverse_exists (R: Set) (h0: R is a relation) :
  ∃inverse: Set, ∀d: Set, d∈inverse ↔ ∃x y: Set, (x,y)∈R ∧ d=(y,x) := by
  let P: Set → Prop :=  (fun d => ∃x y: Set, (x,y)∈R ∧ d=(y,x))
  have h2: ∀d: Set, P d → d∈ran(R)[h0]×dom(R)[h0] := by
    intro d P_d
    have ⟨x, y, h3⟩ := P_d
    have h4: x∈dom(R)[h0] := (domain R h0 x).mpr ⟨y, h3.left⟩
    have h5: y∈ran(R)[h0] := (range R h0 y).mpr ⟨x, h3.left⟩
    exact (cartesian_product ran(R)[h0] dom(R)[h0] d).mpr ⟨y, x, h5, h4, h3.right⟩
  exact subset_construction P (ran(R)[h0]×dom(R)[h0]) h2

noncomputable def inverse_op
  (R: Set) (h0: R is a relation) : Set :=
  Classical.choose (inverse_exists R h0)
notation:max R"["h0"]⁻¹" => inverse_op R h0

theorem inverse (R: Set) (h0: R is a relation) :
  ∀d: Set, d∈R[h0]⁻¹ ↔ ∃x y: Set, (x,y)∈R ∧ d=(y,x) :=
  Classical.choose_spec (inverse_exists R h0)
