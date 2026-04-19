import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.Index
import SetTheory.Relations.Operations.domain
import SetTheory.Relations.Operations.range
import SetTheory.Relations.Operations.relations

theorem composition_exists
  (R S: Set) (h0: R is a relation ∧ S is a relation) :
  ∃comp: Set, ∀d: Set,
  d∈comp ↔ ∃x y t: Set, (x,t)∈S ∧ (t,y)∈R ∧ d=(x,y) := by
  have h01 := h0.left
  have h02 := h0.right
  let P: Set → Prop :=  (fun d => ∃x y t: Set, (x,t)∈S ∧ (t,y)∈R ∧ d=(x,y))
  have h2: ∀d: Set, P d → d∈dom(S)[h02]×ran(R)[h01] := by
    intro d P_d
    have ⟨x, y, t, h3, h4, h5⟩ := P_d
    have h6: x∈dom(S)[h02] := (domain S h02 x).mpr ⟨t, h3⟩
    have h7: y∈ran(R)[h01] := (range R h01 y).mpr ⟨t, h4⟩
    exact (cartesian_product dom(S)[h02] ran(R)[h01] d).mpr ⟨x, y, h6, h7, h5⟩
  exact subset_construction P (dom(S)[h02]×ran(R)[h01]) h2

noncomputable def composition_op
  (R S: Set) (h0: R is a relation) (h1: S is a relation) : Set :=
  Classical.choose (composition_exists R S ⟨h0,h1⟩)
notation:max "["h0","h1"]"R:max"∘"S:max => composition_op R S h0 h1

theorem composition (R S: Set) (h0: R is a relation)(h1: S is a relation) :
  ∀d: Set, d∈[h0,h1]R∘S ↔ ∃x y t: Set, (x,t)∈S ∧ (t,y)∈R ∧ d=(x,y) :=
  Classical.choose_spec (composition_exists R S ⟨h0,h1⟩)

theorem comp_is_relation (R G: Set)
 (h0: R is a relation)(h1: G is a relation) :
 ([h0,h1]R∘G) is a relation := by
 intro d h2
 have ⟨x,y,t,h3,h4,h5⟩ := (composition R G h0 h1 d).mp h2
 exact ⟨x,y,h5⟩

theorem composition_xy (R G: Set)
  (h0: R is a relation) (h1: G is a relation) :
  ∀x y: Set, (x,y)∈[h0,h1]R∘G ↔
  ∃t: Set, (x,t)∈G ∧ (t,y)∈R := by
  intro x y
  constructor
  intro h2
  have ⟨x2,y2,t,h3,h4,h5⟩ := (composition R G h0 h1 (x,y)).mp h2
  have ⟨h6,h7⟩ := (ordered_pair_equiv x y x2 y2).mp h5
  exact ⟨t,h6▸h3,h7▸h4⟩
  intro ⟨t,h4,h5⟩
  exact (composition R G h0 h1 (x,y)).mpr ⟨x,y,t,h4,h5,rfl⟩

theorem composition_ABC (R G A B C: Set)
(h0: R is a relation from A to B)
(h1: G is a relation from B to C)
(h2:= h0.left)(h3:=h1.left) :
([h3,h2]G∘R) is a relation from A to C := by
  have h4: [h3,h2]G∘R ⊆ A×C := by
    intro d h5
    have ⟨x,y,t,h6,h7,h8⟩ := (composition G R h3 h2 d).mp h5
    have h11 := xy_in_A_to_B R A B h0 x t h6
    have h12 := xy_in_A_to_B G B C h1 t y h7
    exact h8 ▸ (cartesian_product_xy A C x y).mpr ⟨h11.left,h12.right⟩
  exact ⟨(comp_is_relation G R h3 h2),h4⟩
