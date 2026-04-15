import SetTheory.FirstAxioms.Index
import SetTheory.Relations.ordered_pair
import SetTheory.Relations.ordered_pair_equiv
import SetTheory.Relations.cartesian_product
import SetTheory.Relations.relations
import SetTheory.Relations.relation_domain
import SetTheory.Relations.relation_range

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
  (R S: Set) (h0: R is a relation ∧ S is a relation) : Set :=
  Classical.choose (composition_exists R S h0)
notation:max "["h0"]"R:max"∘"S:max => composition_op R S h0

theorem composition (R S: Set) (h0: R is a relation ∧ S is a relation) :
  ∀d: Set, d∈[h0]R∘S ↔ ∃x y t: Set, (x,t)∈S ∧ (t,y)∈R ∧ d=(x,y) :=
  Classical.choose_spec (composition_exists R S h0)
