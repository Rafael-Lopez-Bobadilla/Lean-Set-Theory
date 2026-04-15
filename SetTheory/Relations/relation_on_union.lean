import SetTheory.FirstAxioms.Index
import SetTheory.Relations.ordered_pair
import SetTheory.Relations.cartesian_product
import SetTheory.Relations.relations

theorem relation_on_UUR (R: Set) :
  (R is a relation) → R ⊆ ⋃⋃R × ⋃⋃R := by
  intro h1 d h2
  have ⟨x, y, h3⟩ := (h1 d).mp h2
  have h4: {x,y}∈(x,y) := (ordered_pair x y {x,y}).mpr (Or.inr rfl)
  have h5: {x,y}∈⋃R := (arbitrary_union R {x,y}).mpr ⟨d, h2, h3▸h4⟩
  have h6: x∈{x,y} := (pair_set x y x).mpr (Or.inl rfl)
  have h7: y∈{x,y} := (pair_set x y y).mpr (Or.inr rfl)
  have h8: x∈⋃⋃R := (arbitrary_union ⋃R x).mpr ⟨{x,y}, h5, h6⟩
  have h9: y∈⋃⋃R := (arbitrary_union ⋃R y).mpr ⟨{x,y}, h5, h7⟩
  exact (cartesian_product ⋃⋃R ⋃⋃R d).mpr ⟨x, y, h8, h9, h3▸h3⟩
