import SetTheory.FirstAxioms.Index
import SetTheory.Relations.CartesianProduct.ordered_pair

private theorem pair_subset_union (x y A B: Set) :
  (x∈A∪B ∧ y∈A∪B) → {x,y}⊆A∪B := by
  intro h1 d h2
  have h3 := (pair_set x y d).mp h2
  cases h3 with
  | inl h4 =>
    exact h4 ▸ h1.left
  | inr h5 =>
    exact h5 ▸ h1.right

theorem cartesian_product_exists (A B: Set) :
  ∃D: Set, ∀d: Set, d∈D ↔ (∃x y: Set, x∈A ∧ y∈B ∧ d=(x,y)) := by
  let P: Set → Prop := (fun d => (∃x y: Set, x∈A ∧ y∈B ∧ d=(x,y)))
  have h1: ∀d: Set, P d → d∈P(P(A∪B)) := by
    intro d P_d
    have ⟨x ,y, h2, h3, h4⟩:= P_d
    have h5: x∈A∪B := (union_of_two A B x).mpr (Or.inl h2)
    have h6: y∈A∪B := (union_of_two A B y).mpr (Or.inr h3)
    have h7: {x,x}⊆A∪B := (pair_subset_union x x A B) ⟨h5, h5⟩
    have h8: {x,y}⊆A∪B := (pair_subset_union x y A B) ⟨h5, h6⟩
    have h9: {x,x}∈P(A∪B) := (power_set (A∪B) {x,x}).mpr h7
    have h10: {x,y}∈P(A∪B) := (power_set (A∪B) {x,y}).mpr h8
    have h11: (x,y)⊆P(A∪B) := by
      intro r h12
      have h13 := (ordered_pair x y r).mp h12
      cases h13 with
      | inl h14 =>
        exact h14 ▸ h9
      | inr h15 =>
        exact h15 ▸ h10
    exact h4 ▸ (power_set P(A∪B) (x,y)).mpr h11
  exact subset_construction P P(P(A∪B)) h1

noncomputable def cartesian_product_op (A B: Set): Set :=
  Classical.choose (cartesian_product_exists A B)
infix:70 "×" => cartesian_product_op

theorem cartesian_product (A B: Set):
  ∀d: Set, d∈A×B ↔ (∃x y: Set, x∈A ∧ y∈B ∧ d=(x,y)) :=
  Classical.choose_spec (cartesian_product_exists A B)
