import SetTheory.NaturalNumbers.infinityAxiom

theorem x_in_x_succ (x: Set) :
x∈x⁺ := by
  have h1 := (singleton x x).mpr rfl
  exact (union_of_two x {x} x).mpr (Or.inr h1)

def natural_number (x: Set) : Prop :=
∀I: Set, (I is inductive) → x∈I
notation x "is ""a ""natural ""number" => natural_number x

theorem w_exists :
∃w: Set, ∀x: Set, x∈w ↔ x is a natural number:= by
  have ⟨I, h1⟩ := infinity_axiom
  let P := (fun n => n is a natural number)
  have h3: ∀x: Set, P x → x∈I := by
    intro x Px
    exact Px I h1
  exact subset_construction P I h3

noncomputable def natural_numbers_set : Set :=
  Classical.choose (w_exists)
notation "w" => natural_numbers_set

theorem natural_numbers :
∀n: Set, n∈w ↔ (n is a natural number) := by
  exact Classical.choose_spec (w_exists)

theorem zero_in_w : ∅∈w := by
  have h1: ∀I: Set, I is inductive → ∅∈I := by
    intro I h2
    exact h2.left
  exact (natural_numbers ∅).mpr h1

theorem succ_in_w : ∀x: Set, x∈w → x⁺∈w := by
  intro x h3
  have h4 := (natural_numbers x).mp h3
  have ⟨I, h5⟩ := infinity_axiom
  have h6 := h4 I h5
  have h7 := h5.right x h6
  have h8: ∀D: Set, (D is inductive) → x⁺∈D := by
    intro D h9
    have h10 := h4 D h9
    exact h9.right x h10
  exact (natural_numbers x⁺).mpr h8

theorem w_is_inductive : w is inductive := by
  exact ⟨zero_in_w, succ_in_w⟩

theorem zero_not_succ (n: Set) : ∅≠n⁺ := by
  intro h1
  have h2 := x_in_x_succ n
  have h3 := empty_axiom n
  have h4 := h1 ▸ h2
  exact h3 h4
