import SetTheory.CongruenceAndPreorder.Index

notation:max x:max"⁺" => x∪{x}

axiom infinity_axiom:
∃infinite: Set, ∅∈infinite ∧ ∀x: Set, x∈infinite → x⁺∈infinite

def isInductive (I: Set) : Prop :=
  ∅∈I ∧ ∀x: Set, x∈I → x⁺∈I
notation I "is ""inductive" => isInductive I

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

theorem w_is_inductive : w is inductive := by
  have h1: ∀I: Set, I is inductive → ∅∈I := by
    intro I h2
    exact h2.left
  have h2: ∀x: Set, x∈w → x⁺∈w := by
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
  have h3:= (natural_numbers ∅).mpr h1
  exact ⟨h3,h2⟩

theorem w_inductive_subset (I: Set) :
I is inductive → w⊆I := by
  intro h1 x h2
  have h3 := (natural_numbers x).mp h2
  exact h3 I h1

theorem w_subset_quiv (I: Set) :
I⊆w ∧ I is inductive → I=w := by
  intro ⟨h1,h2⟩
  have h3 := w_inductive_subset I h2
  apply (extensionality I w).mpr
  intro x
  constructor
  intro h4
  exact h1 x h4
  intro h5
  exact h3 x h5

theorem n_zero_or_succ (n: Set) :
n∈w → n=∅ ∨ ∃k: Set, n=k⁺ := by
  intro h1
  have h2 := (natural_numbers n).mp h1
  let P := (fun n => n=∅ ∨ ∃k: Set, n=k⁺)
  have ⟨I, h3⟩ := subset_axiom w P

  sorry
