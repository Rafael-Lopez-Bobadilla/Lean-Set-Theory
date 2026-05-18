import SetTheory.NaturalNumbers.induction_principle
import SetTheory.NaturalNumbers.n_zero_or_succ

def transitive_set (A: Set) : Prop :=
∀x: Set, x∈A → x⊆A
notation A "is ""transitive" => transitive_set A

theorem transitive_union (x: Set):
x is transitive → ⋃x⁺=x := by
  intro h0
  apply (extensionality ⋃x⁺ x).mpr
  intro d
  constructor
  intro h1
  have ⟨A,h2,h3⟩ := (arbitrary_union x⁺ d).mp h1
  have h4 := (union_of_two x {x} A).mp h2
  cases h4 with
  |inl h5 =>
    exact h0 A h5 d h3
  |inr h6 =>
    have h7 := (singleton x A).mp h6
    exact h7 ▸ h3
  intro h2
  have h3 := (singleton x x).mpr rfl
  have h4 := (union_of_two x {x} x).mpr (Or.inr h3)
  exact (arbitrary_union x⁺ d).mpr ⟨x,h4,h2⟩

theorem natural_is_transitive (n: Set) :
n∈w → n is transitive := by
  intro h1
  have h2 := (natural_numbers n).mp h1
  let P := (fun x => x is transitive)
  have ⟨I,h3⟩ := subset_axiom w P
  have h4: ∀x: Set, x∈∅ → x⊆∅ := by
    intro x h5
    have h6 := empty_axiom x
    contradiction
  have h5: ∀d: Set, d∈I → d⁺∈I := by
    intro d h6
    have ⟨h7,h8⟩ := (h3 d).mp h6
    have h9 := succ_in_w d h7
    have h10: ∀x: Set, x∈d⁺ → x⊆d⁺ := by
      intro x h11 r h12
      have h13 := (union_of_two d {d} x).mp h11
      cases h13 with
      |inl h14 =>
        have h15: r∈d := (h8 x h14) r h12
        exact (union_of_two d {d} r).mpr (Or.inl h15)
      |inr h15 =>
        have h16: x=d := (singleton d x).mp h15
        exact (union_of_two d {d} r).mpr (Or.inl (h16▸h12))
    exact (h3 d⁺).mpr ⟨h9,h10⟩
  have h6 := (h3 ∅).mpr ⟨zero_in_w, h4⟩
  exact induction_principle I P h3 ⟨h6,h5⟩ n h1

theorem successor_equiv (n m: Set) :
(m∈w ∧ n∈w ∧ m⁺=n⁺) → m=n := by
  intro ⟨h1,h2,(h3: m⁺=n⁺)⟩
  have h4 := natural_is_transitive m h1
  have h5 := natural_is_transitive n h2
  have h6: ⋃m⁺=m := transitive_union m h4
  have h7: ⋃n⁺=n := transitive_union n h5
  have h8 := (arbitrary_union_equiv m⁺ n⁺ h3)
  exact h6 ▸ h8 ▸ h7

theorem w_is_transitive : w is transitive := by
  have h1: ∀x: Set, x∈w → x⊆w := by
    intro x h1
    let P := (fun x => x⊆w)
    have ⟨I,h2⟩ := subset_axiom w P
    have h3 := (h2 ∅).mpr ⟨zero_in_w,empty_is_subset w⟩
    have h4: ∀n: Set, n∈I → n⁺∈I := by
      intro n h5
      have ⟨h6,h7⟩ := (h2 n).mp h5
      have h8: n⁺⊆w := by
        intro d h9
        have h10 := (union_of_two n {n} d).mp h9
        cases h10 with
        |inl h11 =>
          exact h7 d h11
        |inr h12 =>
          have h13 := (singleton n d).mp h12
          exact (h13▸h6)
      exact (h2 n⁺).mpr ⟨succ_in_w n h6,h8⟩
    exact induction_principle I P h2 ⟨h3,h4⟩ x h1
  exact h1
