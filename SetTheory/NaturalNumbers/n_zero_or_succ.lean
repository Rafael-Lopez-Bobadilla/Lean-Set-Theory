import SetTheory.NaturalNumbers.induction_principle

theorem n_zero_or_succ (n: Set) :
n∈w → n=∅ ∨ ∃k: Set, n=k⁺ := by
  intro h1
  have h2 := (natural_numbers n).mp h1
  let P := (fun n => n=∅ ∨ ∃k: Set, n=k⁺)
  have ⟨I, h3⟩ := subset_axiom w P
  have h4 := (h3 ∅).mpr ⟨zero_in_w, Or.inl rfl⟩
  have h5: ∀x: Set, x∈I → x⁺∈I := by
    intro x h6
    have ⟨h7,h8⟩ := (h3 x).mp h6
    have h9 := succ_in_w x h7
    exact (h3 x⁺).mpr ⟨h9,Or.inr ⟨x,rfl⟩⟩
  exact induction_principle I P h3 ⟨h4,h5⟩ n h1
