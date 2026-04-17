import SetTheory.FirstAxioms.Axioms.Index
import SetTheory.Relations.SetDefinitions.ordered_pair

theorem ordered_pair_equiv (a b x y: Set) :
  (a,b)=(x,y) ↔ a=x ∧ b=y := by
  constructor
  intro h1
  have h2: {a,a}∈(a,b) := (ordered_pair a b {a,a}).mpr (Or.inl rfl)
  have h3: {a,a}∈(x,y) := (((extensionality (a,b) (x,y)).mp h1) {a,a}).mp h2
  have h4 := (ordered_pair x y {a,a}).mp h3
  have h5: x=a := by
    cases h4 with
    | inl h6 =>
      have h7: a∈{a,a} := (pair_set a a a).mpr (Or.inl rfl)
      have h8: a∈{x,x} := (((extensionality {a,a} {x,x}).mp h6) a).mp h7
      have h9 := ((pair_set x x a).mp h8)
      have h10:= h9.elim id id
      exact h10 ▸ h10
    | inr h7 =>
      have h8: x∈{x,y} := (pair_set x y x).mpr (Or.inl rfl)
      have h9: x∈{a,a} := (((extensionality {a,a} {x,y}).mp h7) x).mpr h8
      have h10 := ((pair_set a a x).mp h9)
      exact h10.elim id id
  have h6: {a,b}∈(a,b) := (ordered_pair a b {a,b}).mpr (Or.inr rfl)
  have h7: {a,b}∈(x,y) := (((extensionality (a,b) (x,y)).mp h1) {a,b}).mp h6
  have h8 := (ordered_pair x y {a,b}).mp h7
  have h9: b=y := by
    cases h8 with
    | inl h10 =>
      have h11: b∈{a,b} := (pair_set a b b).mpr (Or.inr rfl)
      have h12: b∈{x,x} := (((extensionality {a,b} {x,x}).mp h10) b).mp h11
      have h13 := ((pair_set x x b).mp h12)
      have h14: b=x := h13.elim id id
      have h15: y∈{x,y} := (pair_set x y y).mpr (Or.inr rfl)
      have h16: {x,y}∈(x,y) := (ordered_pair x y {x,y}).mpr (Or.inr rfl)
      have h17: {x,y}∈(a,b) := (((extensionality (a,b) (x,y)).mp h1) {x,y}).mpr h16
      have h18 := (ordered_pair a b {x,y}).mp h17
      cases h18 with
      | inl h19 =>
        have h20: y∈{a,a} := (((extensionality {x,y} {a,a}).mp h19) y).mp h15
        have h21: y=a := ((pair_set a a y).mp h20).elim id id
        have h22 := h5 ▸ h21
        exact h22 ▸ h14
      | inr h20 =>
        have h21: y∈{a,b} := (((extensionality {x,y} {a,b}).mp h20) y).mp h15
        have h22 := ((pair_set a b y).mp h21)
        have h23 := h14 ▸ h14 ▸ h5 ▸ h22
        have h24 := h23.elim id id
        exact h24 ▸ h24
    | inr h11 =>
      have h12: b∈{a,b} := (pair_set a b b).mpr (Or.inr rfl)
      have h13: b∈{x,y} := (((extensionality {a,b} {x,y}).mp h11) b).mp h12
      have h14 := (pair_set x y b).mp h13
      cases h14 with
      | inl h15 =>
        have h16: y∈{x,y} := (pair_set x y y).mpr (Or.inr rfl)
        have h17: y∈{a,b} := (((extensionality {a,b} {x,y}).mp h11) y).mpr h16
        have h18 := (pair_set a b y).mp h17
        have h19 := h15 ▸ h15 ▸ h5 ▸ h18
        have h20 := h19.elim id id
        exact h20 ▸ h20
      | inr h16 =>
        exact h16
  exact ⟨h5 ▸ h5, h9⟩
  intro h1
  apply (extensionality (a,b) (x,y)).mpr
  intro d
  constructor
  intro h2
  have h3 := (ordered_pair a b d).mp h2
  cases h3 with
  | inl h4 =>
    have h5 := h1.left ▸ h4
    exact (ordered_pair x y d).mpr (Or.inl h5)
  | inr h5 =>
    have h6 := h1.right ▸ h1.left ▸ h5
    exact (ordered_pair x y d).mpr (Or.inr h6)
  intro h3
  have h4 := (ordered_pair x y d).mp h3
  cases h4 with
  | inl h5 =>
    have h6 := h1.left ▸ h5
    exact (ordered_pair a b d).mpr (Or.inl h6)
  | inr h5 =>
    have h6 := h1.right ▸ h1.left ▸ h5
    exact (ordered_pair a b d).mpr (Or.inr h6)
