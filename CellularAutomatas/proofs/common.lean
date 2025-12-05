import CellularAutomatas.defs

open Set

theorem ite_eq_of_true {α} { p: Prop } [Decidable p] (h: p) (a b: α): (if p then a else b) = a := by
  simp_all only [↓reduceIte]

theorem min_nat_of_set { p: ℕ → Prop } (h: p 0): min_nat { t | p t } = some 0 := by
  unfold min_nat
  have : ∃ n, n ∈ { t | p t } := by
    use 0
    exact h
  simp_all

theorem set_iff {α: Type*} (p1 p2: α → Prop): {w | p1 w} = {w | p2 w} ↔ (∀ w, p1 w ↔ p2 w) := by
  simp [Set.ext_iff]

-- How to get rid of this?
theorem eq_of_app { α β: Type* } { f g: α → β } (h: f = g) (a: α): f a = g a := by
  rw [h]
