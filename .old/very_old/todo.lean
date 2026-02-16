import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca
open Classical



/-





--instance : Fintype { w: List α | w.length = n } where
--  elems := (Fintype.elems (Vector α n)).image (λ v => ⟨v.toList, by simp⟩)







noncomputable def t_max' [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ :=
  (t_max ca n).get (by simp_all[h, halts, Option.isSome_iff_ne_none])

def OCA_L { β: Type u } [Coe β CellAutomaton] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellAutomaton.left_independent ca

def OCA_R { β: Type u } [Coe β CellAutomaton] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellAutomaton.right_independent ca








theorem OCA_L_equiv_FCA: ℒ (FCellAutomatons) = ℒ (FCellAutomatons |> OCA_L) := sorry

-- Open problems!
theorem X: ℒ (RT) ≠ ℒ (FCellAutomatons |> t⦃ 2 * n ⦄) := sorry

-/
