import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs

namespace CellularAutomatas
variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]

-- open question: is every weak_rt_closed advice a two-stage advice?
def open_question_1 (adv: Advice α Γ) (h: adv.weak_rt_closed): adv.is_two_stage_advice := by
    sorry

theorem lt_eq_rt: CA_rt α = CA_lt α := by
    sorry

-- open question: is every rt-closed advice an lt-advice?
-- (Spatially, an rt-closed advice can be eliminated from any CA_rt; whether it
--  can additionally be *spatially* computed in linear time is open.)
def open_question_rt_closed_implies_lt_advice
    (adv: Advice α Γ) (_h: adv.rt_closed): adv.IsLtAdvice := by
    sorry

-- open question: rt-closed + lt-advice ⟹ two-stage?
-- (Showing rt-closed ⟹ two-stage is hard; the spatial-computability hypothesis
--  of `IsLtAdvice` may be enough to bridge the gap.)
def open_question_rt_closed_and_lt_advice_implies_two_stage
    (adv: Advice α Γ) (_h₁: adv.rt_closed) (_h₂: adv.IsLtAdvice):
    adv.is_two_stage_advice := by
    sorry
