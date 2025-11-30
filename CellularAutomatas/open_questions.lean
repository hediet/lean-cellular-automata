import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs

variable {A: Alphabet}

-- open question: is every rt_closed advice a two-stage advice?
theorem open_question_1 {A Γ: Alphabet} (adv: Advice A Γ) (h: adv.rt_closed): adv.is_two_stage_advice := by
    sorry

theorem lt_eq_rt: CA_rt = CA_lt := by
    sorry
