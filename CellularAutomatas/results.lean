import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs
import CellularAutomatas.proofs.middle_not_two_stage
import CellularAutomatas.proofs.advice_prefixes_in_L_rt_closed

namespace results

variable {α: Type u} [Alphabet α]

theorem result_middle_not_two_stage_advice:
    ¬ Advice.is_two_stage_advice (Advice.middle α) := by
  exact middle_not_two_stage_advice

theorem result_advice_prefixes_in_L_is_two_stage_advice (C: CA_rt α) :
    Advice.is_two_stage_advice (Advice.prefixes_in_L C.val.L) := by
  exact advice_prefixes_in_L_is_two_stage_advice C
