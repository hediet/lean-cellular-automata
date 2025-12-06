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
import CellularAutomatas.proofs.is_two_stage_of_rt_closed_and_prefix_stable

namespace results

variable {α: Type u} [Alphabet α]
variable {Γ: Type u} [Alphabet Γ]

theorem result_middle_not_two_stage_advice:
    ¬ Advice.is_two_stage_advice (Advice.middle α) := by
  exact middle_not_two_stage_advice

theorem result_advice_prefixes_in_L_is_two_stage_advice:
    ∀ C ∈ CA_rt α, Advice.is_two_stage_advice (Advice.prefixes_in_L C.L) := by
  intro C h
  exact advice_prefixes_in_L_is_two_stage_advice ⟨ C, h ⟩

theorem result_is_two_stage_of_rt_closed_and_prefix_stable:
    ∀ adv: Advice α Γ, adv.rt_closed ∧ adv.prefix_stable → adv.is_two_stage_advice := by
  intro adv h
  exact is_two_stage_of_rt_closed_and_prefix_stable adv h.1 h.2
