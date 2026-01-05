import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

variable {α: Type} [Alphabet α]

def ts_prefix_mem (C: CA_rt α): TwoStageAdvice α Bool :=
  {
    β := Bool
    C := C.val.toCellAutomaton
    M := FiniteStateTransducer.M_id Bool
  }


lemma ts_prefix_mem_spec (C: CA_rt α): (ts_prefix_mem C).advice = Advice.prefix_mem C.val.L := by
  apply advice_eq_iff
  funext w

  suffices C.val.trace_rt w = (Advice.prefix_mem C.val.L).f w by
    unfold TwoStageAdvice.advice
    simp only [ts_prefix_mem, FiniteStateTransducer.M_id_scanr_eq, Function.comp_apply, id_eq, this]

  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have (v: Bool) (p: Prop) [Decidable p]: (v = decide p ↔ (v = true ↔ p)) := by grind
    simp [Advice.prefix_mem, this, trace_rt_getElem_i_iff]
    rfl


theorem advice_prefix_mem_is_two_stage_advice (C: CA_rt α):
    (Advice.prefix_mem C.val.L).is_two_stage_advice := by
  use ts_prefix_mem C
  simp [ts_prefix_mem_spec]
