import CellularAutomatas.proofs.ca_rt_utils
import CellularAutomatas.proofs.constructions.composition.composition
import CellularAutomatas.proofs.constructions.composition.compose_two_stage
import CellularAutomatas.proofs.constructions.trace_id

namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

open CellAutomaton


theorem two_stage_rt_closed (adv: TwoStageAdvice α Γ):
    adv.advice.rt_closed := by
  rw [advice_rt_closed_iff]
  intro C
  rw [ℒ_CA_rt_iff]

  let x := ((TwoStageAdvice.from_CA_rt C) ⊚ ((ca_to_two_stage (ca_trace_id_word α)) ⨂ adv))
  let C' := fix_empty ([] ∈ C.val.L) x.to_CA_rt

  use C'

  constructor
  · simp [C']

  ext w


  simp [C']
  rw [Set.mem_setOf_eq]

  by_cases h_empty: w = []
  · simp [h_empty]

  simp [h_empty]
  simp [x]

  unfold TwoStageAdvice.L
  rw [Set.mem_setOf_eq]

  have : ↑C ∈ CA_rt (α ⨉ Γ) := by simp
  rw [elemL_iff_trace_rt this]

  simp [h_empty]
