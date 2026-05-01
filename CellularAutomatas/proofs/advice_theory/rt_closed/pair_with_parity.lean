/-
# `Advice.pair_with_parity` — definition and rt-closedness

`pair_with_parity` zips each input bit with a uniform parity flag:
  `[b₀, b₁, …, bₙ₋₁]` ↦ `[(b₀, p), (b₁, p), …, (bₙ₋₁, p)]`
where `p = (n % 2 = 0)`.

## Proof strategy

`pair_with_parity = identity ⨂ is_even_length`.
Both halves are two-stage, so their zip is two-stage, hence rt-closed.
-/

import CellularAutomatas.proofs.advice_theory.rt_closed.even_length
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_two_stage
import CellularAutomatas.proofs.constructions.trace_id

namespace CellularAutomatas

open CellAutomaton

/-- Pairs each input symbol with the length parity.
    Input: Word Bool.
    Output: Word (Bool × Bool) where the second component is uniform `is_even_length`. -/
def Advice.pair_with_parity : Advice Bool (Bool × Bool) :=
  { f := fun w => w ⨂ (Advice.is_even_length Bool).f w
    len := by intro w; simp [Advice.is_even_length, List.length_zip] }

/-- `pair_with_parity` is a two-stage advice. -/
def pair_with_parity_is_two_stage : Advice.pair_with_parity.is_two_stage_advice := by
  -- identity two-stage: pass the input unchanged via the identity CA
  let id_ts : TwoStageAdvice Bool Bool := ca_to_two_stage (ca_trace_id_word Bool)
  let even_ts := (is_even_length_is_two_stage Bool).witness
  refine ⟨ id_ts ⨂ even_ts, ?_ ⟩
  apply advice_eq_iff
  funext w
  rw [zip_spec id_ts even_ts]
  have h_id : id_ts.advice w = w := by simp [id_ts, ca_to_two_stage_spec]
  have h_even : even_ts.advice w = (Advice.is_even_length Bool).f w := by
    simp [even_ts, (is_even_length_is_two_stage Bool).spec]
  rw [h_id, h_even]
  simp [Advice.pair_with_parity]

/-- `pair_with_parity` is rt-closed. -/
noncomputable def Advice.pair_with_parity_rt_closed :
    Advice.pair_with_parity.rt_closed := by
  rw [← pair_with_parity_is_two_stage.spec]
  exact two_stage_is_rt_closed pair_with_parity_is_two_stage.witness

end CellularAutomatas
