import CellularAutomatas.proofs.advice_theory.bounded_anticipation.characterization
import CellularAutomatas.proofs.advice_theory.local_horizon.examples

namespace CellularAutomatas.BoundedAnticipation.Examples

def unchanged : Advice Bool Bool where
  f := id
  len _ := rfl

theorem unchanged_zero : unchanged.HasAnticipation 0 := by
  intro w i _
  show w[i]? = (w.take (i + 0 + 1))[i]?
  simp only [Nat.add_zero, List.getElem?_take, Nat.lt_succ_self, if_true]

example : unchanged.HasAnticipation 3 :=
  unchanged_zero.mono (by decide)

example : unchanged [] = [] := rfl

open LocalHorizon.Examples

example : lookaheadContract.readout.HasAnticipation 6 :=
  lookaheadContract.hasAnticipation

example : lookaheadContract.readout [false, true, false] = [true, true, false] := by
  decide

example : ¬IsCausal lookaheadContract.readout :=
  lookahead_not_causal

example : lookaheadContract.readout.IsGlobalPacketReadout :=
  Advice.isGlobalPacketReadout_of_boundedAnticipation
    ⟨6, lookaheadContract.hasAnticipation⟩
    (Advice.rt_closed_implies_weak_rt_closed lookaheadContract.rt_closed)

example (hclosed : unchanged.weak_rt_closed) : unchanged.IsGlobalPacketReadout :=
  Advice.isGlobalPacketReadout_of_boundedAnticipation ⟨0, unchanged_zero⟩ hclosed

example {α Γ : Type} [Alphabet α] [Alphabet Γ] {advice : Advice α Γ}
    (trace : advice.DelayedTrace 0) : advice.IsGlobalPacketReadout :=
  Advice.DelayedTrace.isGlobalPacketReadout (distance := 0) trace

example {α Γ : Type} [Alphabet α] [Alphabet Γ] {advice : Advice α Γ}
    (trace : advice.DelayedTrace 0) (word : Word α) (hne : word ≠ []) :
    (DiagonalReadout.source (distance := 0) trace).comp word 2 (0 : ℕ) = none := by
  rw [DiagonalReadout.source_spec (distance := 0) trace word hne 2 0]
  rw [if_neg (by decide)]

example : (selectedSlot 5 2 0).val = 1 := by decide
example : (selectedSlot 5 2 1).val = 0 := by decide
example : (selectedSlot 2 10 0).val = 2 := by decide

example {α Γ : Type} [Alphabet α] [Alphabet Γ]
    (advice : Advice α Γ) (hclosed : advice.weak_rt_closed)
    (hanticipation : advice.HasAnticipation 3) (symbol : α) :
    (advice.delayedTrace_of_weak_rt_closed 3 (by decide) hanticipation hclosed).C.trace
      [symbol] 3 = (advice [symbol])[0]'(by simp) := by
  exact (advice.delayedTrace_of_weak_rt_closed 3 (by decide) hanticipation hclosed).spec
    [symbol] 0 (by simp)

end CellularAutomatas.BoundedAnticipation.Examples
