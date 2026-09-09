import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.async_driven
import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.progress

namespace CellularAutomatas.LocalHorizon.Fusion

open CellAutomaton

variable {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]
  {q₁ q₂ κ₁ κ₂ : ℕ} [NeZero q₁] [NeZero q₂]
  {domain : Word α → Prop} {middle : Word β → Prop}
  {A : Advice α β} {B : Advice β γ}

/-- One finite CA produces the composed packets. The only runtime connection
between the stages is the first producer's actual initialization event. -/
def source (first : PacketProducer q₁ κ₁ domain A)
    (second : PacketProducer q₂ κ₂ middle B) :
    CellAutomaton (Option α) (Option (Fin (q₁ * q₂) → Option γ)) :=
  let target := PackedTarget.C q₁ second
  let initializer := AsyncFullLine.Driven.stateSource target (Initialization.C first)
  (AsyncFullLine.Driven.projected target initializer).map_project Option.join

omit [Alphabet α] in
theorem source_spec (first : PacketProducer q₁ κ₁ domain A)
    (second : PacketProducer q₂ κ₂ middle B)
    (w : Word α) (hw : domain w) (hmiddle : middle (A w)) (hne : w ≠ [])
    (t p : ℕ) :
    (source first second).comp w t p =
      if ready first second w p t then
        some (SpeedupKx.compress (q₁ * q₂) (word_to_config (B (A w))) p)
      else none := by
  let target := PackedTarget.C q₁ second
  let initial := SpeedupKx.compress q₁ (word_to_config (A w))
  let R := Initialization.release first w
  let initializer := AsyncFullLine.Driven.stateSource target (Initialization.C first)
  have hs : AsyncFullLine.Driven.SourceSpec target initializer (word_to_config w) R
      (fun p => target.embed (initial p)) :=
    AsyncFullLine.Driven.stateSource_spec target (Initialization.C first)
      (word_to_config w) R initial
      (fun t p => Initialization.comp_spec first w hw hne t p)
  have hinput : A w ≠ [] := by
    apply List.ne_nil_of_length_pos
    simpa only [advice_len] using List.length_pos_of_ne_nil hne
  change Option.join ((AsyncFullLine.Driven.projected target initializer).comp w t p) = _
  calc
    Option.join ((AsyncFullLine.Driven.projected target initializer).comp w t p) =
        if simulationHeight first w t p = 0 then none
        else target.comp ⦋initial⦌ (simulationHeight first w t p - 1) p := by
      rw [AsyncFullLine.Driven.projected_comp_encode target initializer
        (word_to_config w) R _ hs]
      simp only [simulationHeight, R]
      split_ifs <;> rfl
    _ = _ := PackedTarget.atHeight_spec second (A w) hmiddle hinput
      (simulationHeight first w t p) p

/-- Normalize only the release bounds, not the advice class: both contracts
may be genuinely promise-relative and both word transformations noncausal. -/
theorem normalized_comp (first : NormalizedProducer q₁ κ₁ domain A)
    (second : NormalizedProducer q₂ κ₂ middle B)
    (hcompatible : ∀ w, domain w → middle (A w)) :
    (A.compose B).IsPacketReadoutOn domain := by
  apply readout_of_ready
    (by have := first.width_ge_two; have := second.width_ge_two; nlinarith)
    (width_le_startup q₁ q₂ κ₁ κ₂) domain (A.compose B)
    (source first.toPacketProducer second.toPacketProducer)
    (ready first.toPacketProducer second.toPacketProducer)
  · intro w _ _ p t u htu hready
    show ready first.toPacketProducer second.toPacketProducer w p u
    exact ready_mono _ _ w p t u htu hready
  · intro w _ _ p
    show ∃ t, ready first.toPacketProducer second.toPacketProducer w p t
    exact ready_eventually _ _ w p
  · intro w hw hne p hp
    show ready first.toPacketProducer second.toPacketProducer w p _
    exact ready_deadline first second w hw (hcompatible w hw) hne p hp
  · intro w hw hne t p
    show (source first.toPacketProducer second.toPacketProducer).comp w t p = _
    simpa only [Advice.compose, Function.comp_apply] using
      source_spec first.toPacketProducer second.toPacketProducer
        w hw (hcompatible w hw) hne t p

end CellularAutomatas.LocalHorizon.Fusion
