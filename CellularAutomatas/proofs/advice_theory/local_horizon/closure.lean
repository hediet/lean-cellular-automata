import CellularAutomatas.proofs.advice_theory.local_horizon.normalize
import CellularAutomatas.proofs.advice_theory.marked_prefix.eventual_acceptance

namespace CellularAutomatas.LocalHorizon

open CellAutomaton

theorem map_embed_comp_word {α β Γ : Type}
    (C : CellAutomaton (Option α) Γ) (π : β → α)
    (w : Word β) (t : ℕ) (p : ℤ) :
    (C.map_embed (Option.map π)).comp w t p = C.comp (w.map π) t p :=
  congrArg C.project (map_embed_nextt_word C π w t p)

/-- Changing the observed input alphabet does not alter any local event
time; additional target-input information stays on the independent raw track. -/
def lift {α β : Type} {valid : Word α → Prop}
    (horizon : RealizableHorizon α valid) (π : β → α) :
    RealizableHorizon β (fun w => valid (w.map π)) where
  time w := horizon.time (w.map π)
  clock := horizon.clock.map_embed (Option.map π)
  fires w hw hne t p := by
    show (horizon.clock.map_embed (Option.map π)).comp w t p = _
    rw [map_embed_comp_word]
    exact horizon.fires (w.map π) hw (by simpa using hne) t p

theorem admissible_lift {α β : Type} {valid : Word α → Prop}
    {q κ : ℕ} (horizon : RealizableHorizon α valid) (π : β → α)
    (hadmissible : RTAdmissibleHorizon q κ horizon) :
    RTAdmissibleHorizon q κ (lift horizon π) := by
  refine ⟨hadmissible.1, hadmissible.2.1, ?_⟩
  intro w hw hne p hp
  show horizon.time (w.map π) p ≤ κ + (q - 1) * packetCount q w.length
  simpa only [List.length_map] using
    hadmissible.2.2 (w.map π) hw (by simpa using hne) p (by simpa using hp)

theorem readout_lift {α β Γ : Type} [Alphabet β] {valid : Word α → Prop}
    (q : ℕ) [NeZero q] (horizon : RealizableHorizon α valid)
    (data : CellAutomaton (Option α) (Fin q → Γ)) (π : β → α) :
    readout q (lift horizon π) (data.map_embed (Option.map π)) =
      (readout q horizon data).lift π := by
  apply advice_eq_iff
  funext w
  apply List.ext_getElem (by simp)
  intro i hi _
  have hiw : i < w.length := by simpa using hi
  rw [readout_getElem q (lift horizon π) _ w i hiw]
  change (data.map_embed (Option.map π)).comp w
      (horizon.time (w.map π) (i / q)) (↑(i / q) : ℤ)
        ⟨i % q, Nat.mod_lt _ (NeZero.pos q)⟩ =
    (readout q horizon data (w.map π))[i]
  rw [map_embed_comp_word, readout_getElem q horizon data (w.map π) i (by simpa using hiw)]

/-- Every globally valid RT-admissible local horizon gives strongly RT-closed
advice. Normalization supplies pacing and border packets; finite correction
handles the empty word, for which the horizon has no firing obligation. -/
noncomputable def rt_closed {α Γ : Type} [Alphabet α] [Alphabet Γ]
    (q κ : ℕ) [NeZero q]
    (horizon : RealizableHorizon α (fun _ => True))
    (data : CellAutomaton (Option α) (Fin q → Γ))
    (hadmissible : RTAdmissibleHorizon q κ horizon) :
    (readout q horizon data).rt_closed := by
  intro β _ π
  let lifted := lift horizon π
  let liftedData := data.map_embed (Option.map π)
  let producer := Normalize.producer κ lifted liftedData
    (admissible_lift horizon π hadmissible)
  have hadvice : readout q lifted liftedData = (readout q horizon data).lift π :=
    readout_lift q horizon data π
  apply MarkedPrefix.weakRtClosed_of_eventual_simulators
    ((readout q horizon data).lift π) 1
    (fun target => toRtCa (producer.consumer target.toCellAutomaton))
  intro target w hn
  have hne : w ≠ [] := List.ne_nil_of_length_pos hn
  have hfinal := producer.trace_final target.toCellAutomaton w trivial hne
  have hword : Normalize.annotated lifted liftedData w =
      ((readout q horizon data).lift π).annotate w := by
    change (readout q lifted liftedData).annotate w = _
    rw [hadvice]
  have haccepts :
      (toRtCa (producer.consumer target.toCellAutomaton)).accepts w =
        target.accepts (((readout q horizon data).lift π).annotate w) := by
    change (producer.consumer target.toCellAutomaton).trace w (w.length - 1) =
      target.toCellAutomaton.trace
        (((readout q horizon data).lift π).annotate w)
        ((((readout q horizon data).lift π).annotate w).length - 1)
    simpa only [hword, Advice.annotate, List.length_zip, advice_len, min_self] using hfinal
  rw [haccepts]

end CellularAutomatas.LocalHorizon
