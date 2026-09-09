import CellularAutomatas.proofs.advice_theory.local_horizon.defs
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.readout
import CellularAutomatas.proofs.advice_theory.causal

namespace CellularAutomatas.LocalHorizon

open CellAutomaton

/-- The paced, padded form of a local horizon, ready for the asynchronous
consumer. The outer option marks the single event; inner options are genuine
word padding, including the all-border packet at `packetCount q w.length`.
`output` specifies the sampled word, rather than supplying runtime advice. -/
structure PacketProducer {α Γ : Type}
    (q κ : ℕ) (valid : Word α → Prop) (output : Advice α Γ) where
  source : CellAutomaton (Option α) (Option (Fin q → Option Γ))
  release : Word α → ℕ → ℕ
  width_ge_two : 2 ≤ q
  startup_pos : 0 < κ
  emits : ∀ w, valid w → w ≠ [] → ∀ t p : ℕ,
    source.comp w t p =
      if t = release w p then
        some (SpeedupKx.compress q (word_to_config (output w)) p)
      else none
  lower : ∀ w, valid w → w ≠ [] → ∀ p,
    κ + (q - 1) * p ≤ release w p
  deadline : ∀ w, valid w → w ≠ [] → ∀ p,
    p ≤ packetCount q w.length →
      release w p ≤ κ + (q - 1) * packetCount q w.length

namespace PacketProducer

variable {α Γ : Type} {q κ : ℕ} {valid : Word α → Prop}
  {output : Advice α Γ}

/-- Existential event times are selected only in the specification. The
finite source remains the complete implementation. -/
noncomputable def of_exists
    (source : CellAutomaton (Option α) (Option (Fin q → Option Γ)))
    (hq : 2 ≤ q) (hκ : 0 < κ)
    (hspec : ∀ w, valid w → w ≠ [] → ∃ R : ℕ → ℕ,
      (∀ p, κ + (q - 1) * p ≤ R p) ∧
      (∀ p, p ≤ packetCount q w.length →
        R p ≤ κ + (q - 1) * packetCount q w.length) ∧
      ∀ t p : ℕ, source.comp w t p =
        if t = R p then
          some (SpeedupKx.compress q (word_to_config (output w)) p)
        else none) :
    PacketProducer q κ valid output := by
  classical
  let release := fun w =>
    if h : valid w ∧ w ≠ [] then Classical.choose (hspec w h.1 h.2)
    else fun _ => 0
  refine ⟨source, release, hq, hκ, ?_, ?_, ?_⟩
  · intro w hw hne t p
    show source.comp w t p = _
    simpa only [release, dif_pos (And.intro hw hne)] using
      (Classical.choose_spec (hspec w hw hne)).2.2 t p
  · intro w hw hne p
    show κ + (q - 1) * p ≤ release w p
    simpa only [release, dif_pos (And.intro hw hne)] using
      (Classical.choose_spec (hspec w hw hne)).1 p
  · intro w hw hne p hp
    show release w p ≤ κ + (q - 1) * packetCount q w.length
    simpa only [release, dif_pos (And.intro hw hne)] using
      (Classical.choose_spec (hspec w hw hne)).2.1 p hp

def horizon (producer : PacketProducer q κ valid output) :
    RealizableHorizon α valid where
  time := producer.release
  clock := producer.source.map_project Option.isSome
  fires w hw hne t p := by
    show (producer.source.map_project Option.isSome).comp w t p = _
    simp only [comp_of_map_project, producer.emits w hw hne]
    split <;> simp_all

theorem admissible (producer : PacketProducer q κ valid output) (hκ : q ≤ κ) :
    RTAdmissibleHorizon q κ producer.horizon := by
  refine ⟨producer.width_ge_two, hκ, ?_⟩
  intro w hw hne p hp
  show producer.release w p ≤ κ + (q - 1) * packetCount q w.length
  exact producer.deadline w hw hne p hp.le

def data [Alphabet Γ] (producer : PacketProducer q κ valid output) :
    CellAutomaton (Option α) (Fin q → Γ) :=
  producer.source.map_project fun event i =>
    ((event.getD (fun _ => none)) i).getD default

/-- The producer is literally a horizon readout, not merely RT-equivalent
to one. Default values are used only outside the specified event/word. -/
theorem readout_eq [NeZero q] [Alphabet Γ]
    (producer : PacketProducer q κ valid output)
    (w : Word α) (hw : valid w) :
    readout q producer.horizon producer.data w = output w := by
  apply List.ext_getElem (by simp)
  intro i hi _
  have hiw : i < w.length := by simpa using hi
  have hne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [readout_getElem q producer.horizon producer.data w i hiw]
  simp only [data, comp_of_map_project, horizon, producer.emits w hw hne,
    ite_true, Option.getD_some, SpeedupKx.compress]
  have hindex : (↑(i / q) : ℤ) * q + ↑(i % q) = (i : ℤ) := by
    exact_mod_cast (by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i q :
      (i / q) * q + i % q = i)
  rw [hindex]
  simp [word_to_config, hiw]

def consumer [NeZero q] [Alphabet α] [Alphabet Γ]
    (producer : PacketProducer q κ valid output)
    {β : Type} [Alphabet β] (target : CellAutomaton (Option Γ) β) :
    CellAutomaton (Option α) β :=
  MarkedPrefix.LT.consumerCA q producer.source target κ

theorem trace_final [NeZero q] [Alphabet α] [Alphabet Γ]
    (producer : PacketProducer q κ valid output)
    {β : Type} [Alphabet β] (target : CellAutomaton (Option Γ) β)
    (w : Word α) (hw : valid w) (hne : w ≠ []) :
    (producer.consumer target).trace w (w.length - 1) =
      target.trace (output w) (w.length - 1) := by
  have hn : 0 < w.length := List.length_pos_of_ne_nil hne
  apply MarkedPrefix.LT.consumerCA_trace_final_of_deadline q
    producer.source target w (output w) (producer.release w) κ
    producer.width_ge_two producer.startup_pos (by simp) (by simpa using hn)
    (producer.emits w hw hne) (producer.lower w hw hne)
  simpa only [packetCount_of_pos q w.length hn] using producer.deadline w hw hne

/-- Final readout upgrades to full trace composition when the generated
word function is causal. This extra hypothesis is not part of a horizon. -/
theorem trace_rt_eq [NeZero q] [Alphabet α] [Alphabet Γ]
    (producer : PacketProducer q κ (fun _ => True) output)
    {β : Type} [Alphabet β] (target : CellAutomaton (Option Γ) β)
    (hcausal : IsCausal output) :
    (producer.consumer target).trace_rt = target.trace_rt ∘ output := by
  apply (IsCausal.eq_iff _ _ (by simp)
    (hcausal.comp _ _ (by simp))).2
  intro w
  by_cases hne : w = []
  · show ((producer.consumer target).trace_rt w).getLast? =
      (target.trace_rt (output w)).getLast?
    simp [hne]
  · show ((producer.consumer target).trace_rt w).getLast? =
      (target.trace_rt (output w)).getLast?
    have hfinal := producer.trace_final target w trivial hne
    simp only [List.getLast?_eq_getElem?, trace_rt, List.length_map,
      List.length_range, advice_len]
    simpa [List.getElem?_map, List.getElem?_range,
      List.length_pos_of_ne_nil hne] using congrArg some hfinal

end PacketProducer
end CellularAutomatas.LocalHorizon
