import CellularAutomatas.proofs.advice_theory.local_horizon.machine

namespace CellularAutomatas.LocalHorizon.Fusion

open CellAutomaton

variable {α Γ : Type} [Alphabet Γ]

/-- A padded one-shot source already implements the packet-readout interface;
unlike normalization, this adapter imposes no lower pacing bound. -/
theorem isPacketReadoutOn_of_events {q κ : ℕ}
    (hq : 2 ≤ q) (hκ : q ≤ κ) (domain : Word α → Prop) (A : Advice α Γ)
    (source : CellAutomaton (Option α) (Option (Fin q → Option Γ)))
    (hspec : ∀ w, domain w → w ≠ [] → ∀ p : ℕ,
      ∃ τ, (p < packetCount q w.length → τ ≤ κ + (q - 1) * packetCount q w.length) ∧
        ∀ t, source.comp w t p =
          if t = τ then some (SpeedupKx.compress q (word_to_config (A w)) p)
          else none) :
    A.IsPacketReadoutOn domain := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let machine : PacketReadoutMachine α Γ := {
    width := q
    width_ge_two := hq
    clock := source.map_project Option.isSome
    data := source.map_project fun event i =>
      ((event.getD (fun _ => none)) i).getD default
  }
  let time := fun w p =>
    if h : domain w ∧ w ≠ [] then Classical.choose (hspec w h.1 h.2 p) else 0
  have hevent (w) (hw : domain w) (hne : w ≠ []) (t p : ℕ) :
      source.comp w t p =
        if t = time w p then some (SpeedupKx.compress q (word_to_config (A w)) p)
        else none := by
    simpa only [time, dif_pos (And.intro hw hne)] using
      (Classical.choose_spec (hspec w hw hne p)).2 t
  let contract : machine.RTContractOn domain := {
    startup := κ
    startup_ge_width := hκ
    time := time
    fires := by
      intro w hw hne t p
      show (source.map_project Option.isSome).comp w t p = _
      rw [comp_of_map_project, hevent w hw hne t p]
      split <;> simp_all
    deadline := by
      intro w hw hne p hp
      show time w p ≤ _
      simpa only [time, dif_pos (And.intro hw hne)] using
        (Classical.choose_spec (hspec w hw hne p)).1 hp
  }
  refine ⟨machine, contract, ?_⟩
  intro w hw
  apply List.ext_getElem (by simp)
  intro i hi _
  have hiw : i < w.length := by simpa using hi
  have hne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [contract.readout_getElem w i hiw]
  change (((source.comp w (time w (i / q)) (↑(i / q) : ℤ)).getD
    (fun _ => none)) ⟨i % q, Nat.mod_lt _ (NeZero.pos q)⟩).getD default = _
  simp only [hevent w hw hne, ite_true,
    Option.getD_some, SpeedupKx.compress]
  have hindex : (↑(i / q) : ℤ) * q + ↑(i % q) = (i : ℤ) := by
    exact_mod_cast (by
      simpa only [Nat.mul_comm] using Nat.div_add_mod i q :
      (i / q) * q + i % q = i)
  rw [hindex]
  simp [word_to_config, hiw]

/-- Even a producer with a small startup constant is a readout. Enlarging the
contract's upper bound does not delay or otherwise change its events. -/
theorem producer_isPacketReadoutOn {q κ : ℕ} {domain : Word α → Prop}
    {A : Advice α Γ} (producer : PacketProducer q κ domain A) :
    A.IsPacketReadoutOn domain := by
  apply isPacketReadoutOn_of_events producer.width_ge_two
    (Nat.le_add_right q κ) domain A producer.source
  intro w hw hne p
  refine ⟨producer.release w p, ?_, fun t => producer.emits w hw hne t p⟩
  intro hp
  show producer.release w p ≤ q + κ + (q - 1) * packetCount q w.length
  have := producer.deadline w hw hne p hp.le
  omega

end CellularAutomatas.LocalHorizon.Fusion
