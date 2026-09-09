import CellularAutomatas.proofs.advice_theory.local_horizon.machine

namespace CellularAutomatas.LocalHorizon

open CellAutomaton

namespace PacketProducer

variable {α β γ : Type} {q κ : ℕ} {domain : Word α → Prop}
  {output : Advice α β}

/-- Relabeling packet slots changes neither events nor their timing. -/
def mapOutput (producer : PacketProducer q κ domain output) (f : β → γ) :
    PacketProducer q κ domain
      ⟨fun w => (output w).map f, by simp⟩ where
  source := producer.source.map_project (Option.map fun packet i => (packet i).map f)
  release := producer.release
  width_ge_two := producer.width_ge_two
  startup_pos := producer.startup_pos
  emits := by
    intro w hw hne t p
    rw [comp_of_map_project, producer.emits w hw hne]
    split
    · simp only [Option.map_some]
      apply congrArg some
      funext i
      simp [SpeedupKx.compress, word_to_config]
    · rfl
  lower := producer.lower
  deadline := producer.deadline

end PacketProducer

namespace Fusion

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- Fusion needs controlled padding releases, including beyond the boundary
packet. Normalization supplies this stronger interface for every readout. -/
structure NormalizedProducer (q κ : ℕ) (domain : Word α → Prop)
    (output : Advice α Γ) extends PacketProducer q κ domain output where
  exterior : ∀ w, domain w → w ≠ [] → ∀ p,
    packetCount q w.length ≤ p → release w p = κ + (q - 1) * p

namespace NormalizedProducer

variable {q κ : ℕ} {domain : Word α → Prop} {output : Advice α Γ}

omit [Alphabet α] [Alphabet Γ] in
theorem upper (producer : NormalizedProducer q κ domain output)
    (w : Word α) (hw : domain w) (hne : w ≠ []) (p : ℕ) :
    producer.release w p ≤ κ + (q - 1) * max (packetCount q w.length) p := by
  by_cases hp : p ≤ packetCount q w.length
  · show producer.release w p ≤ _
    rw [max_eq_left hp]
    exact producer.deadline w hw hne p hp
  · show producer.release w p ≤ _
    rw [max_eq_right (by omega), producer.exterior w hw hne p (by omega)]

end NormalizedProducer

/-- Discard the retained input track only after normalization has certified
occupied packets and supplied exterior padding locally. -/
def ofContract {machine : PacketReadoutMachine α Γ} {domain : Word α → Prop}
    (contract : machine.RTContractOn domain) :
    NormalizedProducer machine.width contract.startup domain contract.readout := by
  let normalized := Normalize.producer contract.startup contract.horizon
    machine.data contract.admissible
  let projected := normalized.mapOutput Prod.snd
  have hout :
      (⟨fun w => (Normalize.annotated contract.horizon machine.data w).map Prod.snd,
        by simp⟩ : Advice α Γ) = contract.readout := by
    apply advice_eq_iff
    funext w
    simp [Normalize.annotated, Advice.annotate, List.map_snd_zip, advice_len,
      PacketReadoutMachine.RTContractOn.readout]
  refine {
    source := projected.source
    release := projected.release
    width_ge_two := projected.width_ge_two
    startup_pos := projected.startup_pos
    emits := by
      intro w hw hne t p
      have hspec := projected.emits w hw hne t p
      have hwout := congrArg (fun A : Advice α Γ => A w) hout
      change (Normalize.annotated contract.horizon machine.data w).map Prod.snd =
        contract.readout w at hwout
      simpa only [hwout] using hspec
    lower := projected.lower
    deadline := projected.deadline
    exterior := ?_
  }
  intro w hw hne p hp
  change Normalize.release contract.startup contract.horizon w p = _
  have hnot : ¬machine.width * p < w.length := by
    intro hlt
    have := (Normalize.position_lt_count w hne p).mpr hlt
    omega
  simp only [Normalize.release, hnot, if_false]

end Fusion
end CellularAutomatas.LocalHorizon
