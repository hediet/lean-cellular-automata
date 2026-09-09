import CellularAutomatas.proofs.advice_theory.bounded_anticipation.defs
import CellularAutomatas.proofs.advice_theory.local_horizon.machine
import CellularAutomatas.proofs.advice_theory.local_horizon.prefix_stability

namespace CellularAutomatas

/-- A fixed-delay origin trace cannot observe beyond its backward light
cone, so its delay is also an anticipation bound. -/
theorem Advice.DelayedTrace.hasAnticipation {α Γ : Type}
    {advice : Advice α Γ} {delay : ℕ} (trace : advice.DelayedTrace delay) :
    advice.HasAnticipation delay := by
  intro w i hi
  have hprefix : i < (w.take (i + delay + 1)).length := by
    simp only [List.length_take]
    omega
  rw [List.getElem?_eq_getElem (by simpa using hi),
    List.getElem?_eq_getElem (by simpa using hprefix)]
  apply congrArg some
  calc
    (advice w)[i]'(by simpa using hi) = trace.C.trace w (delay + i) :=
      (trace.spec w i hi).symm
    _ = trace.C.trace (w.take (i + delay + 1)) (delay + i) :=
      LocalHorizon.comp_eq_take_of_cone trace.C w (delay + i) 0
        (i + delay + 1) (by omega)
    _ = (advice (w.take (i + delay + 1)))[i]'(by simpa using hprefix) :=
      trace.spec (w.take (i + delay + 1)) i hprefix

namespace LocalHorizon

theorem raw_readout_getElem?_take {α Γ : Type} {q κ : ℕ} [NeZero q]
    (horizon : RealizableHorizon α (fun _ => True))
    (data : CellAutomaton (Option α) (Fin q → Γ))
    (hadmissible : RTAdmissibleHorizon q κ horizon)
    (w : Word α) (i : ℕ) (hi : i < w.length) :
    (readout q horizon data w)[i]? =
      (readout q horizon data (w.take (q * (i / q + κ + 1))))[i]? := by
  obtain ⟨hprefix, heq⟩ := raw_readout_getElem_take horizon data hadmissible w i hi
  rw [List.getElem?_eq_getElem (by simpa using hi),
    List.getElem?_eq_getElem (by simpa using hprefix)]
  exact congrArg some heq

end LocalHorizon

/-- Prefix stability of both the clock and data supplies a constant
anticipation bound, independent of the input length and output position. -/
theorem PacketReadoutMachine.RTContractOn.hasAnticipation {α Γ : Type}
    {machine : PacketReadoutMachine α Γ}
    (contract : machine.RTContractOn (fun _ => True)) :
    contract.readout.HasAnticipation (machine.width * (contract.startup + 1)) := by
  intro w i hi
  let packetCutoff := machine.width * (i / machine.width + contract.startup + 1)
  let symbolCutoff := i + machine.width * (contract.startup + 1) + 1
  have hcutoffs : packetCutoff ≤ symbolCutoff := by
    have hdivision := Nat.mod_add_div i machine.width
    have hexpand : packetCutoff =
        machine.width * (i / machine.width) + machine.width * (contract.startup + 1) := by
      dsimp only [packetCutoff]
      ring
    dsimp only [symbolCutoff]
    omega
  have hiPrefix : i < (w.take symbolCutoff).length := by
    simp only [List.length_take]
    dsimp only [symbolCutoff]
    omega
  have hnested : (w.take symbolCutoff).take packetCutoff = w.take packetCutoff := by
    simp only [List.take_take, Nat.min_eq_left hcutoffs]
  have hfull := LocalHorizon.raw_readout_getElem?_take
    contract.horizon machine.data contract.admissible w i hi
  have hprefix := LocalHorizon.raw_readout_getElem?_take
    contract.horizon machine.data contract.admissible (w.take symbolCutoff) i hiPrefix
  change (contract.readout w)[i]? =
    (contract.readout (w.take packetCutoff))[i]? at hfull
  change (contract.readout (w.take symbolCutoff))[i]? =
    (contract.readout ((w.take symbolCutoff).take packetCutoff))[i]? at hprefix
  change (contract.readout w)[i]? = (contract.readout (w.take symbolCutoff))[i]?
  calc
    (contract.readout w)[i]? = (contract.readout (w.take packetCutoff))[i]? := hfull
    _ = (contract.readout (w.take symbolCutoff))[i]? := by
      rw [hnested] at hprefix
      exact hprefix.symm

theorem Advice.IsGlobalPacketReadout.boundedAnticipation {α Γ : Type}
    {advice : Advice α Γ} (hreadout : advice.IsGlobalPacketReadout) :
    advice.BoundedAnticipation := by
  obtain ⟨machine, contract, hspec⟩ := hreadout
  refine ⟨machine.width * (contract.startup + 1), ?_⟩
  intro w i hi
  show (advice w)[i]? =
    (advice (w.take (i + machine.width * (contract.startup + 1) + 1)))[i]?
  rw [← hspec w trivial, ← hspec _ trivial]
  exact contract.hasAnticipation w i hi

end CellularAutomatas
