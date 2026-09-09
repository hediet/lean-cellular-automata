import CellularAutomatas.proofs.advice_theory.local_horizon.closure
import CellularAutomatas.proofs.advice_theory.local_horizon.machine
import CellularAutomatas.proofs.advice_theory.local_horizon.prefix_stability
import CellularAutomatas.proofs.advice_theory.marked_prefix.reversal_packets

namespace CellularAutomatas.LocalHorizon.Examples

open CellAutomaton

def oneTickClock : CellAutomaton (Option Bool) Bool where
  Q := Bool × Bool
  δ := fun _ center _ => (false, center.1)
  embed := fun _ => (true, false)
  project := Prod.snd

theorem oneTickClock_state (w : Word Bool) (t : ℕ) (p : ℤ) :
    oneTickClock.nextt w t p = (decide (t = 0), decide (t = 1)) := by
  induction t with
  | zero =>
      show (true, false) = (true, false)
      rfl
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      show (false, (oneTickClock.nextt w t p).1) =
        (decide (t + 1 = 0), decide (t + 1 = 1))
      rw [ih]
      simp

/-- A local one-tick clock, including when the input is empty. The general
interface allows this but never requires it on the empty word. -/
def oneTick : RealizableHorizon Bool (fun _ => True) where
  time := fun _ _ => 1
  clock := oneTickClock
  fires w _ _ t p := congrArg Prod.snd (oneTickClock_state w t p)

def lookahead : CellAutomaton (Option Bool) (Fin 2 → Bool) where
  Q := Option Bool
  δ := fun _ _ right => right
  embed := id
  project := fun symbol _ => symbol.getD false

theorem oneTick_admissible : RTAdmissibleHorizon 2 2 oneTick := by
  refine ⟨by decide, by decide, ?_⟩
  intro w _ _ p _
  show 1 ≤ 2 + (2 - 1) * packetCount 2 w.length
  omega

def lookaheadMachine : PacketReadoutMachine Bool Bool :=
  PacketReadoutMachine.ofHorizon 2 oneTick lookahead (by decide)

def lookaheadContract : lookaheadMachine.RTContractOn (fun _ => True) :=
  PacketReadoutMachine.contractOfHorizon 2 2 oneTick lookahead oneTick_admissible

def longInputContract : lookaheadMachine.RTContractOn (fun w => 2 ≤ w.length) :=
  lookaheadContract.restrict (fun w => 2 ≤ w.length) (fun _ _ => trivial)

example : lookaheadContract.readout [] = [] := by decide
example : lookaheadContract.readout [false] = [false] := by decide
example : lookaheadContract.readout [false, true, false] = [true, true, false] := by decide

example : lookaheadContract.readout.IsGlobalPacketReadout :=
  ⟨lookaheadMachine, lookaheadContract, fun _ _ => rfl⟩

example (w : Word Bool) (hw : 2 ≤ w.length) :
    longInputContract.readout w = lookaheadContract.readout w :=
  longInputContract.readout_eq_on lookaheadContract w hw trivial

example : lookaheadMachine.events.comp [false, true] 1 (0 : ℕ) =
    some (fun _ => true) := by
  rw [lookaheadContract.events_spec [false, true] trivial (by decide) 1 0]
  decide

example : lookaheadMachine.events.comp [false, true] 2 (0 : ℕ) = none := by
  rw [lookaheadContract.events_spec [false, true] trivial (by decide) 2 0]
  decide

open MarkedPrefix.ReversalPackets

/-- A right-going marker wave fires once everywhere only when the marker is
at the origin. Moving the marker right makes the origin never fire. -/
def originMarkerMachine : PacketReadoutMachine (Bool × Bool) Bool where
  width := 2
  width_ge_two := by decide
  clock := (markerSignals Bool).map_project Prod.snd
  data := (markerSignals Bool).map_project fun _ _ => false

def originMarked (v : Word (Bool × Bool)) : Prop :=
  ∃ w : Word Bool, w ≠ [] ∧ v = markedWord w 0

def originMarkerContract : originMarkerMachine.RTContractOn originMarked where
  startup := 2
  startup_ge_width := by decide
  time := fun _ p => p
  fires := by
    intro v hv _ t p
    obtain ⟨w, hne, rfl⟩ := hv
    show ((markerSignals Bool).map_project Prod.snd).comp (markedWord w 0) t p =
      decide (t = p)
    rw [comp_of_map_project, markerSignals_comp w 0 (List.length_pos_of_ne_nil hne)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  deadline := by
    intro v _ _ p hp
    change p < packetCount 2 v.length at hp
    show p ≤ 2 + (2 - 1) * packetCount 2 v.length
    omega

theorem originMarkerMachine_no_global_contract :
    IsEmpty (originMarkerMachine.RTContractOn (fun _ => True)) := by
  constructor
  intro contract
  let malformed := markedWord [false, false] 1
  let firing := contract.time malformed 0
  have hpulse := contract.fires malformed trivial (by decide) firing 0
  change ((markerSignals Bool).map_project Prod.snd).comp malformed firing (0 : ℕ) =
    decide (firing = firing) at hpulse
  rw [comp_of_map_project,
    markerSignals_comp [false, false] 1 (by decide) firing (↑(0 : ℕ) : ℤ)] at hpulse
  have hposition : (↑(0 : ℕ) : ℤ) - (firing : ℤ) = ↑(1 : ℕ) := by
    simpa only [decide_true, decide_eq_true_eq] using hpulse
  omega

example (w : Word Bool) (p : ℕ) (hlength : 2 * (p + 3) ≤ w.length) :
    lookahead.comp w (oneTick.time w p) p =
      lookahead.comp (w.take (2 * (p + 3)))
        (oneTick.time (w.take (2 * (p + 3))) p) p := by
  simpa only [Nat.add_assoc] using
    raw_sample_eq_take oneTick lookahead oneTick_admissible w p hlength

example : lookahead.comp ([] : Word Bool) 0 (0 : ℕ) =
    lookahead.comp (([] : Word Bool).take 1) 0 (0 : ℕ) :=
  comp_eq_take_of_cone lookahead [] 0 0 1 (by decide)

example : readout 2 oneTick lookahead [] = [] := by decide
example : readout 2 oneTick lookahead [false] = [false] := by decide
example : readout 2 oneTick lookahead [false, true] = [true, true] := by decide
example : readout 2 oneTick lookahead [false, true, false] = [true, true, false] := by decide

example : packetCount 3 0 = 0 := by decide
example : packetCount 3 1 = 1 := by decide
example : packetCount 3 3 = 1 := by decide
example : packetCount 3 4 = 2 := by decide

/-- RT admissibility alone does not imply causality, so it cannot imply
unconditional full trace composition. -/
theorem lookahead_not_causal : ¬IsCausal (readout 2 oneTick lookahead) := by
  intro hcausal
  have hprefix := (hcausal [false, true]).2 1
  have hfalse : ([false] : Word Bool) = [true] := by
    exact hprefix
  contradiction

noncomputable def lookahead_rt_closed : (readout 2 oneTick lookahead).rt_closed :=
  LocalHorizon.rt_closed 2 2 oneTick lookahead oneTick_admissible

/-- The first all-border packet bypasses advice and is released at its raw
diagonal, including for a partial final input packet. -/
example : Normalize.release (q := 2) 2 oneTick [false, true, false] 2 = 4 := by
  decide

example :
    (Normalize.producer 2 oneTick lookahead oneTick_admissible).source.comp
      [false, true, false] 4 (2 : ℕ) = some (fun _ => none) := by
  rw [(Normalize.producer 2 oneTick lookahead oneTick_admissible).emits
    [false, true, false] trivial (by decide) 4 2]
  rw [if_pos (by decide)]
  apply congrArg some
  exact Normalize.exterior_packet _ 2 (by rw [advice_len]; decide)

example :
    (Normalize.producer 2 oneTick lookahead oneTick_admissible).source.comp
      [false, true, false] 5 (2 : ℕ) = none := by
  rw [(Normalize.producer 2 oneTick lookahead oneTick_admissible).emits
    [false, true, false] trivial (by decide) 5 2]
  decide

end CellularAutomatas.LocalHorizon.Examples
