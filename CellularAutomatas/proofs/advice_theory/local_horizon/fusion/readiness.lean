import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.ready_packets
import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.event_readout

namespace CellularAutomatas.LocalHorizon.Fusion

open CellAutomaton

def lanesReady {q : ℕ} (times : Fin q → ℕ) (height : ℕ) : Prop :=
  0 < height ∧ ∀ i, times i ≤ q * (height - 1)

instance {q : ℕ} (times : Fin q → ℕ) (height : ℕ) :
    Decidable (lanesReady times height) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _))

theorem lanesReady_mono {q : ℕ} (times : Fin q → ℕ) {h k : ℕ}
    (hle : h ≤ k) (hready : lanesReady times h) : lanesReady times k := by
  refine ⟨by have := hready.1; omega, ?_⟩
  intro i
  calc
    times i ≤ q * (h - 1) := hready.2 i
    _ ≤ q * (k - 1) := Nat.mul_le_mul_left q (Nat.sub_le_sub_right hle 1)

theorem lanesReady_of_generation {q : ℕ} (times : Fin q → ℕ) (d h : ℕ)
    (hh : d + 1 ≤ h) (htimes : ∀ i, times i ≤ q * d) :
    lanesReady times h := by
  refine ⟨by omega, ?_⟩
  intro i
  calc
    times i ≤ q * d := htimes i
    _ ≤ q * (h - 1) := Nat.mul_le_mul_left q (by omega)

theorem lanesReady_eventually {q : ℕ} (hq : 1 ≤ q)
    (times : Fin q → ℕ) (height : ℕ → ℕ)
    (hprogress : ∀ d, ∃ t, d + 1 ≤ height t) :
    ∃ t, lanesReady times (height t) := by
  let d := Finset.univ.sup times
  obtain ⟨t, ht⟩ := hprogress d
  refine ⟨t, lanesReady_of_generation times d (height t) ht ?_⟩
  intro i
  calc
    times i ≤ d := Finset.le_sup (Finset.mem_univ i)
    _ ≤ q * d := by nlinarith

/-- The proof chooses the first ready time; the implementation detects the
same transition using the existing finite one-shot controller. -/
theorem first_ready_event {α β : Type}
    (source : CellAutomaton α (Option β)) (input : Config α) (p : ℤ)
    (ready : ℕ → Prop) [DecidablePred ready] (value : β)
    (hmono : ∀ t u, t ≤ u → ready t → ready u)
    (heventually : ∃ t, ready t)
    (hspec : ∀ t, source.comp ⦋input⦌ t p =
      if ready t then some value else none) :
    ∃ τ, ready τ ∧ (∀ t, ready t → τ ≤ t) ∧
      ∀ t, (MarkedPrefix.LT.FirstOutput.C source).comp ⦋input⦌ t p =
        if t = τ then some value else none := by
  let τ := Nat.find heventually
  have hτ : ready τ := Nat.find_spec heventually
  have hleast : ∀ t, ready t → τ ≤ t := fun _ h => Nat.find_le h
  refine ⟨τ, hτ, hleast, ?_⟩
  intro t
  show (MarkedPrefix.LT.FirstOutput.C source).comp ⦋input⦌ t p = _
  apply MarkedPrefix.LT.FirstOutput.comp_spec
  intro u
  show source.comp ⦋input⦌ u p = _
  rw [hspec]
  have hiff : ready u ↔ τ ≤ u :=
    ⟨hleast u, fun hu => hmono τ u hu hτ⟩
  simp only [hiff]

open Classical in
/-- Package a persistent, correct local readiness signal as a readout.
The readiness predicate and its deadline occur only in the proof. -/
theorem readout_of_ready {α β : Type} [Alphabet β] {q κ : ℕ}
    (hq : 2 ≤ q) (hκ : q ≤ κ)
    (domain : Word α → Prop) (output : Advice α β)
    (source : CellAutomaton (Option α) (Option (Fin q → Option β)))
    (ready : Word α → ℕ → ℕ → Prop)
    (hmono : ∀ w, domain w → w ≠ [] → ∀ p t u,
      t ≤ u → ready w p t → ready w p u)
    (heventually : ∀ w, domain w → w ≠ [] → ∀ p, ∃ t, ready w p t)
    (hdeadline : ∀ w, domain w → w ≠ [] → ∀ p,
      p < packetCount q w.length → ready w p (κ + (q - 1) * packetCount q w.length))
    (hspec : ∀ w, domain w → w ≠ [] → ∀ t p : ℕ,
      source.comp w t p =
        if ready w p t then
          some (SpeedupKx.compress q (word_to_config (output w)) p) else none) :
    output.IsPacketReadoutOn domain := by
  classical
  apply isPacketReadoutOn_of_events hq hκ domain output
    (MarkedPrefix.LT.FirstOutput.C source)
  intro w hw hne p
  obtain ⟨τ, _, hleast, hevent⟩ := first_ready_event source (word_to_config w) p
    (ready w p) (SpeedupKx.compress q (word_to_config (output w)) p)
    (hmono w hw hne p) (heventually w hw hne p)
    (fun t => hspec w hw hne t p)
  refine ⟨τ, ?_, hevent⟩
  intro hp
  show τ ≤ κ + (q - 1) * packetCount q w.length
  exact hleast _ (hdeadline w hw hne p hp)

end CellularAutomatas.LocalHorizon.Fusion
