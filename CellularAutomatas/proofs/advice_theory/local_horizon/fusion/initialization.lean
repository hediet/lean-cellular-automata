import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.normalized

namespace CellularAutomatas.LocalHorizon.Fusion

open CellAutomaton

namespace Initialization

variable {α β : Type} {q κ : ℕ} {domain : Word α → Prop}
  {output : Advice α β}

/-- Raw blank cells initialize immediately. Raw occupied cells wait for their
packet. This initializes the entire integer line without a length oracle. -/
def C (producer : PacketProducer q κ domain output) :
    CellAutomaton (Option α) (Option (Fin q → Option β)) where
  Q := producer.source.Q × Bool × Bool
  embed input := (producer.source.embed input, input.isSome, true)
  δ left center right :=
    (producer.source.δ left.1 center.1 right.1, center.2.1, false)
  project state :=
    if state.2.1 then producer.source.project state.1
    else if state.2.2 then some (fun _ => none) else none

theorem state_spec (producer : PacketProducer q κ domain output)
    (input : Config (Option α)) (t : ℕ) (p : ℤ) :
    (C producer).nextt ⦋input⦌ t p =
      (producer.source.nextt ⦋input⦌ t p, (input p).isSome, decide (t = 0)) := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    rw [nextt_succ, nextt_succ, next_apply, next_apply]
    change (producer.source.δ
      ((C producer).nextt ⦋input⦌ t (p - 1)).1
      ((C producer).nextt ⦋input⦌ t p).1
      ((C producer).nextt ⦋input⦌ t (p + 1)).1,
      ((C producer).nextt ⦋input⦌ t p).2.1, false) = _
    simp only [ih, Nat.add_one_ne_zero, decide_false]

def release (producer : PacketProducer q κ domain output)
    (w : Word α) (p : ℤ) : ℕ :=
  if (word_to_config w p).isSome then producer.release w p.toNat else 0

theorem blank_compress (hq : 1 ≤ q) (w : Word α) (p : ℤ)
    (hblank : (word_to_config w p).isSome = false) :
    SpeedupKx.compress q (word_to_config (output w)) p = fun _ => none := by
  funext i
  show word_to_config (output w) (p * q + i) = none
  have hp : p < 0 ∨ (w.length : ℤ) ≤ p := by
    by_contra! h
    simp [word_to_config, h.1, h.2] at hblank
  rcases hp with hp | hp
  · have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
    have hi : (i : ℤ) < q := by exact_mod_cast i.isLt
    have hneg : p * q + i < 0 := by nlinarith
    simp [word_to_config, not_le_of_gt hneg]
  · have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
    have hi : (0 : ℤ) ≤ i := Int.natCast_nonneg _
    have hlen : (0 : ℤ) ≤ w.length := Int.natCast_nonneg _
    have hout : ((output w).length : ℤ) ≤ p * q + i := by
      rw [advice_len]
      nlinarith
    simp only [word_to_config, not_lt_of_ge hout, and_false, dite_false]

theorem comp_spec (producer : PacketProducer q κ domain output)
    (w : Word α) (hw : domain w) (hne : w ≠ []) (t : ℕ) (p : ℤ) :
    (C producer).comp w t p =
      if t = release producer w p then
        some (SpeedupKx.compress q (word_to_config (output w)) p) else none := by
  change (C producer).project ((C producer).nextt ⦋w⦌ t p) = _
  rw [state_spec]
  change (if (word_to_config w p).isSome then producer.source.comp w t p
    else if decide (t = 0) then some (fun _ => none) else none) = _
  by_cases hp : (word_to_config w p).isSome = true
  · have hnonneg : 0 ≤ p := by
      by_contra h
      simp [word_to_config, h] at hp
    have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hnonneg
    rw [if_pos hp]
    simp only [release, hp, if_true]
    simpa only [hcast] using producer.emits w hw hne t p.toNat
  · have hfalse : (word_to_config w p).isSome = false := Bool.eq_false_iff.mpr hp
    rw [if_neg hp]
    have hblank := blank_compress (q := q) (output := output)
      (by have := producer.width_ge_two; omega) w p hfalse
    simp [release, hp, hblank]

theorem release_upper [Alphabet α] [Alphabet β]
    (producer : NormalizedProducer q κ domain output)
    (w : Word α) (hw : domain w) (hne : w ≠ []) (p : ℤ) :
    release producer.toPacketProducer w p ≤
      κ + (q - 1) * max (packetCount q w.length) p.toNat := by
  unfold release
  split
  · exact producer.upper w hw hne p.toNat
  · exact Nat.zero_le _

theorem release_negative (producer : PacketProducer q κ domain output)
    (w : Word α) (p : ℤ) (hp : p < 0) :
    release producer w p = 0 := by
  simp [release, word_to_config, not_le_of_gt hp]

end Initialization
end CellularAutomatas.LocalHorizon.Fusion
