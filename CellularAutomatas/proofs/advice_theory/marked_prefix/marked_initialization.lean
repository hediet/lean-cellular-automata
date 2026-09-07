import CellularAutomatas.proofs.advice_theory.marked_prefix.clock_arithmetic
import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_config
import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_join

namespace CellularAutomatas.MarkedPrefix.MarkedInitialization

open CellAutomaton

/-- Join raw and advice packet events, then turn their payload pair into the
three-cell annotated packet expected by the compressed simulation. -/
def C {ρ α Γ : Type} [Alphabet α] [Alphabet Γ]
    (raw : CellAutomaton ρ (Option (Fin 3 → Option α)))
    (adviceSource : CellAutomaton ρ (Option (Fin 3 → Γ))) :
    CellAutomaton ρ (Option (Fin 3 → Option (α × Γ))) :=
  (PacketJoin.C raw adviceSource).map_project
    (Option.map fun pair => joinBlock pair.1 pair.2)

/-- Arithmetic form of the joined packet clock. -/
theorem join_time_eq (κ b p : ℕ) :
    max (κ + 2 * p)
        (κ + Int.natAbs ((p : ℤ) - (b : ℤ))) =
      κ + max (2 * p) (b - p) := by
  by_cases hp : p ≤ b
  · have habs : Int.natAbs ((p : ℤ) - (b : ℤ)) = b - p := by
      have hdiff :
          (p : ℤ) - (b : ℤ) = -((b - p : ℕ) : ℤ) := by
        omega
      rw [hdiff, Int.natAbs_neg, Int.natAbs_natCast]
    rw [habs]
    omega
  · have hbp : b < p := Nat.lt_of_not_ge hp
    have habs : Int.natAbs ((p : ℤ) - (b : ℤ)) = p - b := by
      have hdiff :
          (p : ℤ) - (b : ℤ) = ((p - b : ℕ) : ℤ) := by
        omega
      rw [hdiff, Int.natAbs_natCast]
    rw [habs]
    have hsub : b - p = 0 := Nat.sub_eq_zero_of_le hbp.le
    rw [hsub]
    omega

/-- The two packet arrival clocks join at the generation-zero release time. -/
theorem join_time_eq_release (κ b p : ℕ) :
    max (κ + 2 * p)
        (κ + Int.natAbs ((p : ℤ) - (b : ℤ))) =
      MarkedPrefixClock.release κ b p := by
  simpa only [MarkedPrefixClock.release] using join_time_eq κ b p

variable {ρ α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- Complete marked-input initialization. Negative positions remain silent;
every natural position emits exactly once at the release clock, and its
payload is the genuine compressed annotated configuration, including true
`none` cells beyond the input border. -/
theorem comp_spec
    (raw : CellAutomaton ρ (Option (Fin 3 → Option α)))
    (adviceSource : CellAutomaton ρ (Option (Fin 3 → Γ)))
    (c : Config ρ) (w : Word α) (adv : Advice α Γ) (blank : Γ)
    (κ b : ℕ)
    (hraw : ∀ (t : ℕ) (p : ℤ), raw.comp ⦋c⦌ t p =
      if 0 ≤ p ∧ t = κ + 2 * p.natAbs then
        some (SpeedupKx.compress 3 (word_to_config w) p)
      else none)
    (hadvice : ∀ (t p : ℕ), adviceSource.comp ⦋c⦌ t (p : ℤ) =
      if t = κ + Int.natAbs ((p : ℤ) - (b : ℤ)) then
        some (adviceBlock adv blank w (p : ℤ))
      else none)
    (t : ℕ) (p : ℤ) :
    (C raw adviceSource).comp ⦋c⦌ t p =
      if 0 ≤ p ∧ t = MarkedPrefixClock.release κ b p.natAbs then
        some (SpeedupKx.compress 3
          (word_to_config (adv.annotate w)) p)
      else none := by
  change
    Option.map (fun pair => joinBlock pair.1 pair.2)
      ((PacketJoin.C raw adviceSource).comp ⦋c⦌ t p) = _
  by_cases hp : 0 ≤ p
  · lift p to ℕ using hp
    have hrawAt : ∀ s, raw.comp ⦋c⦌ s (p : ℤ) =
        if s = κ + 2 * p then
          some (SpeedupKx.compress 3 (word_to_config w) (p : ℤ))
        else none := by
      intro s
      rw [hraw s p]
      simp
    rw [PacketJoin.comp_spec_at raw adviceSource c (p : ℤ)
      (κ + 2 * p)
      (κ + Int.natAbs ((p : ℤ) - (b : ℤ)))
      (SpeedupKx.compress 3 (word_to_config w) (p : ℤ))
      (adviceBlock adv blank w (p : ℤ))
      hrawAt (fun s => hadvice s p) t]
    rw [join_time_eq_release]
    simp only [Int.natCast_nonneg, Int.natAbs_natCast, true_and]
    by_cases ht : t = MarkedPrefixClock.release κ b p
    · rw [if_pos ht, if_pos ht]
      simp only [Option.map_some]
      congr 1
      exact joinBlock_eq_compressed_annotation adv blank w p
    · rw [if_neg ht, if_neg ht]
      rfl
  · have hrawNone : ∀ s, raw.comp ⦋c⦌ s p = none := by
      intro s
      rw [hraw s p]
      simp [hp]
    rw [PacketJoin.comp_none_of_left_none_at raw adviceSource c p hrawNone t]
    simp [hp]

end CellularAutomatas.MarkedPrefix.MarkedInitialization
