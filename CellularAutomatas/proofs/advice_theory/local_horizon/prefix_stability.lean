import CellularAutomatas.proofs.advice_theory.local_horizon.defs

namespace CellularAutomatas.LocalHorizon

open CellAutomaton

/-- Cutting off input strictly beyond the backward light cone cannot affect
the observed cell. This also covers words shorter than the cutoff. -/
theorem comp_eq_take_of_cone {α β : Type}
    (C : CellAutomaton (Option α) β) (w : Word α)
    (t p cutoff : ℕ) (hcone : p + t < cutoff) :
    C.comp w t p = C.comp (w.take cutoff) t p := by
  apply congrArg C.project
  apply nextt_locality
  intro position hposition
  show C.embed (word_to_config w position) =
    C.embed (word_to_config (w.take cutoff) position)
  apply congrArg C.embed
  have hcutoff : position < (cutoff : ℤ) := by omega
  by_cases hin : 0 ≤ position ∧ position < w.length
  · show word_to_config w position = word_to_config (w.take cutoff) position
    have htake : 0 ≤ position ∧
        position < ((w.take cutoff).length : ℤ) := by
      simp only [List.length_take]
      omega
    simp only [word_to_config, hin, htake, List.getElem_take]
  · show word_to_config w position = word_to_config (w.take cutoff) position
    have htake : ¬(0 ≤ position ∧
        position < ((w.take cutoff).length : ℤ)) := by
      simp only [List.length_take]
      omega
    simp only [word_to_config, hin, htake, dite_false]

/-- An early pulse on a valid prefix fixes the pulse time on every valid
extension. Both validity hypotheses matter: prepared domains need not be
closed under taking prefixes. -/
theorem time_eq_take_of_early_pulse {α : Type} {valid : Word α → Prop}
    (horizon : RealizableHorizon α valid) (w : Word α)
    (p cutoff : ℕ) (hw : valid w) (htake : valid (w.take cutoff))
    (hne : w.take cutoff ≠ [])
    (hearly : p + horizon.time (w.take cutoff) p < cutoff) :
    horizon.time w p = horizon.time (w.take cutoff) p := by
  have hwne : w ≠ [] := by
    intro hempty
    simp only [hempty, List.take_nil] at hne
    exact hne rfl
  have hagrees := comp_eq_take_of_cone horizon.clock w
    (horizon.time (w.take cutoff) p) p cutoff hearly
  rw [horizon.fires w hw hwne, horizon.fires (w.take cutoff) htake hne] at hagrees
  have htime : horizon.time (w.take cutoff) p = horizon.time w p := by
    simpa only [decide_true, decide_eq_true_eq] using hagrees
  exact htime.symm

/-- A globally admissible horizon must fire before seeing a sufficiently
long prefix boundary. The cutoff is affine in physical position. -/
theorem raw_prefix_pulse_early {α : Type} {q κ : ℕ}
    (horizon : RealizableHorizon α (fun _ => True))
    (hadmissible : RTAdmissibleHorizon q κ horizon)
    (w : Word α) (p : ℕ)
    (hlength : q * (p + κ + 1) ≤ w.length) :
    p + horizon.time (w.take (q * (p + κ + 1))) p <
      q * (p + κ + 1) := by
  let cutoff := q * (p + κ + 1)
  have hq : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hadmissible.1
  have hcutoff : 0 < cutoff := Nat.mul_pos hq (by omega)
  have hprefix : (w.take cutoff).length = cutoff := by
    exact List.length_take_of_le hlength
  have hne : w.take cutoff ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hcount : packetCount q (w.take cutoff).length = p + κ + 1 := by
    rw [hprefix, packetCount_of_pos q cutoff hcutoff]
    have hdivision : (cutoff - 1) / q = p + κ := by
      apply Nat.div_eq_of_lt_le
      · dsimp only [cutoff]
        rw [Nat.mul_comm (p + κ) q]
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      · dsimp only [cutoff]
        rw [Nat.mul_comm (p + κ + 1) q]
        omega
    rw [hdivision]
  have hdeadline := hadmissible.2.2 (w.take cutoff) trivial hne p
    (by rw [hcount]; omega)
  rw [hcount] at hdeadline
  change p + horizon.time (w.take cutoff) p < cutoff
  have hbudget : p + (κ + (q - 1) * (p + κ + 1)) + 1 = cutoff := by
    dsimp only [cutoff]
    have hsplit : q = (q - 1) + 1 := by omega
    conv_rhs => rw [hsplit]
    ring
  omega

/-- Global validity lets the early-prefix argument apply to every long word. -/
theorem raw_time_eq_take {α : Type} {q κ : ℕ}
    (horizon : RealizableHorizon α (fun _ => True))
    (hadmissible : RTAdmissibleHorizon q κ horizon)
    (w : Word α) (p : ℕ)
    (hlength : q * (p + κ + 1) ≤ w.length) :
    horizon.time w p =
      horizon.time (w.take (q * (p + κ + 1))) p := by
  have hearly := raw_prefix_pulse_early horizon hadmissible w p hlength
  apply time_eq_take_of_early_pulse horizon w p _ trivial trivial _ hearly
  apply List.ne_nil_of_length_pos
  rw [List.length_take_of_le hlength]
  omega

/-- At logical slot `q*p+r`, a raw horizon sample stabilizes after the
first `q*(p+κ+1)` input symbols. This is a whole-packet equality. -/
theorem raw_sample_eq_take {α Γ : Type} {q κ : ℕ}
    (horizon : RealizableHorizon α (fun _ => True))
    (data : CellAutomaton (Option α) (Fin q → Γ))
    (hadmissible : RTAdmissibleHorizon q κ horizon)
    (w : Word α) (p : ℕ)
    (hlength : q * (p + κ + 1) ≤ w.length) :
    data.comp w (horizon.time w p) p =
      data.comp (w.take (q * (p + κ + 1)))
        (horizon.time (w.take (q * (p + κ + 1))) p) p := by
  rw [raw_time_eq_take horizon hadmissible w p hlength]
  exact comp_eq_take_of_cone data w _ _ _
    (raw_prefix_pulse_early horizon hadmissible w p hlength)

/-- The packet cutoff gives an exact advice-symbol equality, including
short words, for which taking the prefix changes nothing. -/
theorem raw_readout_getElem_take {α Γ : Type} {q κ : ℕ} [NeZero q]
    (horizon : RealizableHorizon α (fun _ => True))
    (data : CellAutomaton (Option α) (Fin q → Γ))
    (hadmissible : RTAdmissibleHorizon q κ horizon)
    (w : Word α) (i : ℕ) (hi : i < w.length) :
    let cutoff := q * (i / q + κ + 1)
    ∃ hprefix : i < (w.take cutoff).length,
      (readout q horizon data w)[i]'(by simpa using hi) =
        (readout q horizon data (w.take cutoff))[i]'(by simpa using hprefix) := by
  dsimp only
  have hq := NeZero.pos q
  have hslot := Nat.mod_lt i hq
  have hdecomposition := Nat.mod_add_div i q
  have hcutoff : i < q * (i / q + κ + 1) := by
    have hexpand : q * (i / q + κ + 1) = q * (i / q) + q * κ + q := by ring
    omega
  have hprefix : i < (w.take (q * (i / q + κ + 1))).length := by
    rw [List.length_take]
    omega
  refine ⟨hprefix, ?_⟩
  by_cases hlong : q * (i / q + κ + 1) ≤ w.length
  · show (readout q horizon data w)[i]'(by simpa using hi) =
      (readout q horizon data (w.take (q * (i / q + κ + 1))))[i]'(by simpa using hprefix)
    rw [readout_getElem q horizon data w i hi,
      readout_getElem q horizon data _ i hprefix]
    exact congrFun (raw_sample_eq_take horizon data hadmissible w (i / q) hlong)
      ⟨i % q, hslot⟩
  · show (readout q horizon data w)[i]'(by simpa using hi) =
      (readout q horizon data (w.take (q * (i / q + κ + 1))))[i]'(by simpa using hprefix)
    simp only [List.take_of_length_le (by omega : w.length ≤ q * (i / q + κ + 1))]

end CellularAutomatas.LocalHorizon
