import CellularAutomatas.proofs.advice_theory.marked_prefix.async_origin
import CellularAutomatas.proofs.advice_theory.marked_prefix.clock_arithmetic
import CellularAutomatas.proofs.advice_theory.marked_prefix.consumer_normalization
import CellularAutomatas.proofs.advice_theory.marked_prefix.marked_initialization

namespace CellularAutomatas.MarkedPrefix.AsyncCatchup

open CellAutomaton

/-- The actual asynchronous source: add origin detection to marked packet
initialization, then drive the normalized threefold accelerated consumer. -/
def source {ρ α Γ β : Type}
    [Alphabet α] [Alphabet Γ] [Alphabet β]
    (raw : CellAutomaton (Option ρ) (Option (Fin 3 → Option α)))
    (adviceSource : CellAutomaton (Option ρ) (Option (Fin 3 → Γ)))
    (consumer : CellAutomaton (Option (α × Γ)) β) :
    CellAutomaton (Option ρ) (Fin 3 → β) :=
  (AsyncHalfLine.OriginPackets.driven
    (MarkedInitialization.C raw adviceSource)
    (normalizedSpeedupAndTrace3 consumer).C
    (qDead consumer) (fun _ => default)).C

/-- The concrete release and arrival clocks satisfy the abstract asynchronous
arrival interface. -/
theorem arrivalSpec (κ b : ℕ) :
    AsyncHalfLine.ArrivalSpec
      (MarkedPrefixClock.release κ b)
      (MarkedPrefixClock.arrival κ b) where
  zero := MarkedPrefixClock.arrival_zero κ b
  step_zero := MarkedPrefixClock.arrival_boundary_succ κ b
  step_succ := MarkedPrefixClock.arrival_interior_succ κ b

variable {ρ α Γ β : Type}
  [Alphabet α] [Alphabet Γ] [Alphabet β]

/-- Once the initial release backlog has been absorbed, the actual marked
packet producer and asynchronous half-line wrapper agree at the origin with
the synchronous normalized accelerated consumer. -/
theorem trace_eq_normalized_of_catchup
    (raw : CellAutomaton (Option ρ) (Option (Fin 3 → Option α)))
    (adviceSource : CellAutomaton (Option ρ) (Option (Fin 3 → Γ)))
    (consumer : CellAutomaton (Option (α × Γ)) β)
    (controllerWord : Word ρ) (hcontroller : 0 < controllerWord.length)
    (w : Word α) (adv : Advice α Γ) (blank : Γ)
    (κ b j : ℕ)
    (hraw : ∀ (t : ℕ) (p : ℤ), raw.comp ⦋word_to_config controllerWord⦌ t p =
      if 0 ≤ p ∧ t = κ + 2 * p.natAbs then
        some (SpeedupKx.compress 3 (word_to_config w) p)
      else none)
    (hadvice : ∀ (t p : ℕ),
      adviceSource.comp ⦋word_to_config controllerWord⦌ t (p : ℤ) =
        if t = κ + Int.natAbs ((p : ℤ) - (b : ℤ)) then
          some (adviceBlock adv blank w (p : ℤ))
        else none)
    (hcatch : b ≤ 2 * j) :
    (source raw adviceSource consumer).trace
        (word_to_config controllerWord) (κ + 3 * j) =
      (normalizedSpeedupAndTrace3 consumer).C.trace
        (SpeedupKx.compress 3
          (word_to_config (adv.annotate w))) j := by
  let P := MarkedInitialization.C raw adviceSource
  let S := (normalizedSpeedupAndTrace3 consumer).C
  let R := MarkedPrefixClock.release κ b
  let H := MarkedPrefixClock.arrival κ b
  let input : ℕ → (Fin 3 → Option (α × Γ)) :=
    fun p => SpeedupKx.compress 3
      (word_to_config (adv.annotate w)) (p : ℤ)
  let initial : Config S.Q :=
    S.embed_config
      (SpeedupKx.compress 3 (word_to_config (adv.annotate w)))
  let driven := AsyncHalfLine.OriginPackets.driven
    P S (qDead consumer) (fun _ => default)

  have hpackets : ∀ t p : ℕ,
      P.comp ⦋word_to_config controllerWord⦌ t (p : ℤ) =
        AsyncHalfLine.packet R input t p := by
    intro t p
    dsimp only [P, R, input]
    rw [MarkedInitialization.comp_spec raw adviceSource
      (word_to_config controllerWord) w adv blank κ b hraw hadvice t p]
    simp only [Int.natCast_nonneg, Int.natAbs_natCast, true_and]
    rfl

  have hcontrollerSpec :
      driven.ControllerSpec
        (word_to_config controllerWord) R input := by
    dsimp only [driven]
    exact AsyncHalfLine.OriginPackets.controllerSpec
      P S (qDead consumer) (fun _ => default)
      controllerWord hcontroller R input hpackets

  have harrival : AsyncHalfLine.ArrivalSpec R H := by
    dsimp only [R, H]
    exact arrivalSpec κ b

  have hnegative : ∀ p : ℤ, p < 0 → initial p = qDead consumer := by
    intro p hp
    have h := normalizedSpeedupAndTrace3_nextt_negative
      consumer (adv.annotate w) 0 p hp
    simpa only [CellAutomaton.nextt_zero] using h

  have hrun :
      AsyncHalfLine.run S.δ (qDead consumer) R
          (fun q : ℕ => S.embed (input q)) (H 0 j) 0 =
        some (AsyncHalfLine.tag j,
          S.nextt initial j 0, S.nextt initial (j - 1) 0) := by
    have h := AsyncHalfLine.run_at_arrival_eq_nextt
      S (qDead consumer) (qDead_dead consumer)
      initial hnegative R harrival 0 j
    convert h using 1

  have hcomp :
      driven.C.comp ⦋word_to_config controllerWord⦌ (H 0 j) 0 =
        S.project (S.nextt initial j 0) :=
    driven.comp_of_run
      (word_to_config controllerWord) R input hcontrollerSpec
      (H 0 j) 0 (AsyncHalfLine.tag j)
      (S.nextt initial j 0) (S.nextt initial (j - 1) 0) hrun

  have htime : H 0 j = κ + 3 * j := by
    dsimp only [H]
    exact MarkedPrefixClock.arrival_origin_of_caught_up κ b j hcatch

  rw [← htime]
  change driven.C.comp ⦋word_to_config controllerWord⦌ (H 0 j) 0 =
    S.project (S.nextt
      (S.embed_config
        (SpeedupKx.compress 3 (word_to_config (adv.annotate w))))
      j 0)
  exact hcomp

end CellularAutomatas.MarkedPrefix.AsyncCatchup
