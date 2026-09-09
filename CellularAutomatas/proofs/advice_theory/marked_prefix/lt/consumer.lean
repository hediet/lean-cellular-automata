import CellularAutomatas.proofs.advice_theory.marked_prefix.async_origin
import CellularAutomatas.proofs.advice_theory.marked_prefix.consumer_normalization
import CellularAutomatas.proofs.advice_theory.marked_prefix.release_envelope
import CellularAutomatas.proofs.advice_theory.local_horizon.deadline

namespace CellularAutomatas.MarkedPrefix.LT

open CellAutomaton

/-- The `q`-fold speedup-and-history wrapper around the dead-border-normalized
consumer. The asynchronous generation protocol itself still uses its fixed
modulo-three tag. -/
abbrev normalizedSpeedupAndTrace
    (q : ℕ) [NeZero q]
    {δ β : Type} [Alphabet δ] [Alphabet β]
    (consumer : CellAutomaton (Option δ) β) : SpeedupAndTraceKx where
  k := q
  α := Option δ
  β := β
  C_orig := (normalizedConsumer consumer).C

/-- The accelerated state carried by every block strictly left of the
half-line. -/
def qDead
    (q : ℕ) [NeZero q]
    {δ β : Type} [Alphabet δ] [Alphabet β]
    (consumer : CellAutomaton (Option δ) β) :
    (normalizedSpeedupAndTrace q consumer).C.Q :=
  (normalizedSpeedupAndTrace q consumer).C.embed (fun _ => none)

theorem qDead_dead
    (q : ℕ) [NeZero q]
    {δ β : Type} [Alphabet δ] [Alphabet β]
    (consumer : CellAutomaton (Option δ) β) :
    (normalizedSpeedupAndTrace q consumer).C.dead (qDead q consumer) := by
  unfold qDead
  apply speedupAndTraceKx_embed_const_dead
  simpa only [CellAutomaton.border] using
    normalizedConsumer_border_dead consumer

/-- Every negative packed block is the normalized consumer's dead state.
This is the only exterior omitted by the half-line clock; blocks to the right
remain part of the actual driven computation. -/
theorem normalizedSpeedupAndTrace_nextt_negative
    (q : ℕ) [NeZero q]
    {δ β : Type} [Alphabet δ] [Alphabet β]
    (consumer : CellAutomaton (Option δ) β)
    (v : Word δ) (t : ℕ) (p : ℤ) (hp : p < 0) :
    (normalizedSpeedupAndTrace q consumer).C.nextt
        ⦋SpeedupKx.compress q (word_to_config v)⦌ t p =
      qDead q consumer := by
  apply nextt_eq_of_dead
    (normalizedSpeedupAndTrace q consumer).C
    (qDead q consumer) (qDead_dead q consumer)
  change (normalizedSpeedupAndTrace q consumer).C.embed
      ((SpeedupKx.compress q (word_to_config v)) p) =
    (normalizedSpeedupAndTrace q consumer).C.embed (fun _ => none)
  apply congrArg
  funext i
  unfold SpeedupKx.compress word_to_config
  have hq : 0 < q := NeZero.pos q
  have hi : (i : ℤ) < q := by exact_mod_cast i.isLt
  have hmul : p * (q : ℤ) ≤ -(q : ℤ) := by
    calc
      p * (q : ℤ) ≤ (-1 : ℤ) * q :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      _ = -(q : ℤ) := by ring
  have hnegative : p * (q : ℤ) + (i : ℤ) < 0 := by
    omega
  simp [hnegative]

/-- An arbitrary one-shot packet producer drives the actual normalized
accelerated consumer. The producer contract covers every natural position,
including all-border packets strictly to the right of the finite word. -/
def source
    (q : ℕ) [NeZero q]
    {ρ δ β : Type} [Alphabet δ] [Alphabet β]
    (producer :
      CellAutomaton (Option ρ) (Option (Fin q → Option δ)))
    (consumer : CellAutomaton (Option δ) β) :
    CellAutomaton (Option ρ) (Fin q → β) :=
  (AsyncHalfLine.OriginPackets.driven producer
    (normalizedSpeedupAndTrace q consumer).C
    (qDead q consumer) (fun _ => default)).C

/-- The explicit half-line arrival recurrence is the arrival specification
used by the finite asynchronous controller. -/
theorem halfLineArrivalSpec (R : ℕ → ℕ) :
    AsyncHalfLine.ArrivalSpec R
      (fun p k => halfLineArrival R k p) where
  zero := fun _ => rfl
  step_zero := fun _ => rfl
  step_succ := fun _ _ => rfl

variable {q : ℕ} [NeZero q]
  {ρ δ β : Type} [Alphabet δ] [Alphabet β]

/-- At its certified arrival time, the concrete driven CA exposes exactly
generation `j` of the synchronous normalized speedup at the origin.
No right border is removed: the packet hypothesis and arrival recurrence range
over every `p : ℕ`. -/
theorem source_trace_eq_normalized_at_arrival
    (producer :
      CellAutomaton (Option ρ) (Option (Fin q → Option δ)))
    (consumer : CellAutomaton (Option δ) β)
    (controllerWord : Word ρ) (hcontroller : 0 < controllerWord.length)
    (v : Word δ) (R : ℕ → ℕ) (κ j : ℕ)
    (hproducer : ∀ t p : ℕ,
      producer.comp ⦋word_to_config controllerWord⦌ t (p : ℤ) =
        if t = R p then
          some (SpeedupKx.compress q (word_to_config v) (p : ℤ))
        else none)
    (harrivalTime : halfLineArrival R j 0 = κ + q * j) :
    (source q producer consumer).trace
        (word_to_config controllerWord) (κ + q * j) =
      (normalizedSpeedupAndTrace q consumer).C.trace
        (SpeedupKx.compress q (word_to_config v)) j := by
  let inner := (normalizedSpeedupAndTrace q consumer).C
  let input : ℕ → (Fin q → Option δ) :=
    fun p => SpeedupKx.compress q (word_to_config v) (p : ℤ)
  let initial : Config inner.Q :=
    inner.embed_config (SpeedupKx.compress q (word_to_config v))
  let H : ℕ → ℕ → ℕ := fun p k => halfLineArrival R k p
  let driven := AsyncHalfLine.OriginPackets.driven producer inner
    (qDead q consumer) (fun _ => default)

  have hpackets : ∀ t p : ℕ,
      producer.comp ⦋word_to_config controllerWord⦌ t (p : ℤ) =
        AsyncHalfLine.packet R input t p := by
    intro t p
    rw [hproducer t p]
    rfl

  have hcontrollerSpec :
      driven.ControllerSpec
        (word_to_config controllerWord) R input := by
    dsimp only [driven]
    exact AsyncHalfLine.OriginPackets.controllerSpec
      producer inner (qDead q consumer) (fun _ => default)
      controllerWord hcontroller R input hpackets

  have harrival : AsyncHalfLine.ArrivalSpec R H := by
    dsimp only [H]
    exact halfLineArrivalSpec R

  have hnegative : ∀ p : ℤ, p < 0 → initial p = qDead q consumer := by
    intro p hp
    have h := normalizedSpeedupAndTrace_nextt_negative
      q consumer v 0 p hp
    simpa only [CellAutomaton.nextt_zero] using h

  have hrun :
      AsyncHalfLine.run inner.δ (qDead q consumer) R
          (fun p : ℕ => inner.embed (input p)) (H 0 j) 0 =
        some (AsyncHalfLine.tag j,
          inner.nextt initial j 0, inner.nextt initial (j - 1) 0) := by
    have h := AsyncHalfLine.run_at_arrival_eq_nextt
      inner (qDead q consumer) (qDead_dead q consumer)
      initial hnegative R harrival 0 j
    convert h using 1

  have hcomp :
      driven.C.comp ⦋word_to_config controllerWord⦌ (H 0 j) 0 =
        inner.project (inner.nextt initial j 0) :=
    driven.comp_of_run
      (word_to_config controllerWord) R input hcontrollerSpec
      (H 0 j) 0 (AsyncHalfLine.tag j)
      (inner.nextt initial j 0) (inner.nextt initial (j - 1) 0) hrun

  have htime : H 0 j = κ + q * j := by
    exact harrivalTime

  rw [← htime]
  change driven.C.comp ⦋word_to_config controllerWord⦌ (H 0 j) 0 =
    inner.project (inner.nextt
      (inner.embed_config
        (SpeedupKx.compress q (word_to_config v))) j 0)
  exact hcomp

theorem source_trace_eq_normalized
    (producer : CellAutomaton (Option ρ) (Option (Fin q → Option δ)))
    (consumer : CellAutomaton (Option δ) β)
    (controllerWord : Word ρ) (hcontroller : 0 < controllerWord.length)
    (v : Word δ) (R : ℕ → ℕ) (κ D j : ℕ) (hq : 2 ≤ q)
    (hproducer : ∀ t p : ℕ,
      producer.comp ⦋word_to_config controllerWord⦌ t (p : ℤ) =
        if t = R p then
          some (SpeedupKx.compress q (word_to_config v) (p : ℤ))
        else none)
    (henvelope : ∀ p,
      κ + (q - 1) * p ≤ R p ∧
        R p ≤ κ + max ((q - 1) * p) D)
    (hcatch : D ≤ (q - 1) * j) :
    (source q producer consumer).trace
        (word_to_config controllerWord) (κ + q * j) =
      (normalizedSpeedupAndTrace q consumer).C.trace
        (SpeedupKx.compress q (word_to_config v)) j := by
  exact source_trace_eq_normalized_at_arrival producer consumer controllerWord
    hcontroller v R κ j hproducer
    (halfLineArrival_origin_of_caught_up R q κ D j (by omega) henvelope hcatch)

theorem source_trace_eq_normalized_of_deadline
    (producer : CellAutomaton (Option ρ) (Option (Fin q → Option δ)))
    (consumer : CellAutomaton (Option δ) β)
    (controllerWord : Word ρ) (hcontroller : 0 < controllerWord.length)
    (v : Word δ) (R : ℕ → ℕ) (κ j : ℕ) (hq : 2 ≤ q)
    (hproducer : ∀ t p : ℕ,
      producer.comp ⦋word_to_config controllerWord⦌ t (p : ℤ) =
        if t = R p then
          some (SpeedupKx.compress q (word_to_config v) (p : ℤ))
        else none)
    (hlower : ∀ p, κ + (q - 1) * p ≤ R p)
    (hupper : ∀ p, p ≤ j → R p ≤ κ + (q - 1) * j) :
    (source q producer consumer).trace
        (word_to_config controllerWord) (κ + q * j) =
      (normalizedSpeedupAndTrace q consumer).C.trace
        (SpeedupKx.compress q (word_to_config v)) j := by
  exact source_trace_eq_normalized_at_arrival producer consumer controllerWord
    hcontroller v R κ j hproducer
    (halfLineArrival_origin_of_deadline R q κ j (by omega) hlower hupper)

end CellularAutomatas.MarkedPrefix.LT
