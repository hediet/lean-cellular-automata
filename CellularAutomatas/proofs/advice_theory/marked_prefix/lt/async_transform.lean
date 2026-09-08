import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.finite_strip
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.packed_transform

namespace CellularAutomatas.MarkedPrefix.LT.AsyncTransform

open AsyncHalfLine

variable {ι α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- The actual finite-strip execution of the accelerated, stable LT witness.
Neither the strip length nor its release schedule occurs in this CA. -/
def driven (q : ℕ) [NeZero q] {F : Advice α Γ} (hF : F.IsLtAdvice)
    (controller :
      CellAutomaton ι ((Bool × Bool) × Option (Fin q → Option α))) :
    FiniteStrip.Driven where
  inner := PackedTransform.C q hF
  controller := controller
  dead := (PackedTransform.C q hF).embed (fun _ => none)
  padding := none

def events (q : ℕ) [NeZero q] {F : Advice α Γ} (hF : F.IsLtAdvice)
    (controller :
      CellAutomaton ι ((Bool × Bool) × Option (Fin q → Option α))) :
    CellAutomaton ι (Option (Fin q → Γ)) :=
  FirstOutput.C (driven q hF controller).C

/-- The ghost clock only records how far the finite-state machine has run.
Its first ready generation is exactly the stable producer's `c*M` deadline. -/
theorem comp_eq_height (q : ℕ) [NeZero q] {F : Advice α Γ}
    (hF : F.IsLtAdvice) (blank : Γ)
    (controller :
      CellAutomaton ι ((Bool × Bool) × Option (Fin q → Option α)))
    (input : Config ι) (w : Word α) (M : ℕ) (hM : 0 < M)
    (hlength : w.length = q * M) (R : ℕ → ℕ)
    (hcontroller : (driven q hF controller).ControllerSpec M input R
      (fun p => SpeedupKx.compress q (word_to_config w) p))
    (t p : ℕ) (hp : p < M) :
    (driven q hF controller).C.comp ⦋input⦌ t p =
      if hF.c * M + 1 ≤ FiniteStrip.height M R t p
        then some (PackedTransform.block q F blank w p) else none := by
  let inner := PackedTransform.C q hF
  let initial : Config inner.Q :=
    inner.embed_config (SpeedupKx.compress q (word_to_config w))
  have hexterior : ∀ z : ℤ, z < 0 ∨ (M : ℤ) ≤ z →
      initial z = inner.embed (fun _ => none) := by
    intro z hz
    change inner.embed (SpeedupKx.compress q (word_to_config w) z) =
      inner.embed (fun _ => none)
    rw [compress_word_exterior q w M hlength z hz]
  rw [(driven q hF controller).comp_eq_output M input R _ hcontroller t p hp]
  by_cases hzero : FiniteStrip.height M R t p = 0
  · rw [FiniteStrip.run_encode _ _ _ _ _ t p hp]
    simp only [hzero, AsyncHalfLine.encode, AsyncHalfLine.output]
    rfl
  · let generation := FiniteStrip.height M R t p - 1
    have hheight : FiniteStrip.height M R t p = generation + 1 := by
      dsimp [generation]
      omega
    have hstate := FiniteStrip.run_at_generation_eq_nextt inner
      (inner.embed (fun _ => none)) (PackedTransform.dead q hF)
      initial M hexterior R t p generation hp hheight
    change AsyncHalfLine.output inner.project none
      (FiniteStrip.run inner.δ (inner.embed (fun _ => none)) M R
        (fun p : ℕ => initial p) t p) = _
    rw [hstate]
    change inner.comp ⦋SpeedupKx.compress q (word_to_config w)⦌
      generation p = _
    rw [PackedTransform.spec q hF blank w M hM hlength generation p hp]
    simp only [hheight, Nat.add_le_add_iff_right]

/-- Every physical producer cell has a definite first ready time, bounded by
the last input release plus the accelerated runtime, despite staggered starts. -/
theorem exists_ready_at (q : ℕ) [NeZero q] {F : Advice α Γ}
    (hF : F.IsLtAdvice) (blank : Γ)
    (controller :
      CellAutomaton ι ((Bool × Bool) × Option (Fin q → Option α)))
    (input : Config ι) (w : Word α) (M : ℕ) (hM : 0 < M)
    (hlength : w.length = q * M) (R : ℕ → ℕ) (T : ℕ)
    (hcontroller : (driven q hF controller).ControllerSpec M input R
      (fun p => SpeedupKx.compress q (word_to_config w) p))
    (hrelease : ∀ p, p < M → R p ≤ T) (p : ℕ) (hp : p < M) :
    ∃ τ, R p ≤ τ ∧ τ ≤ T + hF.c * M ∧
      ∀ t, (driven q hF controller).C.comp ⦋input⦌ t p =
        if τ ≤ t then some (PackedTransform.block q F blank w p) else none := by
  obtain ⟨τ, hlower, hupper, hready⟩ :=
    exists_ready_time (fun t => FiniteStrip.height M R t p) (R p)
      (T + hF.c * M) (hF.c * M + 1)
      (FiniteStrip.height_mono_time M R p) (by omega)
      (FiniteStrip.height_eq_zero_of_lt M R · p)
      (FiniteStrip.height_uniform_completion M R T (hF.c * M) p hp hrelease)
  refine ⟨τ, hlower, hupper, ?_⟩
  intro t
  rw [comp_eq_height q hF blank controller input w M hM hlength R
    hcontroller t p hp]
  simp only [hready t]

/-- The finite-strip computation emits exactly once at that same ready time;
no extra physical tick is spent converting completion to an event. -/
theorem exists_event_at (q : ℕ) [NeZero q] {F : Advice α Γ}
    (hF : F.IsLtAdvice) (blank : Γ)
    (controller :
      CellAutomaton ι ((Bool × Bool) × Option (Fin q → Option α)))
    (input : Config ι) (w : Word α) (M : ℕ) (hM : 0 < M)
    (hlength : w.length = q * M) (R : ℕ → ℕ) (T : ℕ)
    (hcontroller : (driven q hF controller).ControllerSpec M input R
      (fun p => SpeedupKx.compress q (word_to_config w) p))
    (hrelease : ∀ p, p < M → R p ≤ T) (p : ℕ) (hp : p < M) :
    ∃ τ, R p ≤ τ ∧ τ ≤ T + hF.c * M ∧
      ∀ t, (events q hF controller).comp ⦋input⦌ t p =
        if t = τ then some (PackedTransform.block q F blank w p) else none := by
  obtain ⟨τ, hlower, hupper, hready⟩ :=
    exists_ready_at q hF blank controller input w M hM hlength R T
      hcontroller hrelease p hp
  refine ⟨τ, hlower, hupper, ?_⟩
  exact FirstOutput.comp_spec (driven q hF controller).C input p τ
    (PackedTransform.block q F blank w p) hready

end CellularAutomatas.MarkedPrefix.LT.AsyncTransform
