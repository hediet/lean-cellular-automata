import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

/-!
# Time-Constructible Functions — Core Definitions

A function `t : ℕ → ℕ` is time-constructible if a CA can produce a signal
(output `true` at position 0) at exactly time `t(n)` for input length `n`.

This file contains:
- `unitWord`: canonical words over `Unit`
- `TimeConstructible`: the main structure
- `TimeConstructible.signal_iff`: signal fires iff at exactly time t(n)

The latched CA construction and `time_extension` theorem are in
`time_constructible_latched_ca.lean`.
-/

/-- The canonical word of length n over Unit -/
def unitWord (n : ℕ) : Word Unit := List.replicate n ()

@[simp] lemma unitWord_length (n : ℕ) : (unitWord n).length = n := by simp [unitWord]

/-- A time-constructible function bundled with its timer CA.

    Given `t : ℕ → ℕ`, we have a CA that:
    - Takes input `Unit？` (just marks borders with `none`)
    - Outputs `Bool`
    - For input word of length `n`, position 0 outputs:
      - `true` at time `t(n)`
      - `false` at all times `< t(n)`

    This definition is computable - no existential quantifiers. -/
structure TimeConstructible (t : ℕ → ℕ) where
  /-- The timer CA with input `Unit？` and output `Bool` -/
  timer : CellAutomaton Unit？ Bool
  /-- At time t(n), position 0 outputs true -/
  signal_at_t : ∀ n, timer.project (timer.nextt ⦋unitWord n⦌ (t n) 0) = true
  /-- Before time t(n), position 0 outputs false -/
  no_signal_before : ∀ n k, k < t n → timer.project (timer.nextt ⦋unitWord n⦌ k 0) = false

namespace TimeConstructible

variable {t : ℕ → ℕ} (tc : TimeConstructible t)

/-- Signal fires iff we're at exactly time t(n) -/
theorem signal_iff (n : ℕ) (k : ℕ) (hk : k ≤ t n) :
    tc.timer.project (tc.timer.nextt ⦋unitWord n⦌ k 0) = true ↔ k = t n := by
  constructor
  · intro hs
    by_contra hne
    have hlt : k < t n := Nat.lt_of_le_of_ne hk hne
    have := tc.no_signal_before n k hlt
    rw [this] at hs
    exact Bool.false_ne_true hs
  · intro heq
    rw [heq]
    exact tc.signal_at_t n

end TimeConstructible

/-!
## The identity function t(n) = n is time-constructible

A right-to-left signal at speed 1 reaches position 0 at time n.
The timer has two states: `false` (no signal) and `true` (signal arrived).
At each step, a cell becomes `true` if its right neighbor is either
quiescent (border) or already `true`.
-/

/-- Timer CA for t(n) = n.

    A right-to-left signal at speed 1. The rightmost cell detects the border
    at t=1, and the signal propagates left, reaching position 0 at time n. -/
def identityTimerCA : CellAutomaton Unit？ Bool where
  Q := Bool
  δ := fun _left mid right =>
    -- Become true if we or our right neighbor is true
    mid || right
  embed := fun a =>
    match a with
    | none => true   -- Border is "true" (triggers the signal)
    | some () => false
  project := id

/-- The identity function `t(n) = n` is time-constructible.

    **Construction**: A signal propagates left from the right border at speed 1.
    - Border cells embed as `true`, inside cells as `false`.
    - δ: a cell becomes `true` if it or its right neighbor is `true`.
    - For word of length `n`, position `n-1` sees border at `t=1`,
      so position `p` becomes `true` at time `n - p`.
    - Position 0 becomes `true` at time `n`.

    **Key invariant**: At time `t`, position `p` is `true` iff `p ≥ n - t`
    (for positions inside the word, i.e. `0 ≤ p < n`). -/
def identityTimeConstructible : TimeConstructible id where
  timer := identityTimerCA
  signal_at_t := fun n => by
    show id (identityTimerCA.nextt ⦋unitWord n⦌ n 0) = true
    simp only [id_eq]
    -- Signal at position 0 is true at time n.
    -- Key invariant: at time t, position p (0 ≤ p < n) has state (n - p ≤ t).
    -- At t = n, p = 0: n - 0 ≤ n, so true.
    -- Prove by induction on n.
    induction n with
    | zero =>
      -- n = 0: unitWord 0 = [], position 0 is outside the word (border).
      -- embed_config maps none to true. nextt at time 0 is initial.
      simp [CellAutomaton.nextt_zero, CellAutomaton.embed_config, identityTimerCA,
            unitWord, word_to_config]
    | succ n ih =>
      sorry
  no_signal_before := fun n k hk => by
    show id (identityTimerCA.nextt ⦋unitWord n⦌ k 0) = false
    simp only [id_eq]
    -- Before time n, the signal hasn't reached position 0.
    -- Key invariant: at time t < n, position 0 is false.
    sorry

/-- Linear functions `c * n` are time-constructible for all constants `c`.

    A CA can count to `c * n` using a zig-zag signal of speed `c`. -/
axiom scaleTimeConstructible (c : ℕ) : TimeConstructible (fun n => c * n)

/-- Linear functions `c * (n - 1)` are time-constructible for `c ≥ 2`.

    Matches the codebase convention where real-time is `n - 1` and
    linear time is `c * (n - 1)` (cf. `t_lt`, `t_2n`).
    Requires `c ≥ 2` since the timer needs a zig-zag signal that
    traverses the word at least once before firing. -/
axiom linearTimeConstructible (c : ℕ) (hc : c ≥ 2) : TimeConstructible (fun n => c * (n - 1))

end CellularAutomatas
