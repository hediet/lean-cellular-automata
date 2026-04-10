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

/-- The initial configuration for unitWord n.
    Position p is `false` iff `0 ≤ p < n`, and `true` otherwise (border). -/
private lemma identityTimerCA_initial (n : ℕ) (p : ℤ) :
    (⦋unitWord n⦌ : Config identityTimerCA.Q) p = decide (p < 0 ∨ p ≥ n) := by
  simp only [CellAutomaton.embed_config, word_to_config, identityTimerCA, unitWord_length]
  split_ifs with h
  · -- Inside word: p ≥ 0 ∧ p < n → result is false
    -- Need: false = decide (p < 0 ∨ p ≥ n)
    rw [eq_comm, decide_eq_false_iff_not]
    push_neg
    exact ⟨h.1, h.2⟩
  · -- Border: ¬(p ≥ 0 ∧ p < n) → result is true
    -- Need: true = decide (p < 0 ∨ p ≥ n)
    rw [eq_comm, decide_eq_true_eq]
    push_neg at h
    rcases (Int.lt_or_le p 0) with hp | hp
    · exact Or.inl hp
    · exact Or.inr (h hp)

/-- Key invariant: At time t, position p has state `decide (p < 0 ∨ p ≥ n - t)`.

    For positions inside the word (0 ≤ p < n):
    - p is `true` iff p ≥ n - t
    - p is `false` iff p < n - t

    The signal starts at the right border and propagates left at speed 1. -/
private lemma identityTimerCA_invariant (n t : ℕ) (p : ℤ) :
    identityTimerCA.nextt ⦋unitWord n⦌ t p = decide (p < 0 ∨ p ≥ (n : ℤ) - t) := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero, Nat.sub_zero, Nat.cast_zero, sub_zero]
    exact identityTimerCA_initial n p
  | succ t ih =>
    -- Unfold next step - the goal becomes δ _ (nextt t p) (nextt t (p+1))
    rw [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- For identityTimerCA, δ _ mid right = mid || right
    -- Apply induction hypothesis
    have h_mid := ih p
    have h_right := ih (p + 1)
    simp only [identityTimerCA] at h_mid h_right ⊢
    rw [h_mid, h_right]
    -- LHS: decide (p < 0 ∨ p ≥ n - t) || decide (p + 1 < 0 ∨ p + 1 ≥ n - t)
    -- RHS: decide (p < 0 ∨ p ≥ n - (t + 1))
    simp only [Nat.cast_succ]
    -- Use decidability to reduce to propositional reasoning
    simp only [← Bool.decide_and, ← Bool.decide_or, Bool.or_eq_true,
               decide_eq_decide, decide_eq_true_eq]
    -- Now it's: (p < 0 ∨ p ≥ n - t) ∨ (p + 1 < 0 ∨ p + 1 ≥ n - t) ↔ p < 0 ∨ p ≥ n - (t + 1)
    constructor
    · intro h
      rcases h with (hp | hp) | (hp | hp)
      · left; exact hp
      · right; omega
      · left; omega
      · right; omega
    · intro h
      rcases h with hp | hp
      · left; left; exact hp
      · right; right; omega

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
    rw [id_eq, identityTimerCA_invariant]
    -- Need: decide (0 < 0 ∨ 0 ≥ n - n) = true, i.e., decide (0 ≥ 0) = true
    simp
  no_signal_before := fun n k hk => by
    show id (identityTimerCA.nextt ⦋unitWord n⦌ k 0) = false
    rw [id_eq, identityTimerCA_invariant]
    -- Need: decide (0 < 0 ∨ 0 ≥ n - k) = false
    -- Since k < n (from hk : k < id n), we have n - k > 0, so ¬(0 ≥ n - k)
    simp only [lt_self_iff_false, false_or]
    -- hk : k < id n = k < n
    simp only [id_eq] at hk
    -- Need: decide (0 ≥ ↑n - ↑k) = false
    rw [decide_eq_false_iff_not, not_le]
    omega

end CellularAutomatas
