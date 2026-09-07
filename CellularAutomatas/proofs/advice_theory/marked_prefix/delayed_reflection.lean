import CellularAutomatas.defs

namespace CellularAutomatas.MarkedPrefix.DelayedReflection

open CellAutomaton

variable {α : Type} [Alphabet α]

/-!
# Delayed reflection of a finite input word

This file isolates one finite-state signal-routing primitive.  The lower
track moves the input left at unit speed.  The permanent input-shape bit
detects the original left edge, where the lower track is injected into the
upper track.  A delay track then makes every further rightward move take two
steps.

In particular, the upper track is empty at time zero; this is deliberately
different from constructions whose outgoing track is populated by `embed`.
-/

/-- Four-track state for the delayed reflector.  `originalInside` is static;
the other three fields carry the incoming and outgoing streams. -/
structure State (α : Type) where
  originalInside : Bool
  lower : Option α
  delay : Option α
  upper : Option α
  deriving DecidableEq, Fintype, Inhabited

/-- Only the lower track is populated initially. -/
def embed (input : Option α) : State α where
  originalInside := input.isSome
  lower := input
  delay := none
  upper := none

/-- One step of the reflector.

The left-edge test uses only the permanent input-shape bits.  Away from that
edge, `upper` receives the local delay register, while `delay` receives the
left neighbour's upper track. -/
def step (left center right : State α) : State α where
  originalInside := center.originalInside
  lower := right.lower
  delay := left.upper
  upper :=
    if center.originalInside && !left.originalInside then
      center.lower
    else
      center.delay

/-- The finite-state cellular automaton exposing the delayed reflected stream. -/
def ca (α : Type) [Alphabet α] : CellAutomaton (Option α) (Option α) where
  Q := State α
  δ := step
  embed := embed
  project := State.upper

/-! ## Static shape and incoming stream -/

/-- The permanent bit records exactly membership in the original input word. -/
theorem originalInside_spec (w : Word α) (t : ℕ) (p : ℤ) :
    ((ca α).nextt (⦋word_to_config w⦌) t p).originalInside =
      decide (0 ≤ p ∧ p < (w.length : ℤ)) := by
  induction t generalizing p with
  | zero =>
      simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply]
      change (word_to_config w p).isSome =
        decide (0 ≤ p ∧ p < (w.length : ℤ))
      unfold word_to_config
      split_ifs with h
      · simp [h]
      · simp [h]
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      change ((ca α).nextt (⦋word_to_config w⦌) t p).originalInside = _
      exact ih p

/-- For a nonempty word, the permanent-bit detector is true exactly at the
physical origin, at every time. -/
theorem leftmostDetector_iff (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ) :
    (((ca α).nextt (⦋word_to_config w⦌) t p).originalInside &&
        !((ca α).nextt (⦋word_to_config w⦌) t (p - 1)).originalInside) = true ↔
      p = 0 := by
  rw [originalInside_spec, originalInside_spec]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  have hwlen : 0 < w.length := List.length_pos_of_ne_nil hw
  constructor
  · rintro ⟨⟨hp0, hpw⟩, hleft⟩
    by_contra hp
    apply hleft
    constructor <;> omega
  · intro hp
    subst p
    constructor
    · constructor <;> omega
    · omega

/-- The lower track is the input configuration shifted left by `t`. -/
theorem lower_spec (w : Word α) (t : ℕ) (p : ℤ) :
    ((ca α).nextt (⦋word_to_config w⦌) t p).lower =
      word_to_config w (p + (t : ℤ)) := by
  induction t generalizing p with
  | zero =>
      simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply]
      simp [ca, embed]
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      change ((ca α).nextt (⦋word_to_config w⦌) t (p + 1)).lower = _
      rw [ih]
      congr 1
      push_cast
      omega

/-! ## Closed forms for the two outgoing pipeline tracks -/

/-- Closed form for the visible outgoing track.

The signal reaches nonnegative position `p` at time `1 + 2*p`; its payload
then advances through the original word at unit speed. -/
def expectedUpper (w : Word α) (t : ℕ) (p : ℤ) : Option α :=
  if 0 ≤ p ∧ 1 + 2 * p ≤ (t : ℤ) then
    word_to_config w ((t : ℤ) - 1 - 2 * p)
  else
    none

/-- Closed form for the intermediate delay track. -/
def expectedDelay (w : Word α) (t : ℕ) (p : ℤ) : Option α :=
  if 1 ≤ p ∧ 2 * p ≤ (t : ℤ) then
    word_to_config w ((t : ℤ) - 2 * p)
  else
    none

omit [Alphabet α] in
private theorem expectedDelay_succ (w : Word α) (t : ℕ) (p : ℤ) :
    expectedDelay w (t + 1) p = expectedUpper w t (p - 1) := by
  unfold expectedDelay expectedUpper
  split_ifs with hdelay hupper
  · congr 1
    push_cast
    omega
  · omega
  · omega
  · rfl

omit [Alphabet α] in
private theorem expectedUpper_succ_zero (w : Word α) (t : ℕ) :
    expectedUpper w (t + 1) 0 = word_to_config w (t : ℤ) := by
  unfold expectedUpper
  rw [if_pos (by
    constructor
    · omega
    · push_cast
      omega)]
  congr 1
  push_cast
  omega

omit [Alphabet α] in
private theorem expectedUpper_succ_ne_zero (w : Word α) (t : ℕ) (p : ℤ)
    (hp : p ≠ 0) :
    expectedUpper w (t + 1) p = expectedDelay w t p := by
  unfold expectedUpper expectedDelay
  split_ifs with hupper hdelay
  · congr 1
    push_cast
    omega
  · omega
  · omega
  · rfl

/-- The delay and upper tracks satisfy their closed forms jointly.  Pairing
the induction hypotheses reflects the two-stage recurrence
`delay(t+1,p) = upper(t,p-1)`. -/
theorem delay_upper_spec (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ) :
    ((ca α).nextt (⦋word_to_config w⦌) t p).delay = expectedDelay w t p ∧
    ((ca α).nextt (⦋word_to_config w⦌) t p).upper = expectedUpper w t p := by
  induction t generalizing p with
  | zero =>
      simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply]
      change (none : Option α) = expectedDelay w 0 p ∧
        (none : Option α) = expectedUpper w 0 p
      constructor
      · unfold expectedDelay
        rw [if_neg (by omega)]
      · unfold expectedUpper
        rw [if_neg (by omega)]
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      change
        ((ca α).nextt (⦋word_to_config w⦌) t (p - 1)).upper =
            expectedDelay w (t + 1) p ∧
          (if
              ((ca α).nextt (⦋word_to_config w⦌) t p).originalInside &&
                !((ca α).nextt (⦋word_to_config w⦌) t (p - 1)).originalInside
            then ((ca α).nextt (⦋word_to_config w⦌) t p).lower
            else ((ca α).nextt (⦋word_to_config w⦌) t p).delay) =
            expectedUpper w (t + 1) p
      constructor
      · rw [(ih (p - 1)).2]
        exact (expectedDelay_succ w t p).symm
      · rw [lower_spec, (ih p).1]
        by_cases hp : p = 0
        · rw [if_pos ((leftmostDetector_iff w hw t p).2 hp)]
          subst p
          simpa using (expectedUpper_succ_zero w t).symm
        · rw [if_neg (mt (leftmostDetector_iff w hw t p).1 hp)]
          exact (expectedUpper_succ_ne_zero w t p hp).symm

/-! ## Projected-stream API -/

/-- Exact all-integer specification of the projected rightward stream.

For every integer cell, the output is present precisely in the stated
nonnegative arrival cone.  The `word_to_config` payload is important: after
the finite word has passed, and whenever its source index is outside the
word, the result is `none` rather than a saturated natural-number lookup. -/
theorem comp_spec (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ) :
    (ca α).comp (⦋word_to_config w⦌) t p =
      if 0 ≤ p ∧ 1 + 2 * p ≤ (t : ℤ) then
        word_to_config w ((t : ℤ) - 1 - 2 * p)
      else
        none := by
  change ((ca α).nextt (⦋word_to_config w⦌) t p).upper = _
  exact (delay_upper_spec w hw t p).2

/-- Inside the arrival cone, expose the corresponding integer-indexed input
configuration value. -/
theorem comp_after_arrival (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ)
    (hp : 0 ≤ p) (ht : 1 + 2 * p ≤ (t : ℤ)) :
    (ca α).comp (⦋word_to_config w⦌) t p =
      word_to_config w ((t : ℤ) - 1 - 2 * p) := by
  rw [comp_spec w hw]
  exact if_pos ⟨hp, ht⟩

/-- Outside the arrival cone—including every negative physical position—the
projected output is empty. -/
theorem comp_before_arrival (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ)
    (houtside : ¬(0 ≤ p ∧ 1 + 2 * p ≤ (t : ℤ))) :
    (ca α).comp (⦋word_to_config w⦌) t p = none := by
  rw [comp_spec w hw]
  exact if_neg houtside

omit [Alphabet α] in
private theorem word_to_config_nat (w : Word α) (j : ℕ) :
    word_to_config w (j : ℤ) = w[j]? := by
  by_cases hj : j < w.length
  · rw [word_to_config_apply, dif_pos]
    · exact (List.getElem?_eq_getElem hj).symm
    · constructor <;> omega
  · rw [word_to_config_apply, dif_neg]
    · exact (List.getElem?_eq_none (Nat.le_of_not_gt hj)).symm
    · omega

/-- Natural-position form of `comp_spec`.  There is intentionally no upper
bound on `p` or `j`: this includes cells beyond the original right border,
and returns `none` exactly when `j` is beyond the finite word. -/
theorem comp_nat_arrival (w : Word α) (hw : w ≠ []) (p j : ℕ) :
    (ca α).comp (⦋word_to_config w⦌) (1 + 2 * p + j) (p : ℤ) = w[j]? := by
  rw [comp_spec w hw, if_pos]
  · rw [show ((1 + 2 * p + j : ℕ) : ℤ) - 1 - 2 * (p : ℤ) = (j : ℤ) by
      push_cast
      omega]
    exact word_to_config_nat w j
  · constructor
    · omega
    · push_cast
      omega

/-- Before time `1 + 2*p`, the natural-position output is empty. -/
theorem comp_nat_before_arrival (w : Word α) (hw : w ≠ []) (p t : ℕ)
    (ht : t < 1 + 2 * p) :
    (ca α).comp (⦋word_to_config w⦌) t (p : ℤ) = none := by
  apply comp_before_arrival w hw
  omega

end CellularAutomatas.MarkedPrefix.DelayedReflection
