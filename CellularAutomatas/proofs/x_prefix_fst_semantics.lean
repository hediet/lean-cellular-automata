import CellularAutomatas.defs
import CellularAutomatas.proofs.finite_state_transducers
import Mathlib.Tactic.IntervalCases

/-!
# X_PREFIX PARALLEL PROOF 1: FST Semantics

This file proves that the 5-state FST correctly computes the pure function `g`.

## Goal
Prove `bFST_scanr_getElem` which characterizes the FST output at each position.

## Key Insight
Using `scanr_get'_eq1`:
  `(M.scanr w)[i] = M.f (M.δ (M.scanr_reduce w⟦i+1..*⟧) w[i])`

The FST counts "true" values from right, transitioning through states:
  init → s2 (on first element, always)
  s2 → s1 (on true)
  s1 → s0 (on true)
  s0 → fill (on true)
  fill → fill (always)

Output is `true` iff final state is `fill`.

## Dependencies
- `finite_state_transducers.lean` for `scanr_get'_eq1`
-/

namespace CellularAutomatas

/-! ## FST Definition (copied from step1 for independence) -/

inductive BState
  | init | s2 | s1 | s0 | fill
deriving DecidableEq, Repr, Fintype, Inhabited

def bFST : FiniteStateTransducer Bool Bool := {
  Q := BState
  δ := fun state input =>
    match state, input with
    | .init, _      => .s2
    | .s2,   true   => .s1
    | .s1,   true   => .s0
    | .s0,   true   => .fill
    | .fill, _      => .fill
    | s,     false  => s
  q0 := .init
  f := fun state => state == .fill
}

/-! ## Helper: State after processing suffix -/

/-- The state after processing k consecutive "true" values, starting from s2. -/
def bState_after_trues : ℕ → BState
  | 0 => .s2
  | 1 => .s1
  | 2 => .s0
  | _ => .fill

/-- Key: scanr_reduce on a suffix computes state based on count of trues.
    The first element transitions init→s2, then we count trues capped at 3. -/
lemma bFST_scanr_reduce_state (w : List Bool) (hw : w ≠ []) :
    bFST.scanr_reduce w = bState_after_trues (w.dropLast.count true |>.min 3) := by
  induction w with
  | nil => contradiction
  | cons a w ih =>
    cases hnil : w with
    | nil =>
      show bFST.δ bFST.q0 a = bState_after_trues 0
      simp [bFST, bState_after_trues]
    | cons b ws =>
      subst hnil
      have hw' : b :: ws ≠ [] := List.cons_ne_nil b ws
      rw [FiniteStateTransducer.scanr_reduce_cons, ih hw']
      simp only [List.dropLast_cons₂]
      -- For interval_cases, we need a concrete bound
      have hbound : ((b :: ws).dropLast.count true).min 3 ≤ 3 := Nat.min_le_right _ 3
      cases a with
      | false =>
        -- δ state false = state (for non-init states)
        -- count doesn't change: (false :: tail).count true = tail.count true
        simp only [List.count_cons_of_ne (by decide : false ≠ true)]
        generalize hcdef : (b :: ws).dropLast.count true = c at *
        interval_cases (c.min 3) <;> rfl
      | true =>
        -- δ state true transitions: s2→s1, s1→s0, s0→fill, fill→fill
        -- count increments: (true :: tail).count true = tail.count true + 1
        simp only [List.count_cons_self]
        generalize hcdef : (b :: ws).dropLast.count true = c at *
        -- We need to prove: bFST.δ (bState_after_trues (c.min 3)) true = bState_after_trues ((c+1).min 3)
        -- Key: if c.min 3 = k then (c+1).min 3 = (k+1).min 3
        have h_cmin : (c + 1).min 3 = ((c.min 3) + 1).min 3 := by
          simp only [Nat.min_def]
          split_ifs <;> omega
        rw [h_cmin]
        interval_cases (c.min 3) <;> rfl

/-- The FST output at position i depends on suffix state and current element. -/
theorem bFST_scanr_getElem (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (bFST.scanr w)[i]'(by simp; exact hi) = true ↔
    let suffix := w.drop (i + 1)
    let count := suffix.dropLast.count true
    (count ≥ 3) ∨ (count = 2 ∧ w[i] = true) := by
  -- Use scanr_get'_eq1: (M.scanr w)[i] = M.f (M.δ (M.scanr_reduce w⟦i+1..*⟧) w[i])
  have h_eq := FiniteStateTransducer.scanr_get'_eq1 (M := bFST) w ⟨i, hi⟩
  simp only [Fin.getElem_fin] at h_eq
  rw [h_eq]
  simp only [bFST]
  -- Now goal is: (bFST.δ (bFST.scanr_reduce (w.drop (i+1))) w[i] == .fill) = true ↔ ...
  cases hsuffix_empty : w.drop (i + 1) with
  | nil =>
    -- Empty suffix: scanr_reduce [] = init, δ init _ = s2, f s2 = false
    simp only [FiniteStateTransducer.scanr_reduce_empty, List.dropLast_nil, List.count_nil]
    constructor
    · intro h
      cases w[i] <;> simp_all
    · intro h
      rcases h with hge3 | ⟨heq2, _⟩ <;> omega
  | cons a suffix_tail =>
    -- Non-empty suffix: use bFST_scanr_reduce_state
    have hsuffix_ne : (a :: suffix_tail) ≠ [] := List.cons_ne_nil a suffix_tail
    -- Change to use bFST explicitly
    change (bFST.δ (bFST.scanr_reduce (a :: suffix_tail)) w[i] == .fill) = true ↔ _
    rw [bFST_scanr_reduce_state (a :: suffix_tail) hsuffix_ne]
    set count := (a :: suffix_tail).dropLast.count true with hcount
    have hbound : count.min 3 ≤ 3 := Nat.min_le_right count 3
    -- Now case split on count.min 3 and w[i]
    constructor
    · -- Forward: if δ state w[i] = fill, then count ≥ 3 or (count = 2 and w[i] = true)
      intro h_fill
      interval_cases h_min : (count.min 3)
      · -- count.min 3 = 0: state = s2, δ s2 true = s1, δ s2 false = s2, neither is fill
        cases hw_i : w[i] <;> simp [bState_after_trues, bFST, hw_i] at h_fill
      · -- count.min 3 = 1: state = s1, δ s1 true = s0, δ s1 false = s1, neither is fill
        cases hw_i : w[i] <;> simp [bState_after_trues, bFST, hw_i] at h_fill
      · -- count.min 3 = 2: state = s0, δ s0 true = fill, δ s0 false = s0
        cases hw_i : w[i]
        · simp [bState_after_trues, bFST, hw_i] at h_fill  -- false case: s0 ≠ fill
        · right; constructor
          · simp only [Nat.min_def] at h_min
            split_ifs at h_min <;> omega
          · rfl
      · -- count.min 3 = 3: state = fill, δ fill _ = fill
        left
        simp only [Nat.min_def] at h_min
        split_ifs at h_min <;> omega
    · -- Backward: if count ≥ 3 or (count = 2 and w[i] = true), then δ state w[i] = fill
      intro h_cond
      rcases h_cond with hge3 | ⟨heq2, hw_true⟩
      · -- count ≥ 3: state = fill, δ fill _ = fill
        have h_min : count.min 3 = 3 := Nat.min_eq_right hge3
        simp only [h_min, bState_after_trues]
        cases w[i] <;> rfl
      · -- count = 2 and w[i] = true: state = s0, δ s0 true = fill
        have h_min : count.min 3 = 2 := by simp only [heq2]; decide
        simp only [h_min, bState_after_trues, hw_true, bFST]
        rfl

end CellularAutomatas
