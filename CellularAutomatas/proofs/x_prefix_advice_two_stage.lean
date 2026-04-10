import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.exp_middle_two_stage
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.nextpow2
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases

/-!
# xPrefixAdvice Two-Stage

Proves `bFST.scanr (mark_pow2_v n) = threshold_v n` by combining:
1. **FST semantics**: the 5-state FST outputs true iff ≥3 marks in suffix or (2 marks and current is true)
2. **Threshold equivalence**: `i < nextPow2(n)/8 ↔ ≥3 power-of-2 marks in [i..n-2]`
3. **Bridge**: connects the FST output condition to the mark count

## Definitions
- `bFST`: 5-state FST counting "true" values from the right
- `mark_pow2_v n`: marks positions where i+1 is a power of 2
- `threshold_v n`: position i is true iff i < nextPow2(n)/8
-/

namespace CellularAutomatas

open CellAutomaton

/-! ## Part 1: FST Definition and Semantics

The 5-state FST counts "true" values from right, transitioning through states:
  init → s2 (on first element, always)
  s2 → s1 (on true), s1 → s0 (on true), s0 → fill (on true)
  fill → fill (always)
Output is `true` iff final state is `fill`. -/

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

/-- The state after processing k consecutive "true" values, starting from s2. -/
private def bState_after_trues : ℕ → BState
  | 0 => .s2
  | 1 => .s1
  | 2 => .s0
  | _ => .fill

/-- Key: scanr_reduce on a suffix computes state based on count of trues.
    The first element transitions init→s2, then we count trues capped at 3. -/
private lemma bFST_scanr_reduce_state (w : List Bool) (hw : w ≠ []) :
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
      have hbound : ((b :: ws).dropLast.count true).min 3 ≤ 3 := Nat.min_le_right _ 3
      cases a with
      | false =>
        simp only [List.count_cons_of_ne (by decide : false ≠ true)]
        generalize hcdef : (b :: ws).dropLast.count true = c at *
        interval_cases (c.min 3) <;> rfl
      | true =>
        simp only [List.count_cons_self]
        generalize hcdef : (b :: ws).dropLast.count true = c at *
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
  have h_eq := FiniteStateTransducer.scanr_get'_eq1 (M := bFST) w ⟨i, hi⟩
  simp only [Fin.getElem_fin] at h_eq
  rw [h_eq]
  simp only [bFST]
  cases hsuffix_empty : w.drop (i + 1) with
  | nil =>
    simp only [FiniteStateTransducer.scanr_reduce_empty, List.dropLast_nil, List.count_nil]
    constructor
    · intro h
      cases w[i] <;> simp_all
    · intro h
      rcases h with hge3 | ⟨heq2, _⟩ <;> omega
  | cons a suffix_tail =>
    have hsuffix_ne : (a :: suffix_tail) ≠ [] := List.cons_ne_nil a suffix_tail
    change (bFST.δ (bFST.scanr_reduce (a :: suffix_tail)) w[i] == .fill) = true ↔ _
    rw [bFST_scanr_reduce_state (a :: suffix_tail) hsuffix_ne]
    set count := (a :: suffix_tail).dropLast.count true with hcount
    have hbound : count.min 3 ≤ 3 := Nat.min_le_right count 3
    constructor
    · intro h_fill
      interval_cases h_min : (count.min 3)
      · cases hw_i : w[i] <;> simp [bState_after_trues, bFST, hw_i] at h_fill
      · cases hw_i : w[i] <;> simp [bState_after_trues, bFST, hw_i] at h_fill
      · cases hw_i : w[i]
        · simp [bState_after_trues, bFST, hw_i] at h_fill
        · right; constructor
          · simp only [Nat.min_def] at h_min
            split_ifs at h_min <;> omega
          · rfl
      · left
        simp only [Nat.min_def] at h_min
        split_ifs at h_min <;> omega
    · intro h_cond
      rcases h_cond with hge3 | ⟨heq2, hw_true⟩
      · have h_min : count.min 3 = 3 := Nat.min_eq_right hge3
        simp only [h_min, bState_after_trues]
        cases w[i] <;> rfl
      · have h_min : count.min 3 = 2 := by simp only [heq2]; decide
        simp only [h_min, bState_after_trues, hw_true, bFST]
        rfl

/-! ## Part 2: Threshold Equivalence

Proves: `i < nextPow2(n) / 8 ↔ ≥3 power-of-2 marks in [i..n-2]` -/

/-- Count of marks in mark_pow2(n)[i..n-2]. -/
def marks_from_i_excl_last' (n i : ℕ) : ℕ :=
  let mark_pow2 := (List.range n).map (fun j => isPowerOfTwo (j + 1))
  mark_pow2.drop i |>.dropLast |>.count true

/-! ### List-level helpers -/

private lemma dropLast_range'_succ (a m : ℕ) :
    (List.range' a (m + 1)).dropLast = List.range' a m := by
  induction m generalizing a with
  | zero => simp [List.range']
  | succ m ih =>
    simp only [List.range'_succ]
    rw [List.dropLast_cons_of_ne_nil]
    · congr 1; exact ih (a + 1)
    · exact List.ne_nil_of_length_pos (by simp [List.length_range'])

/-- Convert marks to `countP` on a contiguous range of indices. -/
private lemma marks_eq_countP (n i : ℕ) (hi : i < n) :
    marks_from_i_excl_last' n i =
    (List.range' i (n - 1 - i)).countP (fun j => isPowerOfTwo (j + 1)) := by
  unfold marks_from_i_excl_last'; simp only []
  have h_list_eq :
      ((List.map (fun j => isPowerOfTwo (j + 1)) (List.range n)).drop i).dropLast =
      List.map (fun j => isPowerOfTwo (j + 1)) (List.range' i (n - 1 - i)) := by
    rw [← List.map_drop, List.map_dropLast.symm]
    congr 1
    rw [List.range_eq_range', List.drop_range']
    simp only [Nat.zero_add, mul_one]
    rw [show n - i = (n - 1 - i) + 1 from by omega]
    exact dropLast_range'_succ i (n - 1 - i)
  rw [h_list_eq, List.count_eq_countP, List.countP_map]
  congr 1; ext x; simp [beq_iff_eq]

/-! ### Counting helpers -/

private lemma nodup_three_mem_length {l : List ℕ} (hnd : l.Nodup)
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l) :
    l.length ≥ 3 := by
  by_contra h_lt; push_neg at h_lt
  have hlen : l.length ≤ 2 := by omega
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _⟩⟩⟩
  · exact absurd ha (by simp)
  · simp at ha hb; subst ha; subst hb; exact hab rfl
  · simp at ha hb hc
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
      first | exact hab rfl | exact hac rfl | exact hbc rfl | simp_all
  · exfalso; simp at hlen

private lemma countP_ge_three_of_mem {l : List ℕ} (hnd : l.Nodup) (p : ℕ → Bool)
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hpa : p a = true) (hpb : p b = true) (hpc : p c = true) :
    l.countP p ≥ 3 := by
  rw [List.countP_eq_length_filter]
  apply nodup_three_mem_length (List.Nodup.filter _ hnd) hab hac hbc <;>
    rw [List.mem_filter] <;> exact ⟨‹_›, ‹_›⟩

private lemma nodup_two_values_length_le {l : List ℕ} (hnd : l.Nodup) {a b : ℕ}
    (h : ∀ x ∈ l, x = a ∨ x = b) : l.length ≤ 2 := by
  by_contra h_gt; push_neg at h_gt
  have : l.length ≥ 3 := by omega
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l'⟩⟩⟩
  · simp at this
  · simp at this
  · simp at this
  · have hx := h x (by simp)
    have hy := h y (by simp)
    have hz := h z (by simp)
    simp only [List.nodup_cons, List.mem_cons] at hnd
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      simp_all

private lemma countP_le_two_of_two_values {l : List ℕ} (hnd : l.Nodup) (p : ℕ → Bool)
    {a b : ℕ} (h : ∀ x ∈ l, p x = true → x = a ∨ x = b) :
    l.countP p ≤ 2 := by
  rw [List.countP_eq_length_filter]
  exact nodup_two_values_length_le (List.Nodup.filter _ hnd) fun x hx => by
    simp [List.mem_filter] at hx; exact h x hx.1 hx.2

private lemma isPow2_of_pow (k : ℕ) : isPowerOfTwo (2 ^ k) = true := by
  rw [isPowerOfTwo_iff]; exact ⟨k, rfl⟩

/-! ### Main Theorem -/

theorem threshold_iff_marks_ge_3 (n i : ℕ) (hi : i < n) :
    (i < nextPow2 n / 8) ↔ marks_from_i_excl_last' n i ≥ 3 := by
  rw [marks_eq_countP n i hi]
  set isPow2' := (fun j => isPowerOfTwo (j + 1)) with isPow2'_def
  by_cases hn : n ≥ 5
  · set M := Nat.log2 (n - 1) with hM_def
    have hM_ge : M ≥ 2 := by
      rw [ge_iff_le, Nat.le_log2 (show n - 1 ≠ 0 by omega)]
      show 2 ^ 2 ≤ n - 1; omega
    have h_threshold : nextPow2 n / 8 = 2 ^ (M - 2) := by
      have h_np : nextPow2 n = 2 ^ (M + 1) := by
        unfold nextPow2
        split_ifs with h
        · exfalso; omega
        · exact congrArg (2 ^ · ) (by omega : Nat.log2 (n - 1) + 1 = M + 1)
      rw [h_np, show (8 : ℕ) = 2 ^ 3 by norm_num,
          Nat.pow_div (show 3 ≤ M + 1 by omega) (show 0 < 2 by omega),
          show M + 1 - 3 = M - 2 by omega]
    rw [h_threshold]
    have h_2M_le : 2 ^ M ≤ n - 1 := Nat.log2_self_le (show n - 1 ≠ 0 by omega)
    have hnd : (List.range' i (n - 1 - i)).Nodup := List.nodup_range' ..
    have h_lt_12 : 2 ^ (M - 2) < 2 ^ (M - 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have h_lt_23 : 2 ^ (M - 1) < 2 ^ M :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    constructor
    · -- Forward: i < 2^(M-2) → countP ≥ 3
      intro h_lt
      -- Witnesses: 2^(M-2)-1, 2^(M-1)-1, 2^M-1
      apply countP_ge_three_of_mem hnd isPow2'
        (show 2^(M-2)-1 ≠ 2^(M-1)-1 by omega)
        (show 2^(M-2)-1 ≠ 2^M-1 by omega)
        (show 2^(M-1)-1 ≠ 2^M-1 by omega)
      · exact List.mem_range'.mpr ⟨2 ^ (M - 2) - 1 - i, by omega, by omega⟩
      · exact List.mem_range'.mpr ⟨2 ^ (M - 1) - 1 - i, by omega, by omega⟩
      · exact List.mem_range'.mpr ⟨2 ^ M - 1 - i, by omega, by omega⟩
      · show isPow2' (2 ^ (M - 2) - 1) = true
        simp only [isPow2'_def]
        have : 2 ^ (M - 2) ≥ 1 := Nat.one_le_two_pow
        rw [show 2 ^ (M - 2) - 1 + 1 = 2 ^ (M - 2) from by omega]
        exact isPow2_of_pow _
      · show isPow2' (2 ^ (M - 1) - 1) = true
        simp only [isPow2'_def]
        have : 2 ^ (M - 1) ≥ 1 := Nat.one_le_two_pow
        rw [show 2 ^ (M - 1) - 1 + 1 = 2 ^ (M - 1) from by omega]
        exact isPow2_of_pow _
      · show isPow2' (2 ^ M - 1) = true
        simp only [isPow2'_def]
        have : 2 ^ M ≥ 1 := Nat.one_le_two_pow
        rw [show 2 ^ M - 1 + 1 = 2 ^ M from by omega]
        exact isPow2_of_pow _
    · -- Backward (contrapositive): countP ≥ 3 → i < 2^(M-2)
      intro h_ge3
      by_contra h_not_lt; push_neg at h_not_lt
      have h_bound : (List.range' i (n - 1 - i)).countP isPow2' ≤ 2 := by
        apply countP_le_two_of_two_values hnd isPow2'
          (a := 2 ^ (M - 1) - 1) (b := 2 ^ M - 1)
        intro x hx hpx
        simp only [List.mem_range'] at hx
        obtain ⟨idx, hidx_lt, hidx_eq⟩ := hx
        obtain ⟨k, hk⟩ := (isPowerOfTwo_iff (x + 1)).mp hpx
        have hk_ge : k ≥ M - 1 := by
          by_contra h_not; push_neg at h_not
          have : 2 ^ k ≤ 2 ^ (M - 2) :=
            Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
          omega
        have hk_le : k ≤ M := by
          have h2k : 2^k ≤ n - 1 := by omega
          exact (Nat.le_log2 (show n - 1 ≠ 0 by omega)).mpr h2k
        have : k = M - 1 ∨ k = M := by omega
        rcases this with rfl | rfl <;> [left; right] <;> omega
      omega
  · -- Small case: n ≤ 4
    push_neg at hn
    have h_zero : nextPow2 n / 8 = 0 := by
      interval_cases n <;> decide
    rw [h_zero]
    constructor
    · omega
    · intro h; exfalso
      interval_cases n <;> interval_cases i <;> revert h <;> decide

/-! ## Part 3: Definitions and Main Theorem -/

/-- Marks positions where i+1 is a power of 2. -/
def mark_pow2_v (n : ℕ) : List Bool :=
  (List.range n).map (fun i => isPowerOfTwo (i + 1))

/-- Target: position i is true iff i < nextPow2(n)/8. -/
def threshold_v (n : ℕ) : List Bool :=
  (List.range n).map (fun i => decide (i < nextPow2 n / 8))

@[simp] lemma mark_pow2_v_length : (mark_pow2_v n).length = n := by simp [mark_pow2_v]
@[simp] lemma threshold_v_length : (threshold_v n).length = n := by simp [threshold_v]

/-! ### Bridge: marks_from_i_excl_last' n i = (mark_pow2_v n).drop(i).dropLast.count(true) -/

/-- The `marks_from_i_excl_last'` (inline definition) equals the count on `mark_pow2_v`. -/
private lemma marks_eq_mark_pow2 (n i : ℕ) :
    marks_from_i_excl_last' n i = ((mark_pow2_v n).drop i).dropLast.count true := by
  show (let mark_pow2 := (List.range n).map (fun j => isPowerOfTwo (j + 1))
        mark_pow2.drop i |>.dropLast |>.count true) = _
  dsimp only [mark_pow2_v]

/-! ### Bridge: FST output condition ↔ marks_from_i ≥ 3

The FST outputs true at position i iff:
  suffix_count ≥ 3 ∨ (suffix_count = 2 ∧ w[i] = true)
where suffix_count = w.drop(i+1).dropLast.count(true)

This equals marks_from_i ≥ 3 because:
  marks_from_i = w.drop(i).dropLast.count(true)
              = suffix_count + (if w[i] then 1 else 0)  [when i < n-1]
              = 0                                         [when i = n-1]
-/

private lemma drop_cons_dropLast_count (w : List Bool) (i : ℕ) (hi : i < w.length)
    (hi2 : i + 1 < w.length) :
    (w.drop i).dropLast.count true =
    (w.drop (i + 1)).dropLast.count true + if w[i] = true then 1 else 0 := by
  have hne : w.drop (i + 1) ≠ [] := by
    intro h; simp [List.drop_eq_nil_iff] at h; omega
  have key : (w.drop i).dropLast = w[i] :: (w.drop (i + 1)).dropLast := by
    rw [List.drop_eq_getElem_cons hi, List.dropLast_cons_of_ne_nil hne]
  rw [key]
  cases hw : w[i] <;> simp

/-- Bridge: the FST output condition matches marks ≥ 3. -/
private lemma bridge (n i : ℕ) (hi : i < n) :
    ((mark_pow2_v n).drop (i + 1)).dropLast.count true ≥ 3 ∨
    ((mark_pow2_v n).drop (i + 1)).dropLast.count true = 2 ∧
      (mark_pow2_v n)[i]'(by simp; exact hi) = true
    ↔ marks_from_i_excl_last' n i ≥ 3 := by
  rw [marks_eq_mark_pow2]
  by_cases hlast : i = n - 1
  · -- Last position: suffix is empty
    subst hlast
    have hc0 : ((mark_pow2_v n).drop n).dropLast.count true = 0 := by
      simp [List.drop_eq_nil_of_le]
    have hm0 : ((mark_pow2_v n).drop (n - 1)).dropLast.count true = 0 := by
      have hlen : (mark_pow2_v n).length = n := by simp
      have h1 := List.drop_eq_getElem_cons (show n - 1 < (mark_pow2_v n).length by omega)
      simp only [h1]
      have h2 : (mark_pow2_v n).drop (n - 1 + 1) = [] :=
        List.drop_eq_nil_of_le (by omega)
      simp [h2]
    have hc0' : ((mark_pow2_v n).drop (n - 1 + 1)).dropLast.count true = 0 := by
      have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      rw [hn1]; exact hc0
    simp [hc0', hm0]
  · -- Not last position: can decompose drop i = w[i] :: drop (i+1)
    have hi2 : i + 1 < n := by omega
    have hlen : (mark_pow2_v n).length = n := by simp
    set c := ((mark_pow2_v n).drop (i + 1)).dropLast.count true with hc_def
    set m := ((mark_pow2_v n).drop i).dropLast.count true with hm_def
    have h_total : m = c + if (mark_pow2_v n)[i]'(by simp; exact hi) = true then 1 else 0 := by
      rw [hm_def]
      exact drop_cons_dropLast_count _ _ (by simp [mark_pow2_v]; exact hi) (by simp [mark_pow2_v]; exact hi2)
    constructor
    · rintro (hge3 | ⟨heq2, hwi⟩)
      · have : m ≥ c := by
          rw [h_total]; omega
        omega
      · rw [heq2, hwi] at h_total; simp at h_total; omega
    · intro hge3
      cases hwi : (mark_pow2_v n)[i]'(by simp; exact hi) <;> simp [hwi] at h_total
      · left; omega
      · by_cases hc3 : c ≥ 3
        · left; exact hc3
        · right
          have : c = 2 := by omega
          exact ⟨this, rfl⟩

/-! ### Per-element theorem -/

private lemma bFST_scanr_mark_pow2_getElem (n i : ℕ) (hi : i < n) :
    (bFST.scanr (mark_pow2_v n))[i]'(by simp; exact hi) =
    decide (i < nextPow2 n / 8) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,
      bFST_scanr_getElem (mark_pow2_v n) i (by simp; exact hi),
      bridge n i hi]
  exact (threshold_iff_marks_ge_3 n i hi).symm

/-! ### Main Theorem -/

/-- The main theorem: FST.scanr (mark_pow2 n) = threshold n. -/
theorem bFST_scanr_mark_pow2_eq_threshold (n : ℕ) :
    bFST.scanr (mark_pow2_v n) = threshold_v n := by
  apply List.ext_getElem
  · simp [threshold_v]
  intro i hi1 hi2
  have hi : i < n := by simp [threshold_v] at hi2; exact hi2
  rw [bFST_scanr_mark_pow2_getElem n i hi]
  simp [threshold_v, hi]

/-! ## Tests -/

section Tests

/-- FST-independent function: position i is true iff ≥3 marks in w[i..n-2] (excluding last). -/
private def g (w : List Bool) : List Bool :=
  (List.range w.length).map fun i =>
    (w.drop i).dropLast.count true ≥ 3

-- Test mark_pow2_v
#eval mark_pow2_v 0   -- []
#eval mark_pow2_v 1   -- [true]  (pos 0: 1 = 2^0)
#eval mark_pow2_v 4   -- [T, T, F, T]  (pos 0,1,3)
#eval mark_pow2_v 8   -- [T, T, F, T, F, F, F, T]  (pos 0,1,3,7)
#eval mark_pow2_v 16

-- Test threshold_v
#eval threshold_v 0   -- []
#eval threshold_v 8   -- [T, F, F, F, F, F, F, F] (nextPow2(8)=8, /8=1)
#eval threshold_v 9   -- [T, T, F, F, F, F, F, F, F] (nextPow2(9)=16, /8=2)
#eval threshold_v 16

-- Test g on mark_pow2_v
#eval g (mark_pow2_v 8)   -- Should be [T, F, F, F, F, F, F, F]
#eval g (mark_pow2_v 9)   -- Should be [T, T, F, F, F, F, F, F, F]
#eval g (mark_pow2_v 16)

-- Test FST on mark_pow2_v
#eval bFST.scanr (mark_pow2_v 8)
#eval bFST.scanr (mark_pow2_v 9)
#eval bFST.scanr (mark_pow2_v 16)

-- Batch verification
#eval (List.range 32).all fun n => g (mark_pow2_v n) == threshold_v n
#eval (List.range 32).all fun n => bFST.scanr (mark_pow2_v n) == g (mark_pow2_v n)

end Tests

end CellularAutomatas
