import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.exp_middle_two_stage
import CellularAutomatas.proofs.nextpow2
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases

/-!
# X_PREFIX PARALLEL PROOF 3: Threshold Characterization

Proves: `i < nextPow2(n) / 8 ↔ ≥3 power-of-2 marks in [i..n-2]`
-/

namespace CellularAutomatas

open CellAutomaton

/-- Count of marks in mark_pow2(n)[i..n-2]. -/
def marks_from_i_excl_last' (n i : ℕ) : ℕ :=
  let mark_pow2 := (List.range n).map (fun j => isPowerOfTwo (j + 1))
  mark_pow2.drop i |>.dropLast |>.count true

/-! ## List-level helpers -/

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

/-! ## Counting helpers -/

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

/-! ## Properties of nextPow2 -/

/-! ## Main Theorem -/

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
    -- Power-of-2 ordering facts for omega
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
      -- Membership: each 2^k-1 is in [i, ..., n-2]
      · exact List.mem_range'.mpr ⟨2 ^ (M - 2) - 1 - i, by omega, by omega⟩
      · exact List.mem_range'.mpr ⟨2 ^ (M - 1) - 1 - i, by omega, by omega⟩
      · exact List.mem_range'.mpr ⟨2 ^ M - 1 - i, by omega, by omega⟩
      -- isPowerOfTwo: 2^k - 1 + 1 = 2^k
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

/-- For small `n` (≤ 4), both sides of the threshold equivalence are false. -/
lemma threshold_equiv_small (n i : ℕ) (hi : i < n) (hn : n ≤ 4) :
    ¬(i < nextPow2 n / 8) ∧ marks_from_i_excl_last' n i < 3 := by
  constructor
  · have : nextPow2 n / 8 = 0 := by interval_cases n <;> decide
    omega
  · have h_iff := threshold_iff_marks_ge_3 n i hi
    have : nextPow2 n / 8 = 0 := by interval_cases n <;> decide
    omega

end CellularAutomatas
