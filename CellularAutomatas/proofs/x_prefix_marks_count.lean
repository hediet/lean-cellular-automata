import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.exp_middle_two_stage
import Mathlib.Data.Nat.Log

/-!
# X_PREFIX PARALLEL PROOF 2: Marks Characterization

This file proves properties about `mark_pow2` - the list that marks positions
where i+1 is a power of 2.

## Goal
Prove `marks_from_i_excl_last_eq`: the count of marks in positions [i..n-2]
equals the number of powers of 2 in the range.

## Key Facts
- mark_pow2(n) marks position i iff i+1 ∈ {1, 2, 4, 8, 16, ...}
- Position i is marked iff i ∈ {0, 1, 3, 7, 15, 31, ...} = {2^k - 1 : k ≥ 0}
- marks_from_i_excl_last counts marks in [i, n-2]
-/

namespace CellularAutomatas

open CellAutomaton

/-! ## Definitions -/

/-- Marks positions where i+1 is a power of 2: positions 0, 1, 3, 7, 15, ... -/
def mark_pow2_v (n : ℕ) : List Bool :=
  (List.range n).map (fun i => isPowerOfTwo (i + 1))

/-- Count of marks in mark_pow2(n)[i..n-2] (excluding last position). -/
def marks_from_i_excl_last (n i : ℕ) : ℕ :=
  (mark_pow2_v n).drop i |>.dropLast |>.count true

/-! ## Basic Lemmas -/

@[simp] lemma mark_pow2_v_length (n : ℕ) : (mark_pow2_v n).length = n := by simp [mark_pow2_v]

lemma mark_pow2_v_getElem (n i : ℕ) (hi : i < n) :
    (mark_pow2_v n)[i]'(by simp; exact hi) = isPowerOfTwo (i + 1) := by
  simp only [mark_pow2_v, List.getElem_map, List.getElem_range]

/-- Position i is marked iff (i+1) is a power of 2, i.e., i = 2^k - 1 for some k. -/
lemma mark_iff_pow2_minus_one (n i : ℕ) (hi : i < n) :
    (mark_pow2_v n)[i]'(by simp; exact hi) = true ↔ ∃ k : ℕ, i = 2^k - 1 := by
  rw [mark_pow2_v_getElem n i hi, isPowerOfTwo_iff]
  -- isPowerOfTwo (i+1) = true ↔ ∃ k, i+1 = 2^k, which is ↔ ∃ k, i = 2^k - 1
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by have := Nat.one_le_two_pow (n := k); omega⟩

/-! ## Helper Lemmas -/

/-- mark_pow2_v is the map of `isPowerOfTwo (· + 1)` on `List.range n`. -/
private lemma mark_pow2_v_eq (n : ℕ) :
    mark_pow2_v n = (List.range n).map (fun j => isPowerOfTwo (j + 1)) := rfl

/-- The drop-dropLast sublist equals mapping over the range [i..n-2]. -/
private lemma marks_drop_dropLast_eq (n i : ℕ) (hi : i < n) :
    ((mark_pow2_v n).drop i).dropLast =
    (List.range (n - 1 - i)).map (fun j => isPowerOfTwo (i + j + 1)) := by
  apply List.ext_getElem
  · simp [mark_pow2_v, List.length_dropLast]
    omega
  intro j hj1 hj2
  rw [List.getElem_dropLast]
  simp only [mark_pow2_v, List.getElem_drop, List.getElem_map, List.getElem_range]

/-- Counting true in a mapped Bool list equals filtering. -/
private lemma count_true_map_eq_filter (m : ℕ) (P : ℕ → Bool) :
    ((List.range m).map P).count true = ((List.range m).filter (fun j => P j)).length := by
  simp only [List.count_eq_countP, List.countP_map]
  have h : ((fun x => x == true) ∘ P) = (fun j => decide (P j = true)) := rfl
  rw [h, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro x _
  simp [Bool.decide_eq_true]

/-! ## Main Theorem -/

private lemma isPowerOfTwo_pow2' (k : ℕ) : isPowerOfTwo (2^k) = true := by
  rw [isPowerOfTwo_iff]; exact ⟨k, rfl⟩

/-- The map `k ↦ 2^k - 1 - i` is injective on elements satisfying `i ≤ 2^k - 1`. -/
private lemma nodup_filtered_map (n i : ℕ) :
    (((List.range (Nat.log2 (n - 1) + 1)).filter
      (fun k => decide (i ≤ 2^k - 1 ∧ 2^k - 1 ≤ n - 2))).map
      (fun k => 2^k - 1 - i)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  have hnd : ((List.range (Nat.log2 (n - 1) + 1)).filter
      (fun k => decide (i ≤ 2^k - 1 ∧ 2^k - 1 ≤ n - 2))).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [List.Nodup] at hnd
  exact hnd.imp_of_mem fun {a} {b} ha hb hab h => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at ha hb
    exfalso
    exact hab (Nat.pow_right_injective (by omega : 1 < 2) (show 2^a = 2^b by
      have h1a := Nat.one_le_two_pow (n := a)
      have h2a : i ≤ 2^a - 1 := ha.2.1
      have h1b := Nat.one_le_two_pow (n := b)
      have h2b : i ≤ 2^b - 1 := hb.2.1
      omega))

/-- Positions `j` with `isPowerOfTwo(i+j+1)` in `[0, n-1-i)` correspond bijectively to
    `k` with `i ≤ 2^k-1 ≤ n-2`, via `j = 2^k - 1 - i`. -/
private lemma filter_perm_mapped (n i : ℕ) (hi : i < n) (hn : n ≥ 2) :
    ((List.range (n - 1 - i)).filter (fun j => isPowerOfTwo (i + j + 1))).Perm
    (((List.range (Nat.log2 (n - 1) + 1)).filter
      (fun k => decide (i ≤ 2^k - 1 ∧ 2^k - 1 ≤ n - 2))).map (fun k => 2^k - 1 - i)) := by
  rw [List.perm_ext_iff_of_nodup]
  · intro x
    simp only [List.mem_filter, List.mem_range, List.mem_map, decide_eq_true_eq]
    constructor
    · -- x in LHS → x in RHS
      intro ⟨hx, hpow⟩
      rw [isPowerOfTwo_iff] at hpow
      obtain ⟨k, hk⟩ := hpow
      refine ⟨k, ⟨?_, ?_, ?_⟩, ?_⟩
      · show k < Nat.log2 (n - 1) + 1
        rw [Nat.log2_eq_log_two]
        exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by omega) (by omega : 2^k ≤ n - 1))
      · show i ≤ 2^k - 1
        have := Nat.one_le_two_pow (n := k); omega
      · show 2^k - 1 ≤ n - 2; omega
      · show 2^k - 1 - i = x
        have := Nat.one_le_two_pow (n := k); omega
    · -- x in RHS → x in LHS
      rintro ⟨k, ⟨_, hge, hle⟩, rfl⟩
      refine ⟨by omega, ?_⟩
      have h2 : i + (2^k - 1 - i) + 1 = 2^k := by have := Nat.one_le_two_pow (n := k); omega
      rw [h2]; exact isPowerOfTwo_pow2' k
  · exact List.Nodup.filter _ List.nodup_range
  · exact nodup_filtered_map n i

/-- The marks in [i..n-2] are exactly {2^k - 1 : i ≤ 2^k - 1 ≤ n - 2}. -/
theorem marks_from_i_excl_last_eq (n i : ℕ) (hi : i < n) (hn : n ≥ 2) :
    marks_from_i_excl_last n i =
    ((List.range (Nat.log2 (n - 1) + 1)).filter fun k => i ≤ 2^k - 1 ∧ 2^k - 1 ≤ n - 2).length := by
  unfold marks_from_i_excl_last
  rw [marks_drop_dropLast_eq n i hi, count_true_map_eq_filter]
  have hperm := filter_perm_mapped n i hi hn
  rw [hperm.length_eq, List.length_map]

/-- Alternative characterization: count = number of k where 2^k ∈ (i, n-1]. -/
lemma marks_from_i_excl_last_eq' (n i : ℕ) (hi : i < n) (hn : n ≥ 2) :
    marks_from_i_excl_last n i =
    ((List.range (Nat.log2 n + 1)).filter fun k => i < 2^k ∧ 2^k ≤ n - 1).length := by
  rw [marks_from_i_excl_last_eq n i hi hn]
  -- Show the two filtered ranges select the same elements via Perm.
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup]
  · intro k
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro ⟨hk, h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · calc k < Nat.log2 (n - 1) + 1 := hk
          _ ≤ Nat.log2 n + 1 := by
            apply Nat.succ_le_succ
            rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
            exact Nat.log_mono_right (by omega)
      · have := Nat.one_le_two_pow (n := k); omega
      · omega
    · intro ⟨hk, h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.log2_eq_log_two]
        exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by omega) h2)
      · have := Nat.one_le_two_pow (n := k); omega
      · omega
  · exact List.nodup_range.filter _
  · exact List.nodup_range.filter _

end CellularAutomatas
