import CellularAutomatas.proofs.x_prefix_fst_semantics
import CellularAutomatas.proofs.x_prefix_threshold_equiv
import Mathlib.Tactic.IntervalCases

/-!
# xPrefixAdvice Two-Stage: Core Combinatorial Theorem

Proves `bFST.scanr (mark_pow2_v n) = threshold_v n` by combining:
- FST semantics from `x_prefix_fst_semantics`
- Threshold equivalence from `x_prefix_threshold_equiv`

Both `bFST` and `marks_from_i_excl_last'` are defined in the imported files.
We define `mark_pow2_v` and `threshold_v` here and bridge the definitions.
-/

namespace CellularAutomatas

open CellAutomaton

/-! ## Definitions -/

/-- Marks positions where i+1 is a power of 2. -/
def mark_pow2_v (n : ℕ) : List Bool :=
  (List.range n).map (fun i => isPowerOfTwo (i + 1))

/-- Target: position i is true iff i < nextPow2(n)/8. -/
def threshold_v (n : ℕ) : List Bool :=
  (List.range n).map (fun i => decide (i < nextPow2 n / 8))

@[simp] lemma mark_pow2_v_length : (mark_pow2_v n).length = n := by simp [mark_pow2_v]
@[simp] lemma threshold_v_length : (threshold_v n).length = n := by simp [threshold_v]

/-! ## Bridge: marks_from_i_excl_last' n i = (mark_pow2_v n).drop(i).dropLast.count(true)

`marks_from_i_excl_last'` from threshold_equiv uses an inline `let` definition.
We show it equals the same computation on `mark_pow2_v`. -/

/-- The imported `marks_from_i_excl_last'` equals the count on `mark_pow2_v`. -/
private lemma marks_eq_mark_pow2 (n i : ℕ) :
    marks_from_i_excl_last' n i = ((mark_pow2_v n).drop i).dropLast.count true := by
  show (let mark_pow2 := (List.range n).map (fun j => isPowerOfTwo (j + 1))
        mark_pow2.drop i |>.dropLast |>.count true) = _
  dsimp only [mark_pow2_v]

/-! ## Bridge: FST output condition ↔ marks_from_i ≥ 3

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
      · -- c ≥ 3 → m ≥ 3 (since m ≥ c by h_total)
        have : m ≥ c := by
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

/-! ## Per-element theorem -/

private lemma bFST_scanr_mark_pow2_getElem (n i : ℕ) (hi : i < n) :
    (bFST.scanr (mark_pow2_v n))[i]'(by simp; exact hi) =
    decide (i < nextPow2 n / 8) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,
      bFST_scanr_getElem (mark_pow2_v n) i (by simp; exact hi),
      bridge n i hi]
  exact (threshold_iff_marks_ge_3 n i hi).symm

/-! ## Main Theorem -/

/-- The main theorem: FST.scanr (mark_pow2 n) = threshold n. -/
theorem bFST_scanr_mark_pow2_eq_threshold (n : ℕ) :
    bFST.scanr (mark_pow2_v n) = threshold_v n := by
  apply List.ext_getElem
  · simp [threshold_v]
  intro i hi1 hi2
  have hi : i < n := by simp [threshold_v] at hi2; exact hi2
  rw [bFST_scanr_mark_pow2_getElem n i hi]
  simp [threshold_v, hi]

end CellularAutomatas
