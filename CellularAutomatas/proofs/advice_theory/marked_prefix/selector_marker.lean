import CellularAutomatas.proofs.advice_theory.marked_prefix.prefix_reversal

/-!
# The dyadic selector and the existing exponential marker

The one-based marker `middle_exp_idx` is exactly the selected prefix length.
Consequently its zero-based marked cell is `dyadicSelector n - 1`.
-/

namespace CellularAutomatas.MarkedPrefix

variable {α : Type}

theorem dyadicSelector_eq_pow {n : ℕ} (hn : 2 ≤ n) :
    dyadicSelector n = 2 ^ (Nat.log2 n - 1) := by
  simp [dyadicSelector, show ¬n < 2 by omega]

/-- The selected prefix occupies at most half of the input. -/
theorem dyadicSelector_le_half (n : ℕ) :
    dyadicSelector n ≤ n / 2 := by
  by_cases hn : n < 2
  · simp [dyadicSelector, hn]
  · have hn2 : 2 ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hlog : 1 ≤ Nat.log2 n := by
      have hpos := Nat.log_pos (by omega : 1 < 2) hn2
      rw [← Nat.log2_eq_log_two] at hpos
      omega
    rw [dyadicSelector_eq_pow hn2]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    rw [← pow_succ, Nat.sub_add_cancel hlog]
    exact Nat.log2_self_le hn0

/-- From length two onward the selected prefix is nonempty. -/
theorem dyadicSelector_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < dyadicSelector n := by
  rw [dyadicSelector_eq_pow hn]
  exact Nat.two_pow_pos _

/-- The corresponding zero-based marker position is inside the input. -/
theorem dyadicSelector_pred_lt {n : ℕ} (hn : 2 ≤ n) :
    dyadicSelector n - 1 < n := by
  have hpos := dyadicSelector_pos hn
  have hbound := dyadicSelector.bound n
  omega

private lemma exponent_lt_length {n : ℕ} (hn : 2 ≤ n) :
    Nat.log2 n - 1 < n := by
  calc
    Nat.log2 n - 1 < 2 ^ (Nat.log2 n - 1) := Nat.lt_two_pow_self
    _ = dyadicSelector n := (dyadicSelector_eq_pow hn).symm
    _ ≤ n := dyadicSelector.bound n

/-- The legacy one-based exponential-middle marker is exactly the dyadic
selected-prefix length. -/
theorem middle_exp_idx_eq_dyadicSelector (n : ℕ) :
    middle_exp_idx n =
      if n < 2 then none else some (dyadicSelector n) := by
  by_cases hn : n < 2
  · rw [if_pos hn]
    have hn_cases : n = 0 ∨ n = 1 := by omega
    rcases hn_cases with rfl | rfl <;> simp [middle_exp_idx]
  · rw [if_neg hn]
    have hn2 : 2 ≤ n := by omega
    have hlog : 1 ≤ Nat.log2 n := by
      have hpos := Nat.log_pos (by omega : 1 < 2) hn2
      rw [← Nat.log2_eq_log_two] at hpos
      omega
    have hpow : dyadicSelector n = 2 ^ (Nat.log2 n - 1) :=
      dyadicSelector_eq_pow hn2
    unfold middle_exp_idx
    apply List.max?_eq_some_iff.mpr
    constructor
    · rw [List.mem_filter, List.mem_map]
      refine ⟨⟨Nat.log2 n - 1, ?_, hpow.symm⟩, ?_⟩
      · simp only [List.mem_range]
        exact exponent_lt_length hn2
      · simp only [decide_eq_true_eq]
        exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp
          (dyadicSelector_le_half n)
    · intro x hx
      rw [List.mem_filter, List.mem_map] at hx
      obtain ⟨⟨k, _hk_range, rfl⟩, hk⟩ := hx
      simp only [decide_eq_true_eq] at hk
      have hkpow : 2 ^ (k + 1) ≤ n := by
        rw [pow_succ]
        exact hk
      have hkle : k + 1 ≤ Nat.log2 n := by
        rw [Nat.log2_eq_log_two]
        exact Nat.le_log_of_pow_le Nat.one_lt_two hkpow
      rw [hpow]
      exact Nat.pow_le_pow_right (by omega) (by omega)

private lemma add_one_eq_iff_eq_pred {i m : ℕ} (hm : 0 < m) :
    i + 1 = m ↔ i = m - 1 := by
  omega

/-- On nontrivial words, `middle_exp` annotates exactly the zero-based cell
immediately before the selected-prefix boundary. -/
theorem middle_exp_annotate_eq_mapIdx (w : Word α) (hn : 2 ≤ w.length) :
    (Advice.middle_exp α).annotate w =
      w.mapIdx fun i a =>
        (a, decide (i = dyadicSelector w.length - 1)) := by
  change
    w ⨂ ((List.range w.length).map fun i =>
      some (i + 1) == middle_exp_idx w.length) =
      w.mapIdx fun i a =>
        (a, decide (i = dyadicSelector w.length - 1))
  apply List.ext_getElem (by simp)
  intro i hi _
  have hsmall : ¬w.length < 2 := by omega
  have hpos : 0 < dyadicSelector w.length := dyadicSelector_pos hn
  simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
    List.getElem_mapIdx]
  apply Prod.ext
  · rfl
  · change
      (some (i + 1) == middle_exp_idx w.length) =
        decide (i = dyadicSelector w.length - 1)
    rw [middle_exp_idx_eq_dyadicSelector, if_neg hsmall,
      Option.some_beq_some, Bool.beq_eq_decide_eq]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_iff] using add_one_eq_iff_eq_pred hpos

end CellularAutomatas.MarkedPrefix
