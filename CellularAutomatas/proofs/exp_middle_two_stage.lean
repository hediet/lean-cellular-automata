import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.constructions.basic_exp_word
import CellularAutomatas.proofs.advice_prefix_mem_rt_closed
import CellularAutomatas.proofs.word_ops
import Mathlib.Data.Nat.Log

/-!
# exp_middle is a Two-Stage Advice

## Proof Idea

`Advice.exp_middle α` marks position `2^k - 1` (0-indexed) where k is the largest
satisfying `2^(k+1) ≤ n`.

### Two-Stage Decomposition

1. **CArtTransducer C:** Use `exp_word_ca` — its `trace_rt` outputs true at position i
   iff prefix of length i+1 is accepted, i.e., iff i+1 = 2^k for some k.
   This marks positions 0, 1, 3, 7, 15, ... (i.e., 2^k - 1 for all valid k).

2. **FST M:** "Select second true" — scanning right-to-left, outputs true only for
   the second true encountered, false for all others.

### Why this works

- prefix_mem marks ALL positions where prefix length is a power of 2
- exp_middle marks the SECOND-TO-LAST such position (from the left)
- When scanning right-to-left, "second true" = second-to-last from left

Examples:
- n=4: prefix_mem marks 0,1,3. exp_middle marks 1 (second from right = second-to-last from left) ✓
- n=8: prefix_mem marks 0,1,3,7. exp_middle marks 3 ✓
- n=2: prefix_mem marks 0,1. exp_middle marks 0 ✓
- n=1: prefix_mem marks 0. exp_middle marks nothing (no second) ✓
-/

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [Alphabet α]

/-! ## Helpers -/

def isPowerOfTwo (n : ℕ) : Bool := n > 0 && n = 2 ^ (Nat.log2 n)

lemma isPowerOfTwo_iff (n : ℕ) : isPowerOfTwo n = true ↔ ∃ k, n = 2 ^ k := by
  unfold isPowerOfTwo
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hn_pos, hn_eq⟩
    exact ⟨Nat.log2 n, hn_eq⟩
  · rintro ⟨k, rfl⟩
    refine ⟨Nat.one_le_two_pow, ?_⟩
    rw [Nat.log2_eq_log_two]
    simp

/-! ## Stage 1: Advice marking positions where i+1 is a power of 2

`Advice.exp1` marks positions 0, 1, 3, 7, 15, ... (where prefix length i+1 = 2^k).
-/

section Stage1

  /-- Marks position i iff i+1 is a power of 2. -/
  def Advice.exp1 : Advice α Bool :=
    { f := fun w => (List.range w.length).map fun i => isPowerOfTwo (i + 1) }

  /-- The CArt that computes `Advice.exp1` via `exp_word_ca`. -/
  def exp_prefix_CA : CArtTransducer α Bool :=
    (exp_word_ca.map_embed (fun _ => ())).toCellAutomaton

  private lemma exp_word_ca_mem_CA_rt : exp_word_ca ∈ CA_rt Unit := by
    simp only [CA_rt, t_rt, CA, tCellAutomata, Set.mem_setOf_eq, Set.mem_univ, true_and]
    exact ⟨funext (fun _ => rfl), fun _ => rfl⟩

  @[simp] private lemma exp_word_ca_mem_L_iff (w : Word Unit) :
      w ∈ exp_word_ca.L ↔ isPowerOfTwo w.length = true := by
    simp only [tCellAutomaton.L, exp_word_ca_correct, isPowerOfTwo_iff]
    rfl

  lemma exp_prefix_CA_trace_spec {α: Type} (w : Word α) (i : ℕ) (hi : i < w.length) :
      (exp_prefix_CA.trace_rt w)[i]'(by simp [hi]) = isPowerOfTwo (i + 1) := by
    unfold exp_prefix_CA
    simp only [tCellAutomaton.map_embed_trace_rt]
    rw [trace_rt_getElem_i_iff2 (C := ⟨exp_word_ca, exp_word_ca_mem_CA_rt⟩)]
    simp [show (i + 1) ≤ List.length w by omega]

  /-- `exp_prefix_CA.trace_rt` computes `Advice.exp1`. -/
  theorem exp_prefix_CA_eq_exp1 : exp_prefix_CA.advice = (Advice.exp1 : Advice α Bool) := by
    apply advice_eq_iff
    funext w
    -- Both sides are lists of length w.length
    -- LHS: exp_prefix_CA.trace_rt w
    -- RHS: (range w.length).map (fun i => isPowerOfTwo (i + 1))
    simp only [CArtTransducer.advice, Advice.exp1]
    apply List.ext_getElem
    · simp
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range] at hi2 ⊢
    have hi : i < w.length := by simp at hi1; exact hi1
    -- Use exp_prefix_CA_trace_spec directly
    exact exp_prefix_CA_trace_spec w i hi

  /-- `Advice.exp1` is a CArt advice. -/
  theorem exp1_is_cart_advice : (Advice.exp1 : Advice α Bool).is_cart_advice :=
    ⟨exp_prefix_CA, exp_prefix_CA_eq_exp1⟩

end Stage1

/-! ## Stage 2: Advice that marks the second-to-last true position

`Advice.mark_second_last` marks the second-to-last true position in a boolean word.
We define it declaratively via `second_last_true_idx`, then show it equals an FST-based
formulation (`select_2nd`) for proving it's FST-computable.
-/

section Stage2

  /-- Index of the second-to-last `true` position (0-indexed), if it exists. -/
  def second_last_true_idx (w : Word Bool) : Option ℕ :=
    let truePositions := (List.range w.length).filter (fun i => w[i]!)
    if truePositions.length ≥ 2
    then truePositions[truePositions.length - 2]?
    else none

  /-- Marks the second-to-last `true` position in a boolean word.
      Uses `from_marker` with 1-indexed adjustment. -/
  def Advice.mark_second_last : Advice Bool Bool :=
    Advice.from_marker (fun w => (second_last_true_idx w).map (· + 1))

  /-- Alternative characterization: position i is marked iff w[i] = true and exactly one
      true exists after position i. This formulation is what the FST computes. -/
  def Advice.select_2nd : Advice Bool Bool :=
    { f := fun w => (List.range w.length).map fun i =>
        w[i]! && (w.drop (i + 1)).count true == 1 }

  -- Helper type for FST state
  inductive TrueCount
    | zero   -- No trues seen yet
    | one    -- Exactly one true seen
    | two    -- Two or more trues seen
  deriving DecidableEq, Repr, Fintype, Inhabited

  def TrueCount.fromCount : ℕ → TrueCount
    | 0 => .zero
    | 1 => .one
    | _ => .two

  def TrueCount.inc : TrueCount → TrueCount
    | .zero => .one
    | .one => .two
    | .two => .two

  /-- FST that computes `Advice.select_2nd` by scanning right-to-left. -/
  def select_second_FST : FiniteStateTransducer Bool Bool := {
    Q := TrueCount × Bool  -- (count, output_for_this_position)
    δ := fun (count, _) input =>
      match count, input with
      | .zero, false => (.zero, false)
      | .zero, true  => (.one, false)   -- First true: don't output
      | .one, false  => (.one, false)
      | .one, true   => (.two, true)    -- Second true: output!
      | .two, _      => (.two, false)   -- Already found second, no more output
    q0 := (.zero, false)
    f := fun (_, output) => output
  }

  private lemma select_second_δ_fst' (state : TrueCount × Bool) (input : Bool) :
      (select_second_FST.δ state input).1 =
        if input then state.1.inc else state.1 := by
    rcases state with ⟨count, out⟩
    cases count <;> cases input <;> rfl

  private lemma select_second_δ_snd' (state : TrueCount × Bool) (input : Bool) :
      (select_second_FST.δ state input).2 =
        (input && state.1 == .one) := by
    rcases state with ⟨count, out⟩
    cases count <;> cases input <;> rfl

  def TrueCount_toNat : TrueCount → ℕ
    | .zero => 0
    | .one => 1
    | .two => 2

  private lemma TrueCount_inc_eq (tc : TrueCount) :
      tc.inc = TrueCount.fromCount (min (TrueCount_toNat tc + 1) 2) := by
    cases tc <;> decide

  private lemma TrueCount_toNat_fromCount_min (n : ℕ) :
      TrueCount_toNat (TrueCount.fromCount (min n 2)) = min n 2 := by
    match n with
    | 0 => decide
    | 1 => decide
    | n+2 => simp [TrueCount.fromCount, TrueCount_toNat]

  private lemma TrueCount_fromCount_eq_one_iff (n : ℕ) :
      (TrueCount.fromCount (min n 2) == TrueCount.one) = (n == 1) := by
    match n with
    | 0 => decide
    | 1 => decide
    | n+2 => simp [TrueCount.fromCount]

  private lemma TrueCount_fromCount_roundtrip (tc : TrueCount) :
      TrueCount.fromCount (min (TrueCount_toNat tc) 2) = tc := by
    cases tc <;> decide

  private lemma scanr_reduce_q_count (q : TrueCount × Bool) (w : Word Bool) :
      (select_second_FST.scanr_reduce_q q w).1 =
        TrueCount.fromCount (min (w.count true + TrueCount_toNat q.1) 2) := by
    induction w with
    | nil =>
      simp only [FiniteStateTransducer.scanr_reduce_q, List.count_nil, zero_add]
      exact (TrueCount_fromCount_roundtrip q.1).symm
    | cons c cs ih =>
      simp only [FiniteStateTransducer.scanr_reduce_q, select_second_δ_fst', ih]
      cases c
      · -- c = false
        simp [List.count_cons_of_ne (by decide : false ≠ true)]
      · -- c = true
        simp only [List.count_cons_self, ↓reduceIte, TrueCount_inc_eq]
        congr 1
        rw [TrueCount_toNat_fromCount_min]
        omega

  private lemma scanr_reduce_count (w : Word Bool) :
      (select_second_FST.scanr_reduce w).1 = TrueCount.fromCount (min (w.count true) 2) := by
    have := scanr_reduce_q_count select_second_FST.q0 w
    simp only [FiniteStateTransducer.scanr_reduce, select_second_FST, TrueCount_toNat] at this ⊢
    exact this

  private lemma select_second_FST_spec (w : Word Bool) (i : ℕ) (hi : i < w.length) :
      (select_second_FST.scanr w)[i]'(by simp; exact hi) =
        (w[i] && (w.drop (i + 1)).count true == 1) := by
    have h_eq := FiniteStateTransducer.scanr_get'_eq1 (M := select_second_FST) w ⟨i, hi⟩
    simp only [Fin.getElem_fin] at h_eq
    rw [h_eq]
    show select_second_FST.f (select_second_FST.δ (select_second_FST.scanr_reduce w⟦i + 1..*⟧) w[i]) = _
    rw [show select_second_FST.f (select_second_FST.δ (select_second_FST.scanr_reduce w⟦i + 1..*⟧) w[i]) =
            (select_second_FST.δ (select_second_FST.scanr_reduce w⟦i + 1..*⟧) w[i]).2 from rfl]
    rw [select_second_δ_snd']
    rw [scanr_reduce_count]
    rw [TrueCount_fromCount_eq_one_iff]

  /-- `select_second_FST.scanr` computes `Advice.select_2nd`. -/
  theorem select_second_FST_eq_select_2nd : select_second_FST.advice = Advice.select_2nd := by
    apply advice_eq_iff
    funext w
    simp only [FiniteStateTransducer.advice, Advice.select_2nd]
    apply List.ext_getElem
    · simp
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range] at *
    have hi : i < w.length := by simp at hi1; exact hi1
    rw [select_second_FST_spec w i hi]
    -- w[i]! = w[i] when i < w.length: use getElem?_eq_getElem and get! properties
    have h_eq : w[i]! = w[i] := by
      simp only [getElem!_def, List.getElem?_eq_getElem hi]
    rw [h_eq]

  /-! ### Equivalence between mark_second_last and select_2nd -/

  /-- In a strictly-sorted list, the count of elements > l[k] is length - (k+1). -/
  private lemma sorted_countP_gt (l : List ℕ) (hl : l.Sorted (· < ·)) (k : ℕ)
      (hk : k < l.length) :
      l.countP (· > l[k]) = l.length - (k + 1) := by
    induction l generalizing k with
    | nil => simp at hk
    | cons a as ih =>
      simp only [List.length_cons] at hk
      have has_sorted : as.Sorted (· < ·) := hl.of_cons
      rcases k with _ | k
      · -- k = 0: count elements > a in (a :: as)
        simp only [List.getElem_cons_zero, List.countP_cons,
                   show ¬(a > a) from by omega, decide_false, Bool.false_eq_true, ↓reduceIte,
                   Nat.zero_add, Nat.add_sub_cancel]
        rw [List.countP_eq_length_filter, List.filter_eq_self.mpr]
        · simp
        · intro x hx; simp [List.rel_of_sorted_cons hl x hx]
      · -- k > 0: recurse on as
        simp only [List.getElem_cons_succ, List.countP_cons]
        have h_a_le : ¬(a > as[k]) := by
          have hmem : as[k] ∈ as := List.getElem_mem (h := by omega)
          have := List.rel_of_sorted_cons hl as[k] hmem
          omega
        simp only [decide_eq_true_eq, h_a_le, Bool.false_eq_true, ↓reduceIte]
        rw [ih has_sorted k (by omega)]
        simp

  /-- i is in truePositions iff w[i]! is true and i < w.length. -/
  private lemma mem_truePositions_iff (w : Word Bool) (i : ℕ) :
      i ∈ (List.range w.length).filter (fun j => w[j]!) ↔ i < w.length ∧ w[i]! = true := by
    simp [List.mem_filter, List.mem_range]

  /-- A list's drop can be expressed as a map over a range suffix. -/
  private lemma list_drop_eq_map_range (l : List Bool) (k : ℕ) :
      l.drop k = ((List.range l.length).drop k).map (fun j => l[j]!) := by
    apply List.ext_getElem
    · simp
    intro i hi1 hi2
    have hi_bound : i + k < l.length := by
      rw [List.length_drop] at hi1; omega
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [getElem!_def, List.getElem?_eq_getElem (show k + i < l.length by omega)]

  /-- Filter (· > p) on range n = drop (p+1) of range n. -/
  private lemma range_filter_gt (n p : ℕ) :
      (List.range n).filter (· > p) = (List.range n).drop (p + 1) := by
    -- Both sides are [p+1, p+2, ..., n-1] if p+1 < n, else []
    -- Prove by showing both equal range' (p+1) (n - (p+1))
    suffices h : ∀ m, (List.range m).filter (· > p) = (List.range m).drop (p + 1) by exact h n
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.filter_append]
      simp only [List.filter_cons, List.filter_nil]
      by_cases hp : p < m
      · -- m > p, so m passes the filter
        simp only [show m > p from hp, decide_true, ↓reduceIte, List.nil_append, ih]
        -- (range m ++ [m]).drop (p+1) = (range m).drop (p+1) ++ [m]
        -- because (range m).length = m ≥ p+1
        symm
        rw [List.drop_append_of_le_length (by simp; omega)]
      · -- m ≤ p, so m doesn't pass
        push_neg at hp
        simp only [show ¬(m > p) from by omega, decide_false, ↓reduceIte, List.nil_append,
                   List.append_nil, ih]
        -- (range m ++ [m]).drop (p+1) = (range m).drop (p+1) ++ [m].drop (p+1-m)
        -- Since m ≤ p, p+1 > m, all elements get dropped
        rw [List.drop_append (l₁ := List.range m)]
        simp only [List.length_range]
        -- Both (range m).drop (p+1) and [m].drop (p+1-m) are []
        -- because m ≤ p implies p+1 > m and p+1-m ≥ 1
        have h1 : (List.range m).drop (p + 1) = [] := by
          apply List.drop_eq_nil_of_le; simp; omega
        have h2 : ([m] : List ℕ).drop (p + 1 - m) = [] := by
          apply List.drop_eq_nil_of_le; simp; omega
        rw [h1, h2]; simp

  /-- Count of trues after position p equals countP on truePositions. -/
  private lemma count_drop_eq_countP (w : Word Bool) (p : ℕ) :
      (w.drop (p + 1)).count true =
      ((List.range w.length).filter (fun j => w[j]!)).countP (· > p) := by
    rw [List.countP_filter, show (fun a => decide (a > p) && w[a]!) =
      (fun a => w[a]! && decide (a > p)) from by funext; rw [Bool.and_comm],
      ← List.countP_filter, List.count_eq_countP]
    -- Goal: (w.drop (p+1)).countP (·==true) = ((range n).filter (·>p)).countP (w[·]!)
    rw [range_filter_gt]
    rw [list_drop_eq_map_range]
    rw [List.countP_map]
    congr 1
    funext j
    simp [Function.comp]

  /-- The two formulations of selecting the second-to-last true are equivalent. -/
  theorem mark_second_last_eq_select_2nd : Advice.mark_second_last = Advice.select_2nd := by
    apply advice_eq_iff
    funext w
    simp only [Advice.mark_second_last, Advice.select_2nd, second_last_true_idx, Advice.from_marker]
    apply List.ext_getElem
    · simp
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range] at *
    have hi : i < w.length := by simp at hi1; exact hi1
    -- Use set to create a definitional equation that simp can use
    set tp := (List.range w.length).filter (fun j => w[j]!) with tp_def
    have tp_sorted : tp.Sorted (· < ·) :=
      tp_def ▸ List.Sorted.filter _ (List.sorted_lt_range w.length)
    have count_eq_countP : (w.drop (i + 1)).count true = tp.countP (· > i) :=
      tp_def ▸ count_drop_eq_countP w i
    -- Case split on w[i]
    by_cases hwi : w[i]! = true
    · -- w[i] is true → i ∈ tp
      have h_in : i ∈ tp := (mem_truePositions_iff w i |>.mpr ⟨hi, hwi⟩)
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem h_in
      -- hk_eq : tp[k] = i
      have h_count_val : (w.drop (i + 1)).count true = tp.length - (k + 1) := by
        rw [count_eq_countP, ← hk_eq, sorted_countP_gt tp tp_sorted k hk_lt]
      by_cases h2 : tp.length ≥ 2
      · by_cases hk2 : k = tp.length - 2
        · -- i = tp[len-2]: both sides true
          subst hk2
          simp only [h2, ↓reduceIte, List.getElem?_eq_getElem (show tp.length - 2 < tp.length by omega),
                     Option.map_some, hk_eq, hwi, h_count_val,
                     Bool.true_and, beq_self_eq_true, Bool.true_eq, beq_iff_eq]
          omega
        · -- i ≠ tp[len-2]: both sides false
          have h_val_ne : tp[k] ≠ tp[tp.length - 2] := by
            have hSM := tp_sorted.get_strictMono
            rcases Nat.lt_or_gt_of_ne hk2 with h | h
            · exact Nat.ne_of_lt (hSM h)
            · exact Nat.ne_of_gt (hSM h)
          -- Use same simp approach as case 1
          simp only [h2, ↓reduceIte, List.getElem?_eq_getElem (show tp.length - 2 < tp.length by omega),
                     Option.map_some, hwi, h_count_val,
                     Bool.true_and, beq_iff_eq]
          -- Goal: (i + 1 = tp[len-2] + 1) = (tp.length - (k+1) = 1)
          -- Both are false: tp[k]=i ≠ tp[len-2], and k ≠ len-2 so length-(k+1) ≠ 1
          have : ¬(i + 1 = tp[tp.length - 2] + 1) := by
            intro h; exact h_val_ne (by omega : tp[k] = tp[tp.length - 2])
          have : ¬(tp.length - (k + 1) = 1) := by omega
          simp_all
      · -- tp.length < 2: both sides false
        have h_tp_len : tp.length = 1 := by
          have : 0 < tp.length := List.length_pos_of_mem h_in; omega
        show (some (i + 1) == (if tp.length ≥ 2 then tp[tp.length - 2]? else none).map (· + 1)) =
             (w[i]! && ((w.drop (i + 1)).count true == 1))
        rw [if_neg (by omega), hwi, h_count_val]
        have hk0 : k = 0 := by omega
        subst hk0
        simp [h_tp_len, Option.map]
    · -- w[i] is false
      have hwi_false : w[i]! = false := by simpa using hwi
      by_cases h2 : tp.length ≥ 2
      · -- tp[len-2] ∈ tp, so w[tp[len-2]]=true but w[i]=false → i ≠ tp[len-2]
        have h_mem2 : tp[tp.length - 2] ∈ tp := List.getElem_mem (h := by omega)
        have h_mem2_filter := List.mem_filter.mp h_mem2
        have h_ne : tp[tp.length - 2] ≠ i := by
          intro hab; rw [← hab] at hwi_false; simp [h_mem2_filter.2] at hwi_false
        simp only [h2, ↓reduceIte, List.getElem?_eq_getElem (show tp.length - 2 < tp.length by omega),
                   Option.map_some, hwi_false, Bool.false_and]
        -- Goal: (some (i + 1) == some (tp[len-2] + 1)) = false
        -- This reduces to (i + 1 == tp[len-2] + 1) = false
        -- Which is decide (i + 1 = tp[len-2] + 1) = false, which holds by h_ne2
        have h_ne2 : ¬(i + 1 = tp[tp.length - 2] + 1) := by omega
        -- Just use simp_all with enough facts
        have h2b : 2 ≤ ((List.range w.length).filter (fun j => w[j]!)).length := h2
        have hlt : ((List.range w.length).filter (fun j => w[j]!)).length - 2 <
                   ((List.range w.length).filter (fun j => w[j]!)).length := by omega
        clear h_mem2 h_mem2_filter count_eq_countP
        simp_all [beq_iff_eq, Option.map, List.getElem?_eq_getElem, getElem!_def]
      · simp only [show ¬(tp.length ≥ 2) from by omega, ↓reduceIte, hwi_false,
                   Bool.false_and, Option.map]
        rfl

end Stage2
/-! ## Combining the stages: exp_middle = mark_second_last ∘ exp1

The key insight: `exp_middle_idx n = some v` iff v is the second-largest power of 2 ≤ n.
For word w of length n, exp1 marks positions where i+1 is a power of 2. The second-to-last
such position is exactly where exp_middle marks.
-/

section Composition

  /-! ### Lemmas about exp_middle_idx -/

  private lemma exp_middle_idx_none_iff (n : ℕ) :
      exp_middle_idx n = none ↔ n ≤ 1 := by
    unfold exp_middle_idx
    rw [List.max?_eq_none_iff]
    constructor
    · intro h
      by_contra hne
      push_neg at hne
      -- n ≥ 2, so k=0 should be in the filtered list since 2^0 * 2 = 2 ≤ n
      have h1 : 1 ∈ List.filter (fun x => decide (x * 2 ≤ n)) ((List.range n).map (2 ^ ·)) := by
        rw [List.mem_filter]
        constructor
        · rw [List.mem_map]
          refine ⟨0, ?_, rfl⟩
          simp [List.mem_range]
          omega
        · simp; omega
      simp only [h, List.not_mem_nil] at h1
    · intro hn
      rw [List.filter_eq_nil_iff]
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      simp only [decide_eq_true_eq, not_le]
      have h1 : 2^k * 2 = 2^(k+1) := by ring
      have h2 : 2^(k+1) ≥ 2^1 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ k + 1)
      omega

  private lemma k_lt_two_pow_k (k : ℕ) : k < 2^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc k + 1 ≤ k + 2^k := by omega
        _ < 2^k + 2^k := by omega
        _ = 2^(k+1) := by ring

  private lemma exp_middle_idx_some_iff (n v : ℕ) :
      exp_middle_idx n = some v ↔ (∃ k, v = 2^k ∧ 2^(k+1) ≤ n ∧ ∀ k', 2^(k'+1) ≤ n → k' ≤ k) := by
    unfold exp_middle_idx
    constructor
    · intro h
      have hv_mem := List.max?_mem h
      rw [List.mem_filter, List.mem_map] at hv_mem
      obtain ⟨⟨k, hk, rfl⟩, hfilter⟩ := hv_mem
      simp only [decide_eq_true_eq] at hfilter
      refine ⟨k, rfl, hfilter, ?_⟩
      intro k' hk'
      have hk'_lt_n : k' < n := by
        have h1 : k' < 2^k' := k_lt_two_pow_k k'
        have h2 : 2^k' < 2^(k'+1) := Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
        omega
      have hk'_in : 2^k' ∈ List.filter (fun x => decide (x * 2 ≤ n)) ((List.range n).map (2 ^ ·)) := by
        rw [List.mem_filter, List.mem_map]
        exact ⟨⟨k', by simp [List.mem_range, hk'_lt_n], rfl⟩, by simp; exact hk'⟩
      rw [List.max?_eq_some_iff] at h
      exact Nat.pow_le_pow_iff_right (by omega : 1 < 2) |>.mp (h.2 (2^k') hk'_in)
    · rintro ⟨k, rfl, hk, hmax⟩
      apply List.max?_eq_some_iff.mpr
      constructor
      · rw [List.mem_filter, List.mem_map]
        have hk_lt_n : k < n := by
          have h1 : k < 2^k := k_lt_two_pow_k k
          have h2 : 2^k < 2^(k+1) := Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
          omega
        exact ⟨⟨k, by simp [List.mem_range, hk_lt_n], rfl⟩, by simp; exact hk⟩
      · intro x hx
        rw [List.mem_filter, List.mem_map] at hx
        obtain ⟨⟨k', hk'_range, rfl⟩, hk'_filter⟩ := hx
        simp only [decide_eq_true_eq] at hk'_filter
        exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) (hmax k' hk'_filter)

  private lemma log2_pow2 (k : ℕ) : Nat.log2 (2^k) = k := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pow Nat.one_lt_two k

  private lemma isPowerOfTwo_pow2 (k : ℕ) : isPowerOfTwo (2^k) = true := by
    unfold isPowerOfTwo
    simp only [log2_pow2, gt_iff_lt, Nat.two_pow_pos, decide_true, Bool.true_and]

  /-- Position i is in truePos iff i+1 is a power of 2 and i < n. -/
  private lemma mem_truePos_iff (n i : ℕ) :
      i ∈ (List.range n).filter (fun j => isPowerOfTwo (j + 1)) ↔
      ∃ k, i = 2^k - 1 ∧ 2^k ≤ n := by
    rw [List.mem_filter, List.mem_range, isPowerOfTwo_iff]
    constructor
    · rintro ⟨hi, k, hk⟩
      refine ⟨k, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨k, rfl, hle⟩
      have hk_pos : 1 ≤ 2^k := Nat.one_le_two_pow
      refine ⟨by omega, k, by omega⟩

  /-- The true positions for exp1 are [0, 1, 3, 7, ...] up to 2^(log2 n) - 1. -/
  lemma truePos_eq_map_pow2 (n : ℕ) (hn : n ≥ 1) :
      (List.range n).filter (fun i => isPowerOfTwo (i + 1)) =
      (List.range (Nat.log2 n + 1)).map (fun k => 2^k - 1) := by
    apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
    · -- Show the two lists are permutations (same elements)
      rw [List.perm_ext_iff_of_nodup]
      · intro x
        rw [mem_truePos_iff, List.mem_map]
        constructor
        · rintro ⟨k, rfl, hle⟩
          refine ⟨k, ?_, rfl⟩
          rw [List.mem_range]
          rw [Nat.log2_eq_log_two]
          have : k ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by omega) hle
          omega
        · rintro ⟨k, hk, rfl⟩
          rw [List.mem_range] at hk
          refine ⟨k, rfl, ?_⟩
          rw [Nat.log2_eq_log_two] at hk
          have h := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
          exact le_trans (Nat.pow_le_pow_right (by omega) (by omega : k ≤ Nat.log 2 n)) h
      · exact List.Nodup.filter _ List.nodup_range
      · apply List.Nodup.map
        · intro a b (hab : 2^a - 1 = 2^b - 1)
          have h1 : 1 ≤ 2^a := Nat.one_le_two_pow
          have h2 : 1 ≤ 2^b := Nat.one_le_two_pow
          have h3 : 2^a = 2^b := by
            have := Nat.sub_add_cancel h1
            have := Nat.sub_add_cancel h2
            omega
          exact Nat.pow_right_injective (by omega) h3
        · exact List.nodup_range
    · -- LHS is sorted (filter of sorted range)
      exact List.Sorted.filter _ (List.sorted_le_range n)
    · -- RHS is sorted (map of monotone function over sorted range)
      apply List.Pairwise.map
      · intro a b hab
        have : 2^a ≤ 2^b := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (le_of_lt hab)
        omega
      · exact List.sorted_lt_range _

  lemma truePos_length_eq_log2_succ (n : ℕ) (hn : n ≥ 1) :
      ((List.range n).filter (fun i => isPowerOfTwo (i + 1))).length = Nat.log2 n + 1 := by
    rw [truePos_eq_map_pow2 n hn]; simp

  /-! ### The key lemma: relating second_last_true_idx to exp_middle_idx -/

  /-- Helper: the true positions in exp1 are exactly those where isPowerOfTwo is true. -/
  private lemma exp1_truePositions_eq (n : ℕ) :
      let exp1_word := (List.range n).map (fun i => isPowerOfTwo (i + 1))
      (List.range exp1_word.length).filter (fun i => exp1_word[i]!) =
      (List.range n).filter (fun i => isPowerOfTwo (i + 1)) := by
    simp only [List.length_map, List.length_range]
    refine List.filter_congr ?_
    intro i hi
    rw [List.mem_range] at hi
    simp only [getElem!_def, List.getElem?_map, List.getElem?_range, hi]
    rfl

  /-- True positions in `exp1 w` are exactly positions where `i+1` is a power of 2.
      The second-to-last such position is `exp_middle_idx - 1`. -/
  private lemma second_last_true_of_exp1 (w : Word α) :
      (second_last_true_idx ((Advice.exp1 : Advice α Bool) w)).map (· + 1) = exp_middle_idx w.length := by
    simp only [second_last_true_idx, Advice.exp1]
    set n := w.length with hn
    -- Simplify the inner filter using exp1_truePositions_eq
    have h_filter : (List.range ((List.range n).map (fun i => isPowerOfTwo (i + 1))).length).filter
        (fun i => ((List.range n).map (fun i => isPowerOfTwo (i + 1)))[i]!) =
        (List.range n).filter (fun i => isPowerOfTwo (i + 1)) := exp1_truePositions_eq n
    rw [h_filter]
    set truePos := (List.range n).filter (fun i => isPowerOfTwo (i + 1)) with htp
    -- Case split on whether there are at least 2 true positions
    by_cases h2 : truePos.length ≥ 2
    · -- There are at least 2 true positions
      simp only [h2, ↓reduceIte]
      -- Need to show: Option.map (+1) truePos[truePos.length - 2]? = exp_middle_idx n
      -- First convert optional access to regular access
      have h_idx_valid : truePos.length - 2 < truePos.length := by omega
      rw [List.getElem?_eq_getElem h_idx_valid]
      -- Now: some (truePos[truePos.length - 2] + 1) = exp_middle_idx n

      -- truePos.length ≥ 2 implies n ≥ 2 (since 0 and 1 are true positions when n ≥ 2)
      have hn_ge2 : n ≥ 2 := by
        by_contra h_lt
        push_neg at h_lt
        -- When n < 2, truePos has at most 1 element
        have h_small : truePos.length ≤ 1 := by
          rw [htp]
          rcases n with _ | _ | _
          · decide
          · decide
          · omega
        omega

      -- Key: truePos[len-2] + 1 = 2^(log2 n - 1) = exp_middle_idx n
      -- This follows from the structure: truePos = [2^0-1, 2^1-1, ..., 2^(log2 n)-1]
      -- and exp_middle_idx n = 2^(log2 n - 1)
      simp only [Option.map]
      symm
      rw [exp_middle_idx_some_iff]
      -- Show ∃ k, 2^k = truePos[len-2] + 1 ∧ 2^(k+1) ≤ n ∧ k is maximal
      use Nat.log2 n - 1
      refine ⟨?_, ?_, ?_⟩
      · -- 2^(log2 n - 1) = truePos[len-2] + 1
        -- Use truePos = (range (log2 n + 1)).map (2^· - 1)
        have h_eq := truePos_eq_map_pow2 n (by omega)
        have h_len := truePos_length_eq_log2_succ n (by omega)
        have h_log_ge1 : Nat.log2 n ≥ 1 := by
          have := Nat.log_pos (by omega : 1 < 2) hn_ge2
          rw [← Nat.log2_eq_log_two] at this; omega
        -- truePos[len-2] = ((range (log2 n + 1)).map (2^· - 1))[log2 n - 1]
        --                = 2^(log2 n - 1) - 1
        have : truePos[truePos.length - 2] = 2^(Nat.log2 n - 1) - 1 := by
          have h_idx : truePos.length - 2 = Nat.log2 n - 1 := by rw [h_len]; omega
          have h_mapped := truePos_eq_map_pow2 n (by omega)
          -- Use htp (truePos = filter ...) and h_mapped (filter ... = map ...)
          -- to get truePos = map and hence truePos[k] = map[k]
          have h_eq2 : truePos = (List.range (Nat.log2 n + 1)).map (fun k => 2^k - 1) := by
            rw [htp]; exact h_mapped
          simp_rw [h_eq2, List.getElem_map, List.getElem_range]
          simp
        rw [this]
        have := Nat.one_le_two_pow (n := Nat.log2 n - 1)
        omega
      · -- 2^((log2 n - 1) + 1) ≤ n, i.e., 2^(log2 n) ≤ n
        have h_pow_le : 2^(Nat.log2 n) ≤ n := by
          rw [Nat.log2_eq_log_two]
          exact Nat.pow_log_le_self 2 (by omega : n ≠ 0)
        have h_log_ge1 : Nat.log2 n ≥ 1 := by
          have := Nat.log_pos (by omega : 1 < 2) hn_ge2
          rw [← Nat.log2_eq_log_two] at this
          omega
        simp only [Nat.sub_add_cancel h_log_ge1]
        exact h_pow_le
      · -- k' ≤ log2 n - 1 for all k' with 2^(k'+1) ≤ n
        intro k' hk'
        -- 2^(k'+1) ≤ n implies k'+1 ≤ log2 n implies k' ≤ log2 n - 1
        have h1 : k' + 1 ≤ Nat.log2 n := by
          rw [Nat.log2_eq_log_two]
          exact Nat.le_log_of_pow_le (by omega : 1 < 2) hk'
        omega
    · -- Fewer than 2 true positions
      push_neg at h2
      have h_lt2 : truePos.length < 2 := by omega
      simp only [show ¬(truePos.length ≥ 2) from by omega, ↓reduceIte]
      -- Now goal is: Option.map (· + 1) none = exp_middle_idx n
      -- Which is: none = exp_middle_idx n
      -- Need to show n ≤ 1
      show none = exp_middle_idx n
      symm
      rw [exp_middle_idx_none_iff]
      by_contra h_n_big
      push_neg at h_n_big
      -- n ≥ 2, so both i=0 and i=1 are in range and give true
      have h0 : 0 ∈ truePos := by
        rw [htp, List.mem_filter]
        refine ⟨List.mem_range.mpr (by omega), ?_⟩
        decide
      have h1 : 1 ∈ truePos := by
        rw [htp, List.mem_filter]
        refine ⟨List.mem_range.mpr (by omega), ?_⟩
        decide
      have hdist : (0 : ℕ) ≠ 1 := by omega
      have hnodup : truePos.Nodup := List.Nodup.filter _ List.nodup_range
      have hcard : truePos.length ≥ 2 := by
        have hcard_eq : truePos.toFinset.card = truePos.length := List.toFinset_card_of_nodup hnodup
        have hsub : ({0, 1} : Finset ℕ) ⊆ truePos.toFinset := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [List.mem_toFinset]
          rcases hx with rfl | rfl <;> assumption
        have : ({0, 1} : Finset ℕ).card ≤ truePos.toFinset.card := Finset.card_le_card hsub
        simp only [Finset.card_insert_of_notMem (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)),
                   Finset.card_singleton] at this
        omega
      omega

  /-! ### Main composition theorem -/

  /-- The key decomposition: `exp_middle = exp1.compose mark_second_last`. -/
  theorem exp_middle_eq_compose :
      (Advice.exp_middle α) = (Advice.exp1 : Advice α Bool).compose Advice.mark_second_last := by
    apply advice_eq_iff
    funext w
    -- Unfold all definitions
    simp only [Advice.compose, Advice.exp_middle, Advice.from_len_marker,
               Advice.mark_second_last, Advice.from_marker, Advice.exp1,
               Function.comp_apply]
    -- Note: exp1 preserves length
    have h_len : (List.map (fun i => isPowerOfTwo (i + 1)) (List.range w.length)).length = w.length := by simp
    -- Use the key lemma to relate second_last_true_idx to exp_middle_idx
    have h := second_last_true_of_exp1 w
    simp only [Advice.exp1] at h
    -- Both sides are maps over List.range of same length, producing same values
    apply List.ext_getElem
    · simp [h_len]
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range, h_len] at *
    rw [h]

  /-- Two-stage construction for `exp_middle`. -/
  def ts_exp_middle : TwoStageAdvice α Bool := {
    β := Bool
    C := exp_prefix_CA
    M := select_second_FST
  }

  /-- `Advice.exp_middle` is a two-stage advice. -/
  theorem exp_middle_two_stage_advice : (Advice.exp_middle α).is_two_stage_advice := by
    use ts_exp_middle
    -- ts_exp_middle.advice = select_second_FST.scanr ∘ exp_prefix_CA.trace_rt
    --                      = Advice.exp1.compose Advice.select_2nd
    --                      = Advice.exp1.compose Advice.mark_second_last  (by mark_second_last_eq_select_2nd)
    --                      = Advice.exp_middle                            (by exp_middle_eq_compose)
    calc ts_exp_middle.advice
        = { f := select_second_FST.scanr ∘ exp_prefix_CA.trace_rt } := rfl
      _ = (Advice.exp1 : Advice α Bool).compose Advice.select_2nd := by
          apply advice_eq_iff
          funext w
          simp only [Advice.compose, Function.comp_apply]
          have h_exp1 : exp_prefix_CA.trace_rt w = (Advice.exp1 : Advice α Bool) w := by
            have h := congrFun (congrArg Advice.f (exp_prefix_CA_eq_exp1 (α := α))) w
            simp only [CArtTransducer.advice] at h
            exact h
          rw [h_exp1]
          have h_sel := congrFun (congrArg Advice.f select_second_FST_eq_select_2nd) ((Advice.exp1 : Advice α Bool) w)
          simp only [FiniteStateTransducer.advice] at h_sel
          exact h_sel
      _ = (Advice.exp1 : Advice α Bool).compose Advice.mark_second_last := by
          rw [mark_second_last_eq_select_2nd]
      _ = Advice.exp_middle α := exp_middle_eq_compose.symm

end Composition

end CellularAutomatas
