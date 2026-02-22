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

/-! ## Stage 1: CArtTransducer from exp_word_ca

The trace of exp_word_ca marks positions i where prefix length i+1 is a power of 2.
We map the input alphabet to Unit to ignore actual values.
-/

section Stage1

  def isPowerOfTwo (n : ℕ) : Bool := n > 0 && n = 2 ^ (Nat.log2 n)

  def exp_prefix_CA : CArtTransducer α Bool :=
    (exp_word_ca.map_embed (fun _ => ())).toCellAutomaton

  private lemma exp_word_ca_mem_CA_rt : exp_word_ca ∈ CA_rt Unit := by
    simp only [CA_rt, t_rt, CA, tCellAutomata, Set.mem_setOf_eq, Set.mem_univ, true_and]
    exact ⟨funext (fun _ => rfl), fun _ => rfl⟩

  private lemma isPowerOfTwo_iff (n : ℕ) : isPowerOfTwo n = true ↔ ∃ k, n = 2 ^ k := by
    unfold isPowerOfTwo
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hn_pos, hn_eq⟩
      exact ⟨Nat.log2 n, hn_eq⟩
    · rintro ⟨k, rfl⟩
      refine ⟨Nat.one_le_two_pow, ?_⟩
      rw [Nat.log2_eq_log_two]
      simp

  @[simp] private lemma exp_word_ca_mem_L_iff (w : Word Unit) :
      w ∈ exp_word_ca.L ↔ isPowerOfTwo w.length = true := by
    simp only [tCellAutomaton.L, exp_word_ca_correct, isPowerOfTwo_iff]
    rfl

  lemma exp_prefix_CA_trace_spec {α: Type} (w : Word α) (i : ℕ) (hi : i < w.length) :
      (exp_prefix_CA.trace_rt w)[i]'(by simp; exact hi) = isPowerOfTwo (i + 1) := by
    unfold exp_prefix_CA
    simp only [tCellAutomaton.map_embed_trace_rt]
    rw [trace_rt_getElem_i_iff2 (C := ⟨exp_word_ca, exp_word_ca_mem_CA_rt⟩)]

    simp [show (i + 1) ≤ List.length w by omega]

end Stage1

/-! ## Stage 2: FST that selects the second true (scanning right-to-left)

State = count of trues seen so far, capped at 2
Output true only when transitioning from count=1 to count=2
-/

section Stage2

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
    cases tc <;> native_decide

  private lemma TrueCount_toNat_fromCount_min (n : ℕ) :
      TrueCount_toNat (TrueCount.fromCount (min n 2)) = min n 2 := by
    match n with
    | 0 => native_decide
    | 1 => native_decide
    | n+2 => simp [TrueCount.fromCount, TrueCount_toNat]

  private lemma TrueCount_fromCount_eq_one_iff (n : ℕ) :
      (TrueCount.fromCount (min n 2) == TrueCount.one) = (n == 1) := by
    match n with
    | 0 => native_decide
    | 1 => native_decide
    | n+2 => simp [TrueCount.fromCount]

  private lemma TrueCount_fromCount_roundtrip (tc : TrueCount) :
      TrueCount.fromCount (min (TrueCount_toNat tc) 2) = tc := by
    cases tc <;> native_decide

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

  lemma select_second_FST_spec (w : Word Bool) (i : ℕ) (hi : i < w.length) :
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

end Stage2

/-! ## Combining the stages -/

section TwoStageConstruction

  def ts_exp_middle : TwoStageAdvice α Bool := {
    β := Bool
    C := exp_prefix_CA
    M := select_second_FST
  }

  omit [Alphabet α] in
  lemma exp_middle_eq_from_len_marker (w : Word α) :
      (Advice.exp_middle α) w =
        (List.range w.length).map (fun i => some (i + 1) == exp_middle_idx w.length) := by
    rfl

  /-! ### Key lemmas about exp_middle_idx

  `exp_middle_idx n` = largest 2^k such that 2^(k+1) ≤ n, i.e., 2^k ≤ n/2.
  This equals 2^(log2(n) - 1) when n ≥ 2, and none otherwise.

  Positions with isPowerOfTwo(i+1): 0,1,3,7,15,... (where i+1 = 2^k for k=0,1,2,3,4,...)

  Key fact: some(i+1) = exp_middle_idx n iff
    - isPowerOfTwo(i+1) AND
    - exactly one position j > i in [0,n) has isPowerOfTwo(j+1)
  -/

  private def countPow2After (n i : ℕ) : ℕ :=
    ((List.range n).filter (fun j => i < j && isPowerOfTwo (j + 1))).length

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
      -- 2^k * 2 = 2^(k+1) ≥ 2 > n (since n ≤ 1)
      have h1 : 2^k * 2 = 2^(k+1) := by ring
      have h2 : 2^(k+1) ≥ 2^1 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ k + 1)
      omega

  private lemma k_lt_two_pow_k (k : ℕ) : k < 2^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : k + 1 ≤ k + 2^k := by omega
      calc k + 1 ≤ k + 2^k := h1
        _ < 2^k + 2^k := by omega
        _ = 2^(k+1) := by ring

  private lemma exp_middle_idx_some_iff (n v : ℕ) :
      exp_middle_idx n = some v ↔ (∃ k, v = 2^k ∧ 2^(k+1) ≤ n ∧ ∀ k', 2^(k'+1) ≤ n → k' ≤ k) := by
    -- exp_middle_idx n = max? of [2^k : k < n ∧ 2^(k+1) ≤ n]
    unfold exp_middle_idx
    constructor
    · intro h
      -- h says List.max? (filter ...) = some v
      have hv_mem := List.max?_mem h
      rw [List.mem_filter, List.mem_map] at hv_mem
      obtain ⟨⟨k, hk, rfl⟩, hfilter⟩ := hv_mem
      simp only [decide_eq_true_eq] at hfilter
      refine ⟨k, rfl, hfilter, ?_⟩
      -- Show k is maximal
      intro k' hk'
      have hk'_lt_n : k' < n := by
        have h1 : k' < 2^k' := k_lt_two_pow_k k'
        have h2 : 2^k' < 2^(k'+1) := Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
        have h3 : 2^(k'+1) ≤ n := hk'
        omega
      have hk'_in : 2^k' ∈ List.filter (fun x => decide (x * 2 ≤ n)) ((List.range n).map (2 ^ ·)) := by
        rw [List.mem_filter, List.mem_map]
        constructor
        · refine ⟨k', ?_, rfl⟩
          simp [List.mem_range, hk'_lt_n]
        · simp; exact hk'
      rw [List.max?_eq_some_iff] at h
      have hmax := h.2 (2^k') hk'_in
      -- hmax : 2^k' ≤ v = 2^k
      exact Nat.pow_le_pow_iff_right (by omega : 1 < 2) |>.mp hmax
    · rintro ⟨k, rfl, hk, hmax⟩
      -- Show List.max? ... = some (2^k)
      apply List.max?_eq_some_iff.mpr
      constructor
      · -- 2^k ∈ filter
        rw [List.mem_filter, List.mem_map]
        have hk_lt_n : k < n := by
          have h1 : k < 2^k := k_lt_two_pow_k k
          have h2 : 2^k < 2^(k+1) := Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
          have h3 : 2^(k+1) ≤ n := hk
          omega
        constructor
        · refine ⟨k, ?_, rfl⟩
          simp [List.mem_range, hk_lt_n]
        · simp; exact hk
      · -- 2^k is max
        intro x hx
        rw [List.mem_filter, List.mem_map] at hx
        obtain ⟨⟨k', hk'_range, rfl⟩, hk'_filter⟩ := hx
        simp only [decide_eq_true_eq] at hk'_filter
        have : k' ≤ k := hmax k' hk'_filter
        exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) this

  private lemma log2_pow2 (k : ℕ) : Nat.log2 (2^k) = k := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pow Nat.one_lt_two k

  private lemma isPowerOfTwo_pow2 (k : ℕ) : isPowerOfTwo (2^k) = true := by
    unfold isPowerOfTwo
    simp only [log2_pow2, gt_iff_lt, Nat.two_pow_pos, decide_true, Bool.true_and, beq_self_eq_true]

  private lemma isPowerOfTwo_iff' (m : ℕ) :
      isPowerOfTwo m = true ↔ m > 0 ∧ m = 2^(Nat.log2 m) := by
    unfold isPowerOfTwo
    simp [Nat.log2_eq_log_two]

  private lemma countPow2After_eq (n i : ℕ) (hi : i < n) (hn : 0 < n) :
      countPow2After n i = Nat.log2 n - Nat.log2 (i + 1) := by
    unfold countPow2After
    -- Positions j with i < j < n and isPowerOfTwo(j+1) are exactly 2^m - 1 for m with i+1 < 2^m ≤ n
    -- This means log2(i+1) < m ≤ log2(n), i.e., m ∈ [log2(i+1)+1, log2(n)]
    -- Count = log2(n) - log2(i+1)

    -- First, characterize when isPowerOfTwo (j+1) holds: iff j+1 = 2^(log2(j+1))
    have pow2_char : ∀ j, isPowerOfTwo (j + 1) = true ↔ ∃ m, j + 1 = 2^m :=
      fun j => isPowerOfTwo_iff (j + 1)

    -- For j < n with isPowerOfTwo(j+1), j = 2^m - 1 for some m with 2^m ≤ n
    -- Count of such j with i < j is #{m : log2(i+1) < m ≤ log2(n)}

    -- We compute this by showing the filter has exactly log2(n) - log2(i+1) elements
    -- The elements are exactly [2^(log2(i+1)+1) - 1, 2^(log2(i+1)+2) - 1, ..., 2^log2(n) - 1]

    sorry

  private lemma exp_middle_idx_char (n i : ℕ) (hi : i < n) :
      (some (i + 1) == exp_middle_idx n) = (isPowerOfTwo (i + 1) && countPow2After n i == 1) := by
    -- Case analysis on whether exp_middle_idx n is none or some
    cases hn : exp_middle_idx n with
    | none =>
      -- exp_middle_idx n = none means n ≤ 1
      rw [exp_middle_idx_none_iff] at hn
      -- If n ≤ 1 and i < n, then i = 0 and n = 1
      -- Need to show: (some (i+1) == none) = (isPowerOfTwo (i+1) && countPow2After n i == 1)
      -- LHS = false
      -- RHS: for n ≤ 1, countPow2After n i = 0 (no j > i in range 1)
      have h_n_eq : n = 1 := by omega
      have h_i_eq : i = 0 := by omega
      subst h_n_eq h_i_eq
      native_decide
    | some v =>
      -- exp_middle_idx n = some v
      rw [exp_middle_idx_some_iff] at hn
      obtain ⟨k, hv, hk, hmax⟩ := hn
      subst hv
      -- Goal: (some (i + 1) == some (2^k)) = (isPowerOfTwo (i + 1) && countPow2After n i == 1)
      conv_lhs => rw [show (some (i + 1) == some (2 ^ k)) = (i + 1 == 2 ^ k) from rfl]
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, Bool.and_eq_true]
      constructor
      · intro heq
        rw [heq]
        refine ⟨isPowerOfTwo_pow2 k, ?_⟩
        -- Need: countPow2After n (2^k - 1) = 1
        -- When i = 2^k - 1, the only j in (i, n) with isPowerOfTwo(j+1) is j = 2^(k+1) - 1
        -- This is because:
        -- 1. j = 2^(k+1) - 1 is in range: 2^(k+1) - 1 > 2^k - 1 and 2^(k+1) - 1 < n (from hk)
        -- 2. No other j works: any j with isPowerOfTwo(j+1) has j = 2^m - 1 for some m
        --    If m > k+1, then 2^(m+1) ≤ 2^m ≤ n would contradict maximality of k
        -- TODO: Complete this combinatorial argument
        sorry
      · rintro ⟨hpow, hcount⟩
        -- isPowerOfTwo(i+1) means i+1 = 2^m for some m
        -- countPow2After n i = 1 constrains m to equal k
        rw [isPowerOfTwo_iff] at hpow
        obtain ⟨m, hm⟩ := hpow
        -- Need to show m = k
        -- If m < k: count ≥ 2 (both 2^(m+1)-1 and 2^(k+1)-1 in range)
        -- If m > k: count = 0 (no power of 2 between 2^m and 2^(m+1))
        -- TODO: Complete this case analysis
        sorry

  private lemma trace_drop_count_eq_countPow2After (w : Word α) (i : ℕ) (hi : i < w.length) :
      ((exp_prefix_CA.trace_rt w).drop (i + 1)).count true = countPow2After w.length i := by
    unfold countPow2After
    have trace_len : (exp_prefix_CA.trace_rt w).length = w.length := by simp
    have trace_eq : ∀ j (hj : j < w.length),
        (exp_prefix_CA.trace_rt w)[j]'(by rw [trace_len]; exact hj) = isPowerOfTwo (j + 1) := by
      intro j hj
      exact exp_prefix_CA_trace_spec w j hj
    -- Both sides count positions j ∈ (i, w.length) with isPowerOfTwo(j+1) = true
    -- LHS: drop(i+1) contains [trace[i+1], ..., trace[n-1]] where trace[j] = isPowerOfTwo(j+1)
    -- RHS: filter across range n for j > i with isPowerOfTwo(j+1)
    -- These are equal by a straightforward but tedious list manipulation argument
    -- TODO: Complete this proof via induction on (w.length - (i+1))
    sorry

  theorem exp_middle_two_stage_advice : (Advice.exp_middle α).is_two_stage_advice := by
    use ts_exp_middle
    apply advice_eq_iff
    funext w
    simp only [ts_exp_middle, TwoStageAdvice.advice, Advice.exp_middle, Advice.from_len_marker,
               Function.comp_apply]
    apply List.ext_getElem
    · simp [FiniteStateTransducer.scanr]
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range] at hi2 ⊢
    have hi : i < w.length := by
      simp [FiniteStateTransducer.scanr] at hi1
      exact hi1
    rw [select_second_FST_spec (exp_prefix_CA.trace_rt w) i (by simp; exact hi)]
    rw [exp_prefix_CA_trace_spec w i hi]
    rw [trace_drop_count_eq_countPow2After w i hi]
    rw [exp_middle_idx_char w.length i hi]

end TwoStageConstruction

end CellularAutomatas
