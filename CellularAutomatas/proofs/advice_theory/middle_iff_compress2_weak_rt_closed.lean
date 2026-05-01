/-
  # Middle and Compress2 Weak-RT-Closedness Equivalence (Unary Alphabet)

  This file proves:
    `Nonempty (Advice.middle Unit).weak_rt_closed ↔ Nonempty (Advice.compress2 Unit).weak_rt_closed`

  ## Strategy

  Both directions use the composition lemma:
    `weak_rt_closed_compose_rt_closed : f₁.weak_rt_closed → f₂.rt_closed → (f₁.compose f₂).weak_rt_closed`

  Since two-stage advices are rt_closed, it suffices to find two-stage advices g, h such that:
    (1) middle = compress2.compose g   (then: compress2 weak + g rt_closed → middle weak)
    (2) compress2 = middle.compose h   (then: middle weak + h rt_closed → compress2 weak)

  ## Advice Definitions (Unit alphabet)

  **middle (Unit)**: For input length n, marks position n/2 - 1 with True.

  **compress2 (Unit)**: For input length n, position i outputs:
    - (some (), some ()): if 2i < n and 2i+1 < n
    - (some (), none):    if 2i < n and 2i+1 ≥ n (i.e., n = 2i+1)
    - (none, none):       if 2i ≥ n

  ## Auxiliary Advices

  **g : Advice (Option Unit × Option Unit) Bool**
    Given compress2 output, find the middle position.
    - For even n = 2k: last (some,some) at position k-1, mark it.
    - For odd n = 2k+1: unique (some,none) at position k, mark position k-1.

  **h : Advice Bool (Option Unit × Option Unit)**
    Given middle output (True at position n/2-1), produce compress2 output.
    - Needs CArt to broadcast marker position, then local FST computation.
-/

import CellularAutomatas.proofs.advice_theory.rt_closed.of_compose
import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage
import CellularAutomatas.proofs.constructions.trace_id
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.advice_theory.rt_closed.with_left_neighbor
import CellularAutomatas.proofs.advice_theory.rt_closed.pair_with_parity

namespace CellularAutomatas

open CellAutomaton
open FiniteStateTransducer

/-!
## Section 1: Function Definitions

First we define the pure functions, independently of automaton structure.
Then we separately prove they are two-stage and satisfy the composition equations.
-/

section FunctionDefinitions

  /-!
  ### g: compress2 output → middle output (Bool marking)

  Given a word `w : Word (Option Unit × Option Unit)` from compress2:
  - Scan right-to-left to find the boundary between "real" and "border" symbols.
  - Mark one position before the boundary (for even-length originals) or
    two positions before a (some, none) symbol (for odd-length originals).

  More precisely:
  - If we see (none, none) followed by (some, some), mark the (some, some) position.
  - If we see (some, none), mark the position before it.
  -/

  /-- The function underlying g: given compress2 output, compute middle output. -/
  def compress2_to_middle_fn (w: Word (Option Unit × Option Unit)): Word Bool :=
    (List.range w.length).map fun i =>
      -- Mark position i iff:
      -- (even case) w[i] = (some, some) and w[i+1] = (none, none)
      -- (odd case) w[i+1] = (some, none) (mark position i, which is one before the (some, none))
      let curr := w[i]?
      let next := w[i+1]?
      match curr, next with
      | some (some _, some _), some (none, none) => true   -- even case: mark last (some,some)
      | some (some _, some _), some (some _, none) => true -- odd case: mark position before (some,none)
      | some (some _, some _), none => true                -- edge case: last position is (some,some)
      | _, _ => false

  /-!
  ### h: middle output → compress2 output

  Given a word `w : Word (Bool × Bool)` where:
  - First component: middle marker (True at exactly position n/2 - 1)
  - Second component: is_even_length (uniform True/False across all positions)

  The compress2 pattern is:
  - Positions left of marker (i < m): output (some, some)
  - At marker (i = m): output (some, some)
  - One right of marker (i = m+1): output (some, none) if odd, (none, none) if even
  - Further right (i > m+1): output (none, none)

  This is FST-computable (right-to-left scan):
  - Track "just saw marker" to handle the m+1 position
  - Track "past marker" to output (some, some) for positions ≤ m
  -/

  /-- The function underlying h: given (middle_marker, is_even) pairs, compute compress2 output.

      Scanning right-to-left, we track whether we've seen the marker.
      - Before seeing marker: output (none, none)
      - Just saw marker at previous position (i.e., current is m+1):
        output (some, none) if odd, (none, none) if even
      - At marker or past it (i ≤ m): output (some, some)
  -/
  def middle_to_compress2_fn (w: Word (Bool × Bool)): Word (Option Unit × Option Unit) :=
    let n := w.length
    (List.range n).map fun i =>
      -- Check if marker is at any position j > i (to our right, already processed in R-to-L scan)
      let marker_seen_right := (List.range (n - i - 1)).any fun k => (w[i + 1 + k]!).1
      let (marker_here, is_even) := w[i]!
      if marker_seen_right then
        -- Marker is to our right → we're left of marker → (some, some)
        (some (), some ())
      else if marker_here then
        -- At the marker → (some, some)
        (some (), some ())
      else
        -- No marker at or to our right → we're right of marker
        -- Check if marker is exactly one position to our left (i.e., at position i-1)
        let marker_one_left := if i > 0 then (w[i - 1]!).1 else false
        if marker_one_left then
          -- We're at position m+1 (one right of marker)
          if is_even then (none, none) else (some (), none)
        else if i = 0 ∧ is_even = false then
          -- Special case: n = 1 (no marker exists, we're at position 0, length is odd)
          -- Need to output (some, none) since compress2[0] = (w[0]?, w[1]?) = (some(), none)
          (some (), none)
        else
          -- Further right of marker (or n = 0/even with no marker, etc.)
          (none, none)

end FunctionDefinitions


/-!
## Section 2: The Advices from Functions
-/

section AdviceDefinitions

  def Advice.compress2_to_middle: Advice (Option Unit × Option Unit) Bool :=
    { f := compress2_to_middle_fn
      len := by intro w; simp [compress2_to_middle_fn] }

  -- Advice.is_even_length (defined in middle_iff_compress2_defs)
  -- Advice.pair_with_parity (defined in middle_iff_compress2_defs)
  -- Advice.with_left_neighbor (defined in middle_iff_compress2_defs)

  /-- Given (middle_marker, is_even) pairs, produce compress2 output. -/
  def Advice.middle_to_compress2: Advice (Bool × Bool) (Option Unit × Option Unit) :=
    { f := middle_to_compress2_fn
      len := by intro w; simp [middle_to_compress2_fn] }

end AdviceDefinitions


/-!
## Section 3: Composition Equations

Prove:
  (1) middle Unit = (compress2 Unit).compose compress2_to_middle
  (2) compress2 Unit = (pair_with_parity.compose middle Unit).compose middle_to_compress2
-/

section CompositionEquations

  /-- Key equation 1: middle = compress2.compose compress2_to_middle

  For a Unit word of length n:
  - compress2 outputs [(some,some), ..., (some,some)/(some,none), (none,none), ...]
  - compress2_to_middle marks the position before the first (none,none) or (some,none)
  - This is exactly position n/2 - 1, matching middle's marker.

  Proof idea:
  - For Unit words, compress2(w)[i] = (some (), some ()) iff 2i+1 < n
  - compress2_to_middle marks position i iff compress2(w)[i] = (some,some)
    and compress2(w)[i+1] ∉ {(some,some)}
  - This happens exactly when i = n/2 - 1 = middle_idx(n) - 1
  -/
  theorem middle_eq_compress2_compose_g:
      Advice.middle Unit = (Advice.compress2 Unit).compose Advice.compress2_to_middle := by
    apply advice_eq_iff
    funext w
    simp only [Advice.compose, Function.comp]

    -- Show lengths match and do element-wise equality
    have h_c2_len : ((Advice.compress2 Unit) w).length = w.length := by simp
    have h_c2m_len : (Advice.compress2_to_middle ((Advice.compress2 Unit) w)).length = w.length := by
      simp only [Advice.compress2_to_middle, compress2_to_middle_fn, h_c2_len, List.length_map, List.length_range]

    apply List.ext_getElem
    · simp only [Advice.middle, Advice.from_len_marker, Advice.from_marker, List.length_map, List.length_range]
      exact h_c2m_len.symm
    intro i hi _

    -- Get bounds first
    have hi_len : i < w.length := by simp only [Advice.middle, Advice.from_len_marker, Advice.from_marker] at hi; simp at hi; exact hi

    -- Simplify LHS (middle)
    simp only [Advice.middle, Advice.from_len_marker, Advice.from_marker, middle_idx,
               Function.comp_apply, List.getElem_map, List.getElem_range]

    -- Simplify RHS: unfold compress2_to_middle, compress2
    -- Important: also unfold Advice.compress2 so rw later can find the pattern
    simp only [Advice.compress2_to_middle, compress2_to_middle_fn,
               Advice.compress2, List.getElem_map, List.getElem_range]

    -- Now the goal has pattern  ((List.map (fun j => (w[2*j]?, w[2*j+1]?)) (List.range w.length))[i]?)
    -- Simplify the compress2 list access at position i (in bounds)
    have h_c2i : ((List.map (fun j => (w[2*j]?, w[2*j+1]?)) (List.range w.length))[i]?) =
        some (w[2*i]?, w[2*i+1]?) := by
      rw [List.getElem?_eq_getElem (by simp; exact hi_len)]
      simp [List.getElem_map, List.getElem_range]

    -- For Unit words, getElem? is determined purely by index bounds
    have h2i : w[2*i]? = if 2*i < w.length then some () else none := by
      split_ifs with h <;> simp_all
    have h2i1 : w[2*i+1]? = if 2*i+1 < w.length then some () else none := by
      split_ifs with h <;> simp_all

    -- Handle the getElem? for position i+1
    by_cases hi1 : i + 1 < w.length
    · -- i+1 is in bounds
      have h_c2i1 : ((List.map (fun j => (w[2*j]?, w[2*j+1]?)) (List.range w.length))[i+1]?) =
          some (w[2*(i+1)]?, w[2*(i+1)+1]?) := by
        rw [List.getElem?_eq_getElem (by simp; exact hi1)]
        simp [List.getElem_map, List.getElem_range]
      have h2i1' : w[2*(i+1)]? = if 2*(i+1) < w.length then some () else none := by
        split_ifs with h <;> simp_all
      have h2i1'' : w[2*(i+1)+1]? = if 2*(i+1)+1 < w.length then some () else none := by
        split_ifs with h <;> simp_all
      rw [h_c2i, h_c2i1, h2i, h2i1, h2i1', h2i1'']
      -- Now do case analysis
      split_ifs <;> simp_all <;> omega
    · -- i+1 is out of bounds
      have h_c2i1 : ((List.map (fun j => (w[2*j]?, w[2*j+1]?)) (List.range w.length))[i+1]?) = none := by
        apply List.getElem?_eq_none
        simp; omega
      rw [h_c2i, h_c2i1, h2i, h2i1]
      -- Now do case analysis
      split_ifs <;> simp_all <;> omega


  /-! ### Helper lemmas for compress2 ↔ middle composition equation -/

  /-- For a Unit word, the paired word has marker at position k iff k+1 = n/2. -/
  lemma paired_marker_at (w : Word Unit) (k : ℕ) (hk : k < w.length) :
      (((Advice.middle Unit).f w ⨂ List.replicate w.length (w.length % 2 == 0))[k]!).1 =
        decide (k + 1 = w.length / 2) := by
    have h_middle_len : ((Advice.middle Unit).f w).length = w.length := by simp
    have h_paired_len : (((Advice.middle Unit).f w) ⨂
                       List.replicate w.length (w.length % 2 == 0)).length = w.length := by
      simp [List.length_zip, h_middle_len]
    rw [getElem!_def, List.getElem?_eq_getElem (by rw [h_paired_len]; exact hk)]
    rw [List.getElem_zip]
    simp only [Advice.middle, Advice.from_len_marker, Advice.from_marker, middle_idx,
               Function.comp_apply, List.getElem_map, List.getElem_range]
    by_cases h : k + 1 = w.length / 2 <;> simp [h]

  /-- For a Unit word, the parity component of the paired word is uniform. -/
  lemma paired_parity_at (w : Word Unit) (k : ℕ) (hk : k < w.length) :
      (((Advice.middle Unit).f w ⨂ List.replicate w.length (w.length % 2 == 0))[k]!).2 =
        decide (w.length % 2 = 0) := by
    have h_middle_len : ((Advice.middle Unit).f w).length = w.length := by simp
    have h_paired_len : (((Advice.middle Unit).f w) ⨂
                       List.replicate w.length (w.length % 2 == 0)).length = w.length := by
      simp [List.length_zip, h_middle_len]
    rw [getElem!_def, List.getElem?_eq_getElem (by rw [h_paired_len]; exact hk)]
    rw [List.getElem_zip]
    simp only [List.getElem_replicate]
    by_cases h : w.length % 2 = 0 <;> simp [h]

  /-- For a Unit word, marker_seen_right at position i is true iff i+1 < n/2. -/
  lemma marker_seen_right_iff (w : Word Unit) (i : ℕ) (hi : i < w.length) :
      ((List.range (w.length - i - 1)).any fun k =>
         (((Advice.middle Unit).f w ⨂ List.replicate w.length (w.length % 2 == 0))[i + 1 + k]!).1)
        = decide (i + 1 < w.length / 2) := by
    by_cases h : i + 1 < w.length / 2
    · simp only [h, decide_true]
      apply List.any_eq_true.mpr
      have h_div_le : w.length / 2 ≤ w.length := Nat.div_le_self w.length 2
      let k_marker := w.length / 2 - i - 2
      have h_k_lt : k_marker < w.length - i - 1 := by simp only [k_marker]; omega
      have h_pos_lt : i + 1 + k_marker < w.length := by simp only [k_marker]; omega
      use k_marker
      refine ⟨List.mem_range.mpr h_k_lt, ?_⟩
      rw [paired_marker_at w (i + 1 + k_marker) h_pos_lt]
      simp only [k_marker]
      have hsum : i + 1 + (w.length / 2 - i - 2) + 1 = w.length / 2 := by omega
      rw [hsum]; simp
    · simp only [h, decide_false]
      apply (Bool.eq_false_iff).mpr
      intro h_any
      rw [List.any_eq_true] at h_any
      obtain ⟨k, hk_mem, hk_marker⟩ := h_any
      rw [List.mem_range] at hk_mem
      have h_pos_lt : i + 1 + k < w.length := by omega
      rw [paired_marker_at w (i + 1 + k) h_pos_lt] at hk_marker
      simp only [decide_eq_true_iff] at hk_marker
      omega

  /-- Key equation 2: compress2 = (middle.compose pair_with_parity).compose middle_to_compress2

  For a Unit word of length n, position i, let m = n/2.
  - middle[i] = (i + 1 == m)
  - paired[i] = (middle[i], n % 2 == 0)
  - middle_to_compress2_fn computes (some,some), (some,none), or (none,none)
    based on marker position relative to i.
  - compress2[i] = (some_iff(2i<n), some_iff(2i+1<n))

  Both reduce to the same case analysis on i vs n/2.
  -/
  theorem compress2_eq_middle_compose_h:
      Advice.compress2 Unit = ((Advice.middle Unit).compose Advice.pair_with_parity).compose Advice.middle_to_compress2 := by
    apply advice_eq_iff
    funext w
    simp only [Advice.compose, Function.comp]
    simp only [Advice.middle_to_compress2, middle_to_compress2_fn]
    simp only [Advice.pair_with_parity, Advice.is_even_length]

    have h_middle_len : ((Advice.middle Unit).f w).length = w.length := by simp
    -- Normalize all `((Advice.middle Unit).f w).length` to `w.length` everywhere
    simp only [h_middle_len]

    have h_paired_len : (((Advice.middle Unit).f w) ⨂
                       List.replicate w.length (w.length % 2 == 0)).length = w.length := by
      simp [List.length_zip, h_middle_len]

    apply List.ext_getElem
    · simp only [Advice.compress2, List.length_map, List.length_range]
      rw [h_paired_len]
    intro i hi _

    have hi_w : i < w.length := by
      simp only [Advice.compress2, List.length_map, List.length_range] at hi
      exact hi

    -- Simplify LHS (compress2)
    simp only [Advice.compress2, List.getElem_map, List.getElem_range]

    -- For Unit words, w[k]? = some () iff k < w.length
    have unit_getElem : ∀ k, w[k]? = if k < w.length then some () else none := by
      intro k
      by_cases h : k < w.length
      · rw [List.getElem?_eq_getElem h]; simp [h]
      · rw [List.getElem?_eq_none (by omega)]; simp [h]
    rw [unit_getElem (2*i), unit_getElem (2*i+1)]

    -- Simplify the map index access on RHS
    rw [show (((Advice.middle Unit).f w) ⨂
             List.replicate w.length (w.length % 2 == 0)).length = w.length from h_paired_len]

    -- The destructure `let (a, b) := w[i]!` produces `.get!Internal i` which is defeq to `[i]!`
    have eq1 : (((Advice.middle Unit).f w ⨂ List.replicate w.length (w.length % 2 == 0)).get!Internal i).1
             = (((Advice.middle Unit).f w ⨂ List.replicate w.length (w.length % 2 == 0))[i]!).1 := rfl
    have eq2 : (((Advice.middle Unit).f w ⨂ List.replicate w.length (w.length % 2 == 0)).get!Internal i).2
             = (((Advice.middle Unit).f w ⨂ List.replicate w.length (w.length % 2 == 0))[i]!).2 := rfl
    rw [eq1, eq2]
    rw [marker_seen_right_iff w i hi_w]
    rw [paired_marker_at w i hi_w]
    rw [paired_parity_at w i hi_w]

    -- Rewrite marker_one_left to a clean form
    have h_marker_one_left :
        (if i > 0 then (((Advice.middle Unit).f w) ⨂
                List.replicate w.length (w.length % 2 == 0))[i - 1]!.1
              else false) = (decide (i > 0) && decide (i = w.length / 2)) := by
      by_cases hi_pos : i > 0
      · have hi_minus_1 : i - 1 < w.length := Nat.lt_of_le_of_lt (Nat.sub_le i 1) hi_w
        have h_im1 : i - 1 + 1 = i := Nat.sub_add_cancel hi_pos
        simp only [hi_pos, ↓reduceIte, decide_true, Bool.true_and]
        rw [paired_marker_at w (i - 1) hi_minus_1, h_im1]
      · simp [hi_pos]
    rw [h_marker_one_left]

    -- Now do case analysis using omega
    set n := w.length with hn
    have h_div : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
    have h_mod : n % 2 < 2 := Nat.mod_lt n (by omega)
    have h_div_mod : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2

    by_cases h1 : i + 1 < n / 2
    · -- marker_seen_right = true → (some, some)
      have h_2i1 : 2 * i + 1 < n := by omega
      have h_2i : 2 * i < n := by omega
      simp [h1, h_2i, h_2i1]
    · by_cases h2 : i + 1 = n / 2
      · -- marker_here = true → (some, some)
        have h_2i1 : 2 * i + 1 < n := by omega
        have h_2i : 2 * i < n := by omega
        simp [h1, h2, h_2i, h_2i1]
      · by_cases h3 : i = n / 2
        · -- marker_one_left = true → use parity
          by_cases hi_pos : i > 0
          · by_cases h_even : n % 2 = 0
            · -- Even: 2i = n → (none, none)
              have h_2i : ¬ (2 * i < n) := by omega
              have h_2i1 : ¬ (2 * i + 1 < n) := by omega
              simp [h1, h2, h3, hi_pos, h_even, h_2i, h_2i1]
              omega
            · -- Odd: 2i = n - 1 → (some, none)
              have h_2i_lt : 2 * i < n := by omega
              have h_2i1 : ¬ (2 * i + 1 < n) := by omega
              have h_n_ge_2 : 2 ≤ n := by omega
              simp [h1, h2, h3, hi_pos, h_even, h_2i_lt, h_2i1, h_n_ge_2]
              omega
          · -- i = 0 = n/2: special case
            have hi_eq : i = 0 := by omega
            -- i = 0 and i = n/2 means n/2 = 0, so n ≤ 1
            -- We need n > 0 (from hi_w), so n = 1, hence odd
            have hn1 : n = 1 := by omega
            have h_2i_lt : 2 * i < n := by omega
            have h_2i1 : ¬ (2 * i + 1 < n) := by omega
            simp [h1, h2, h3, hi_pos, h_2i_lt, h_2i1, hn1]
        · -- i > n/2 → (none, none)
          have h_i_large : i > n / 2 := by omega
          have h_2i : ¬ (2 * i < n) := by omega
          have h_2i1 : ¬ (2 * i + 1 < n) := by omega
          simp [h1, h2, h3, h_2i, h_2i1]
          omega

end CompositionEquations


/-!
## Section 4: Two-Stage Proofs

Show that compress2_to_middle and middle_to_compress2 are two-stage advices.
-/

section TwoStageProofs

  /-!
  ### compress2_to_middle is two-stage

  Strategy: Use identity CArt + FST that tracks (current, right_neighbor).
  The FST processes right-to-left, so when outputting at position i,
  it has already seen position i+1 and can make the decision.
  -/

  abbrev C2M_Input := Option Unit × Option Unit

  /-- FST that pairs each symbol with its right neighbor.
      State = (current_symbol, right_neighbor).
      Processing right-to-left: when we see w[i], state already has w[i+1]. -/
  def compress2_to_middle_fst : FiniteStateTransducer C2M_Input Bool where
    Q := Option C2M_Input × Option C2M_Input
    δ := fun (prev_curr, _) a => (some a, prev_curr)
    q0 := (none, none)
    f := fun (curr, right) =>
      match curr, right with
      | some (some _, some _), some (none, none) => true
      | some (some _, some _), some (some _, none) => true
      | some (some _, some _), none => true
      | _, _ => false

  instance : Alphabet (Option C2M_Input × Option C2M_Input) := inferInstance

  def compress2_to_middle_two_stage: TwoStageAdvice C2M_Input Bool where
    β := C2M_Input
    C := ca_trace_id_word C2M_Input
    M := compress2_to_middle_fst

  /-- At position i, the FST state after processing the suffix w[i:] is (w[i]?, w[i+1]?). -/
  lemma compress2_to_middle_fst_scanr_state (w : Word C2M_Input) (i : ℕ) (hi : i ≤ w.length) :
      compress2_to_middle_fst.scanr_reduce (w.drop i) = (w[i]?, w[i+1]?) := by
    induction i generalizing w with
    | zero =>
      simp only [List.drop_zero, Nat.zero_add]
      induction w with
      | nil => rfl
      | cons a as ih =>
        simp only [FiniteStateTransducer.scanr_reduce, FiniteStateTransducer.scanr_reduce_q,
                   List.getElem?_cons_zero, List.getElem?_cons_succ]
        -- Goal: δ (scanr_reduce_q q0 as) a = (some a, as[0]?)
        -- scanr_reduce as = scanr_reduce_q q0 as = (as[0]?, as[1]?)
        have h_ih : compress2_to_middle_fst.scanr_reduce as = (as[0]?, as[1]?) := ih (by omega)
        simp only [FiniteStateTransducer.scanr_reduce] at h_ih
        rw [h_ih]
        rfl
    | succ k ih =>
      cases w with
      | nil => simp at hi
      | cons a as =>
        simp only [List.drop_succ_cons, List.getElem?_cons_succ]
        apply ih
        simp at hi; omega

  theorem compress2_to_middle_two_stage_spec:
      compress2_to_middle_two_stage.advice = Advice.compress2_to_middle := by
    apply advice_eq_iff
    funext w
    simp only [TwoStageAdvice.advice, compress2_to_middle_two_stage,
               ca_trace_id_scan_temporal, Function.comp_apply, id_eq]
    simp only [Advice.compress2_to_middle, compress2_to_middle_fn]

    -- Show the FST scanr produces the same output as compress2_to_middle_fn
    apply List.ext_getElem (by simp)
    intro i hi _
    have hi_w : i < w.length := by simp at hi; exact hi

    -- Simplify LHS to show it equals RHS
    simp only [FiniteStateTransducer.scanr, List.getElem_map, List.getElem_range]

    -- Use the FST scanr element lemma
    have h_scanr := FiniteStateTransducer.scanr_get'_eq1 (M := compress2_to_middle_fst) w ⟨i, hi_w⟩
    -- h_scanr: (M.scanr w)[⟨i, hi_w⟩]'... = M.f (M.δ ...).  This has Fin indexing.

    -- Convert: the goal uses scanr_q form with Nat indexing
    simp only [FiniteStateTransducer.scanr, FiniteStateTransducer.scanr_q] at h_scanr

    -- The state after processing positions i+1,...,n-1 is (w[i+1]?, w[i+2]?)
    have h_state : compress2_to_middle_fst.scanr_reduce (w.drop (i + 1)) = (w[i+1]?, w[i+2]?) :=
      compress2_to_middle_fst_scanr_state w (i+1) (by omega)

    -- The goal already has scanr_q form (from the earlier simp)
    have hi_scanr_q : i < (compress2_to_middle_fst.scanr_q compress2_to_middle_fst.q0 w).length := by
      simp [FiniteStateTransducer.scanr_q_len, hi_w]

    -- Use the FST element lemma - convert h_scanr (which uses Fin indexing) to Nat indexing
    have h_scanr_nat : (compress2_to_middle_fst.scanr_q compress2_to_middle_fst.q0 w)[i]'hi_scanr_q =
        compress2_to_middle_fst.f (compress2_to_middle_fst.δ (compress2_to_middle_fst.scanr_reduce (w.drop (i + 1))) w[i]) := by
      have h := h_scanr
      simp only [FiniteStateTransducer.scanr_q] at h ⊢
      convert h using 1
    rw [h_scanr_nat, h_state]
    simp only [compress2_to_middle_fst, List.getElem?_eq_getElem, hi_w]
    rfl

  def compress2_to_middle_is_two_stage:
      Advice.compress2_to_middle.is_two_stage_advice :=
    ⟨compress2_to_middle_two_stage, compress2_to_middle_two_stage_spec⟩


  /-!
  ### middle_to_compress2 is RT-closed

  Strategy: Decompose as `with_left_neighbor.compose m2c_from_enriched`.
  - `with_left_neighbor` is RT-closed (axiom).
  - `m2c_from_enriched` is two-stage (ID CA + FST), hence RT-closed.
  - Composition of RT-closed is RT-closed.

  The enriched input `((marker, parity), left_neighbor?)` gives the FST access to
  `marker_one_left` directly, solving the right-to-left scan obstacle.
  -/

  /-- Input to the enriched advice: ((marker, parity), left_neighbor). -/
  abbrev M2C_Enriched := (Bool × Bool) × Option (Bool × Bool)

  /-- Given enriched input, compute compress2 output.
      Each position sees its own (marker, parity) and its left neighbor. -/
  def m2c_from_enriched_fn (w : Word M2C_Enriched) : Word (Option Unit × Option Unit) :=
    let n := w.length
    (List.range n).map fun i =>
      let ((marker_here, is_even), left) := w[i]!
      -- Check if marker is at any position j > i (to our right)
      let marker_seen_right := (List.range (n - i - 1)).any fun k => (w[i + 1 + k]!).1.1
      if marker_seen_right then (some (), some ())
      else if marker_here then (some (), some ())
      else
        -- Right of marker. Check left neighbor for marker.
        let marker_one_left := match left with | some (m, _) => m | none => false
        if marker_one_left then
          if is_even then (none, none) else (some (), none)
        else if left.isNone ∧ is_even = false then
          -- i = 0, odd length → (some, none)
          (some (), none)
        else (none, none)

  def Advice.m2c_from_enriched : Advice M2C_Enriched (Option Unit × Option Unit) :=
    { f := m2c_from_enriched_fn
      len := by intro w; simp [m2c_from_enriched_fn] }

  /-- Helper: getElem! of the enriched list at a valid index. -/
  lemma with_left_neighbor_getElem (w : Word (Bool × Bool)) (j : ℕ) (hj : j < w.length) :
      ((Advice.with_left_neighbor (Bool × Bool)).f w)[j]! =
        (w[j]!, if j > 0 then some w[j - 1]! else none) := by
    simp only [Advice.with_left_neighbor]
    rw [getElem!_def]
    rw [List.getElem?_eq_getElem (by simp [hj])]
    simp [List.getElem_map, List.getElem_range, hj]

  /-- For any index j, the marker bit (.1.1) on the enriched list equals
      the marker bit (.1) on the original. Holds even out-of-range (both default to false). -/
  lemma with_left_neighbor_marker_eq (w : Word (Bool × Bool)) (j : ℕ) :
      (((Advice.with_left_neighbor (Bool × Bool)).f w)[j]!).1.1 = (w[j]!).1 := by
    by_cases hj : j < w.length
    · rw [with_left_neighbor_getElem w j hj]
    · push_neg at hj
      have h_enriched_len : ((Advice.with_left_neighbor (Bool × Bool)).f w).length = w.length := by
        simp [Advice.with_left_neighbor]
      simp only [getElem!_def]
      rw [List.getElem?_eq_none (by rw [h_enriched_len]; exact hj),
          List.getElem?_eq_none hj]
      rfl

  /-- Composition equation: middle_to_compress2 = with_left_neighbor.compose m2c_from_enriched -/
  theorem middle_to_compress2_eq_compose :
      Advice.middle_to_compress2 = (Advice.with_left_neighbor (Bool × Bool)).compose Advice.m2c_from_enriched := by
    apply advice_eq_iff
    funext w
    simp only [Advice.compose, Function.comp, Advice.middle_to_compress2, Advice.m2c_from_enriched,
               middle_to_compress2_fn, m2c_from_enriched_fn]
    have h_enriched_len : ((Advice.with_left_neighbor (Bool × Bool)).f w).length = w.length := by
      simp [Advice.with_left_neighbor]
    apply List.ext_getElem
    · simp [h_enriched_len]
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    have hi_w : i < w.length := by simp at hi; exact hi
    -- Normalize get!Internal to [_]! on both sides
    have norm_lhs : List.get!Internal w i = w[i]! := rfl
    have norm_rhs : List.get!Internal ((Advice.with_left_neighbor (Bool × Bool)).f w) i =
        ((Advice.with_left_neighbor (Bool × Bool)).f w)[i]! := rfl
    rw [norm_lhs, norm_rhs]
    -- Substitute the enriched element via helper
    rw [with_left_neighbor_getElem w i hi_w, h_enriched_len]
    -- Show the marker_seen_right `any` bodies match
    have h_any_eq :
        ((List.range (w.length - i - 1)).any fun k =>
          (((Advice.with_left_neighbor (Bool × Bool)).f w)[i + 1 + k]!).1.1) =
        ((List.range (w.length - i - 1)).any fun k => (w[i + 1 + k]!).1) := by
      congr 1
      funext k
      exact with_left_neighbor_marker_eq w (i + 1 + k)
    rw [h_any_eq]
    -- Now case-split on i > 0 to align the left-neighbor and (i = 0) checks
    by_cases hi_pos : i > 0
    · simp only [hi_pos, ↓reduceIte, Option.isNone_some]
      rcases h : w[i]! with ⟨mh, ev⟩
      have hi_ne : i ≠ 0 := Nat.pos_iff_ne_zero.mp hi_pos
      simp [hi_ne]
    · push_neg at hi_pos
      have hi_eq : i = 0 := by omega
      subst hi_eq
      simp only [Nat.lt_irrefl, ↓reduceIte, Option.isNone_none]

  /-- State for the m2c FST. Encodes everything needed for the output decision. -/
  abbrev M2C_FST_State := Bool × Bool × Bool × Bool × Bool
  -- (marker_seen_strictly_right, marker_here, is_even, marker_one_left, is_pos_zero)

  instance : Alphabet M2C_FST_State := inferInstance

  /-- FST that computes m2c_from_enriched using right-to-left scan.
      State tracks: (seen_right, marker_here, is_even, marker_left, is_pos_zero). -/
  def m2c_enriched_fst' : FiniteStateTransducer M2C_Enriched (Option Unit × Option Unit) where
    Q := M2C_FST_State
    δ := fun (seen_right, prev_marker, _, _, _) ((marker_here, is_even), left) =>
      let new_seen_right := seen_right || prev_marker
      let marker_left := match left with | some (m, _) => m | none => false
      let is_zero := left.isNone
      (new_seen_right, marker_here, is_even, marker_left, is_zero)
    q0 := (false, false, false, false, false)
    f := fun (seen_right, marker_here, is_even, marker_left, is_zero) =>
      if seen_right then (some (), some ())
      else if marker_here then (some (), some ())
      else if marker_left then
        if is_even then (none, none) else (some (), none)
      else if is_zero ∧ !is_even then (some (), none)
      else (none, none)

  def m2c_enriched_two_stage : TwoStageAdvice M2C_Enriched (Option Unit × Option Unit) where
    β := M2C_Enriched
    C := ca_trace_id_word M2C_Enriched
    M := m2c_enriched_fst'

  /-- The "marker seen at any position > 0" predicate over a word. -/
  def m2c_marker_or_tail (w : Word M2C_Enriched) : Bool :=
    (List.range (w.length - 1)).any fun k => (w[k + 1]!).1.1

  /-- Spec for the scanr state on a word w. -/
  lemma m2c_fst_scanr_word (w : Word M2C_Enriched) :
      let st := m2c_enriched_fst'.scanr_reduce w
      st.1 = m2c_marker_or_tail w ∧
      st.2.1 = (if 0 < w.length then (w[0]!).1.1 else false) := by
    induction w with
    | nil =>
      simp [FiniteStateTransducer.scanr_reduce, FiniteStateTransducer.scanr_reduce_q,
            m2c_enriched_fst', m2c_marker_or_tail]
    | cons a as ih =>
      simp only [FiniteStateTransducer.scanr_reduce, FiniteStateTransducer.scanr_reduce_q] at *
      obtain ⟨h_ih_1, h_ih_2⟩ := ih
      generalize h_st : m2c_enriched_fst'.scanr_reduce_q m2c_enriched_fst'.q0 as = st
      rw [h_st] at h_ih_1 h_ih_2
      obtain ⟨st1, st2, st3, st4, st5⟩ := st
      obtain ⟨⟨a_mh, a_ev⟩, a_left⟩ := a
      simp only at h_ih_1 h_ih_2
      refine ⟨?_, ?_⟩
      · show (m2c_enriched_fst'.δ (st1, st2, st3, st4, st5) ((a_mh, a_ev), a_left)).1
              = m2c_marker_or_tail (((a_mh, a_ev), a_left) :: as)
        simp only [m2c_enriched_fst']
        rw [h_ih_1, h_ih_2]
        unfold m2c_marker_or_tail
        simp only [List.length_cons, Nat.add_sub_cancel, List.getElem!_cons_succ]
        -- Goal: m2c_marker_or_tail-of-as part || (if 0 < as.length then (as[0]!).1.1 else false)
        --     = (range as.length).any (fun k => (as[k]!).1.1)
        cases hlen : as with
        | nil => simp
        | cons b bs =>
          simp only [List.length_cons, Nat.zero_lt_succ, ↓reduceIte,
                     List.getElem!_cons_zero, List.range_succ_eq_map, List.any_cons,
                     List.any_map, Function.comp_def, List.getElem!_cons_succ,
                     Nat.add_sub_cancel]
          rw [Bool.or_comm]
      · show (m2c_enriched_fst'.δ (st1, st2, st3, st4, st5) ((a_mh, a_ev), a_left)).2.1
              = (((a_mh, a_ev), a_left) :: as)[0]!.1.1
        simp [m2c_enriched_fst']

  /-- The marker-or over the tail of `w.drop (i+1)`, combined with the marker at position i+1,
      gives the marker-or over positions strictly greater than i. -/
  lemma m2c_marker_or_combined (w : Word M2C_Enriched) (i : ℕ) :
      (m2c_marker_or_tail (w.drop (i + 1)) ||
        (if 0 < (w.drop (i + 1)).length then ((w.drop (i + 1))[0]!).1.1 else false))
      = (List.range (w.length - i - 1)).any fun k => (w[i + 1 + k]!).1.1 := by
    -- (w.drop (i+1)).length = w.length - (i+1) = w.length - i - 1
    -- (w.drop (i+1))[k]! = w[i+1+k]! when in range; default otherwise
    simp only [List.length_drop]
    by_cases h_pos : 0 < w.length - (i + 1)
    · -- nonempty drop case
      simp only [h_pos, ↓reduceIte]
      -- Both sides combine: split (range n).any at first index
      have h_drop_zero : (w.drop (i + 1))[0]! = w[i + 1]! := by
        have h0 : 0 < (w.drop (i + 1)).length := by
          rw [List.length_drop]; exact h_pos
        have h1 : i + 1 < w.length := by
          simp only [List.length_drop] at h0; omega
        simp only [getElem!_def]
        rw [List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1]
        show (w.drop (i + 1))[0] = w[i + 1]
        rw [List.getElem_drop]
      rw [h_drop_zero]
      unfold m2c_marker_or_tail
      simp only [List.length_drop]
      -- LHS: (range (w.length - (i+1) - 1)).any (k => (w.drop (i+1))[k+1]!.1.1) || w[i+1]!.1.1
      -- RHS: (range (w.length - i - 1)).any (k => w[i+1+k]!.1.1)
      -- Note: w.length - (i+1) - 1 = w.length - i - 2, and w.length - i - 1 = w.length - (i+1)
      have h_len_eq : w.length - (i + 1) - 1 = w.length - i - 1 - 1 := by omega
      rw [h_len_eq]
      -- Rewrite (w.drop (i+1))[k+1]! = w[i+1+(k+1)]! = w[i+1+k+1]!
      have h_drop : ∀ k, ((w.drop (i + 1))[k + 1]!).1.1 = (w[i + 1 + (k + 1)]!).1.1 := by
        intro k
        by_cases h_in : k + 1 < (w.drop (i + 1)).length
        · simp only [getElem!_def]
          rw [List.getElem?_eq_getElem h_in]
          have h_in_w : i + 1 + (k + 1) < w.length := by
            simp only [List.length_drop] at h_in; omega
          rw [List.getElem?_eq_getElem h_in_w]
          show ((w.drop (i + 1))[k + 1]).1.1 = (w[i + 1 + (k + 1)]).1.1
          rw [List.getElem_drop]
        · push_neg at h_in
          simp only [getElem!_def]
          have h_in_w : ¬(i + 1 + (k + 1) < w.length) := by
            simp only [List.length_drop] at h_in; omega
          rw [List.getElem?_eq_none h_in, List.getElem?_eq_none (by omega)]
      have h_lhs_rw : (List.range (w.length - i - 1 - 1)).any
              (fun k => ((w.drop (i + 1))[k + 1]!).1.1)
            = (List.range (w.length - i - 1 - 1)).any
              (fun k => (w[i + 1 + (k + 1)]!).1.1) := by
        congr 1; funext k; exact h_drop k
      rw [h_lhs_rw]
      -- Now: (range (n-1)).any (k => w[i+1+(k+1)]!.1.1) || w[i+1]!.1.1
      --    = (range n).any (k => w[i+1+k]!.1.1), where n = w.length - i - 1
      have hn : w.length - i - 1 = (w.length - i - 1 - 1) + 1 := by omega
      -- Decompose the RHS via range_succ_eq_map
      have hrhs : (List.range (w.length - i - 1)).any (fun k => (w[i + 1 + k]!).1.1)
                = (w[i + 1]!.1.1
                  || (List.range (w.length - i - 1 - 1)).any
                       (fun k => (w[i + 1 + (k + 1)]!).1.1)) := by
        rw [hn, List.range_succ_eq_map, List.any_cons, List.any_map]
        show (w[i + 1 + 0]!.1.1 ||
                (List.range _).any (fun k => (w[i + 1 + (k + 1)]!).1.1))
              = _
        rw [Nat.add_zero, Nat.add_sub_cancel]
      rw [hrhs]
      exact Bool.or_comm _ _
    · -- empty drop case: w.length ≤ i + 1
      push_neg at h_pos
      have h_empty : w.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have h_zero : w.length - i - 1 = 0 := by omega
      rw [h_empty, h_zero]
      simp [m2c_marker_or_tail]
      -- remaining: i + 1 < w.length → default.1.1 = false; impossible since w.length ≤ i + 1
      intro h_lt
      omega

  theorem m2c_enriched_two_stage_spec :
      m2c_enriched_two_stage.advice = Advice.m2c_from_enriched := by
    apply advice_eq_iff
    funext w
    simp only [TwoStageAdvice.advice, m2c_enriched_two_stage,
               ca_trace_id_scan_temporal, Function.comp_apply, id_eq]
    simp only [Advice.m2c_from_enriched, m2c_from_enriched_fn]
    apply List.ext_getElem (by simp)
    intro i hi _
    have hi_w : i < w.length := by simp at hi; exact hi
    simp only [FiniteStateTransducer.scanr, List.getElem_map, List.getElem_range]
    -- Use scanr_get'_eq1 to express scanr at position i
    have h_scanr := FiniteStateTransducer.scanr_get'_eq1 (M := m2c_enriched_fst') w ⟨i, hi_w⟩
    have hi_scanr_q : i < (m2c_enriched_fst'.scanr_q m2c_enriched_fst'.q0 w).length := by
      simp [FiniteStateTransducer.scanr_q_len, hi_w]
    have h_scanr_nat : (m2c_enriched_fst'.scanr_q m2c_enriched_fst'.q0 w)[i]'hi_scanr_q =
        m2c_enriched_fst'.f (m2c_enriched_fst'.δ
          (m2c_enriched_fst'.scanr_reduce (w.drop (i + 1))) w[i]) := by
      have h := h_scanr
      simp only [FiniteStateTransducer.scanr_q] at h ⊢
      convert h using 1
    rw [h_scanr_nat]
    -- Apply state lemma to (w.drop (i+1))
    obtain ⟨h_st_1, h_st_2⟩ := m2c_fst_scanr_word (w.drop (i + 1))
    -- Destructure the state
    generalize h_st : m2c_enriched_fst'.scanr_reduce (w.drop (i + 1)) = st
    rw [h_st] at h_st_1 h_st_2
    obtain ⟨st1, st2, st3, st4, st5⟩ := st
    simp only at h_st_1 h_st_2
    -- Destructure w[i] for clarity (with equation)
    rcases h_wi_eq : w[i] with ⟨⟨wi_mh, wi_ev⟩, wi_left⟩
    -- Compute δ and f
    show m2c_enriched_fst'.f (m2c_enriched_fst'.δ (st1, st2, st3, st4, st5)
              ((wi_mh, wi_ev), wi_left)) = _
    simp only [m2c_enriched_fst']
    rw [h_st_1, h_st_2]
    -- The combined seen_right:
    rw [m2c_marker_or_combined w i]
    -- Now both sides have the same marker_seen_right form. Need to align with RHS.
    -- RHS uses w[i]! (i.e., List.get!Internal w i) while LHS uses destructured w[i].
    have h_wi_bang : w[i]! = (((wi_mh, wi_ev), wi_left) : M2C_Enriched) := by
      have h1 : w[i]! = w[i] := by simp [hi_w]
      rw [h1, h_wi_eq]
    show _ = _
    -- Replace List.get!Internal w i (which is w[i]!) with the destructured form
    change _ = (if _ = true then _ else
      if (w[i]!).1.1 = true then _ else
      if (match (w[i]!).2 with | some (m, _) => m | none => false) = true then
        (if (w[i]!).1.2 = true then _ else _)
      else if (w[i]!).2.isNone = true ∧ (w[i]!).1.2 = false then _ else _)
    rw [h_wi_bang]
    -- Now both sides match modulo `!wi_ev` vs `wi_ev = false`
    cases wi_ev <;> simp

  def m2c_from_enriched_is_two_stage :
      Advice.m2c_from_enriched.is_two_stage_advice :=
    ⟨m2c_enriched_two_stage, m2c_enriched_two_stage_spec⟩

  /-- middle_to_compress2 is RT-closed.
      Proof: decompose as with_left_neighbor.compose m2c_from_enriched.
      Both are RT-closed (two-stage), so composition is RT-closed. -/
  noncomputable def middle_to_compress2_is_rt_closed : Advice.middle_to_compress2.rt_closed := by
    rw [middle_to_compress2_eq_compose]
    exact Advice.rt_closed_compose_rt_closed
      (Advice.with_left_neighbor (Bool × Bool))
      Advice.m2c_from_enriched
      (Advice.with_left_neighbor_rt_closed (Bool × Bool))
      (by rw [← m2c_enriched_two_stage_spec]; exact two_stage_is_rt_closed m2c_enriched_two_stage)

end TwoStageProofs


/-!
## Section 5: Main Theorem

Combine everything to prove the equivalence.
-/

section MainTheorem

  /-- If compress2 is weak-rt-closed, then middle is weak-rt-closed. -/
  noncomputable def compress2_weak_implies_middle_weak
      (h: (Advice.compress2 Unit).weak_rt_closed):
      (Advice.middle Unit).weak_rt_closed := by
    rw [middle_eq_compress2_compose_g]
    have h_g_rt : Advice.compress2_to_middle.rt_closed := by
      rw [← compress2_to_middle_two_stage_spec]
      exact two_stage_is_rt_closed compress2_to_middle_two_stage
    exact Advice.weak_rt_closed_compose_rt_closed
      (Advice.compress2 Unit)
      Advice.compress2_to_middle
      h
      h_g_rt

  /-- If middle is weak-rt-closed, then compress2 is weak-rt-closed. -/
  noncomputable def middle_weak_implies_compress2_weak
      (h: (Advice.middle Unit).weak_rt_closed):
      (Advice.compress2 Unit).weak_rt_closed := by
    rw [compress2_eq_middle_compose_h]
    -- First: (middle Unit).compose pair_with_parity is weak-rt-closed
    have h_paired_weak : ((Advice.middle Unit).compose Advice.pair_with_parity).weak_rt_closed := by
      exact Advice.weak_rt_closed_compose_rt_closed
        (Advice.middle Unit)
        Advice.pair_with_parity
        h
        Advice.pair_with_parity_rt_closed
    -- Then: compose with middle_to_compress2 (which is rt-closed)
    have h_h_rt : Advice.middle_to_compress2.rt_closed :=
      middle_to_compress2_is_rt_closed
    exact Advice.weak_rt_closed_compose_rt_closed
      ((Advice.middle Unit).compose Advice.pair_with_parity)
      Advice.middle_to_compress2
      h_paired_weak
      h_h_rt

  /-- Main theorem: the two weak-rt-closed conditions are equivalent (over Unit). -/
  theorem middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary:
      Nonempty (Advice.middle Unit).weak_rt_closed ↔
      Nonempty (Advice.compress2 Unit).weak_rt_closed := by
    constructor
    · intro ⟨h⟩
      exact ⟨middle_weak_implies_compress2_weak h⟩
    · intro ⟨h⟩
      exact ⟨compress2_weak_implies_middle_weak h⟩

  #print axioms middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary

end MainTheorem

end CellularAutomatas
