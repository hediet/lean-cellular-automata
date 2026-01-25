/-
  Zigzag Folding - A bijection between ℤ and (cell_pos, lane_idx) pairs

  Visualized for width=3, lanes -2..2:

  Original positions:    ...-6 -5 -4 -3 -2 -1 [0 1 2] 3 4 5 6 7 8...

  Lane -2:                  -6 -5 -4
  Lane -1:                  -1 -2 -3           (reversed!)
  Lane  0:                            [0 1 2]
  Lane  1:                                      5 4 3  (reversed!)
  Lane  2:                                      6 7 8

  The zigzag pattern ensures that when crossing a lane boundary,
  the adjacent cells are neighbors (e.g., position 2 and 3 are both at cell 2,
  in lanes 0 and 1 respectively).
-/

import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.ModEq

namespace CellularAutomatas

structure Zigzag where
  width : ℕ
  h_width : width > 0 := by omega

namespace Zigzag

-- Core definitions (taking z explicitly for cleaner usage)

def width_int (z : Zigzag) : ℤ := z.width

def lane_of (z : Zigzag) (p : ℤ) : ℤ := p / z.width

def is_reversed (lane : ℤ) : Bool := lane % 2 ≠ 0

def cell_of (z : Zigzag) (p : ℤ) : ℤ :=
  let rem := p % z.width
  if is_reversed (lane_of z p) then z.width - 1 - rem else rem

-- The fold operation: position → (cell, lane)
def fold (z : Zigzag) (p : ℤ) : ℤ × ℤ := (cell_of z p, lane_of z p)

-- The unfold operation: (cell, lane) → position
def unfold (z : Zigzag) (cell lane : ℤ) : ℤ :=
  if is_reversed lane then
    (lane + 1) * z.width - 1 - cell
  else
    lane * z.width + cell

/-! ## Basic Properties -/

lemma width_pos (z : Zigzag) : (z.width : ℤ) > 0 := Int.natCast_pos.mpr z.h_width

lemma width_ne_zero (z : Zigzag) : (z.width : ℤ) ≠ 0 := ne_of_gt (width_pos z)

-- cell_of is always in range [0, width)
lemma cell_range (z : Zigzag) (p : ℤ) : 0 ≤ cell_of z p ∧ cell_of z p < z.width := by
  unfold cell_of is_reversed lane_of
  have h_mod_range : 0 ≤ p % z.width ∧ p % z.width < z.width := by
    constructor
    · exact Int.emod_nonneg p (width_ne_zero z)
    · exact Int.emod_lt_of_pos p (width_pos z)
  split_ifs with h_odd
  · -- reversed lane: width - 1 - rem
    constructor <;> omega
  · -- normal lane: rem
    exact h_mod_range

/-! ## Fold and Unfold are Inverses -/

lemma unfold_fold (z : Zigzag) (p : ℤ) : unfold z (cell_of z p) (lane_of z p) = p := by
  unfold unfold cell_of lane_of is_reversed
  have h_div_mod : p = (p / z.width) * z.width + p % z.width := (Int.ediv_add_emod p z.width).symm
  split_ifs with h_odd
  · -- reversed lane
    calc (p / z.width + 1) * z.width - 1 - (z.width - 1 - p % z.width)
        = (p / z.width) * z.width + z.width - 1 - z.width + 1 + p % z.width := by ring
      _ = (p / z.width) * z.width + p % z.width := by ring
      _ = p := h_div_mod.symm
  · -- normal lane
    calc (p / z.width) * z.width + p % z.width = p := h_div_mod.symm

lemma fold_unfold (z : Zigzag) (cell lane : ℤ) (h_cell : 0 ≤ cell ∧ cell < z.width) :
    fold z (unfold z cell lane) = (cell, lane) := by
  unfold fold unfold cell_of lane_of is_reversed
  have w_pos := width_pos z
  have w_ne := width_ne_zero z

  split_ifs with h_odd
  · -- reversed lane (odd)
    -- Position is: (lane + 1) * width - 1 - cell
    set pos := (lane + 1) * z.width - 1 - cell with h_pos

    -- Compute lane_of pos
    have h_lane : pos / z.width = lane := by
      have key : pos = lane * z.width + (z.width - 1 - cell) := by rw [h_pos]; ring
      rw [key]
      have h_rem : 0 ≤ z.width - 1 - cell ∧ z.width - 1 - cell < z.width := by omega
      rw [Int.add_mul_ediv_right _ lane w_ne]
      rw [Int.ediv_eq_zero_of_lt h_rem.1 h_rem.2]
      ring

    -- Compute pos % width
    have h_mod : pos % z.width = z.width - 1 - cell := by
      have key : pos = lane * z.width + (z.width - 1 - cell) := by rw [h_pos]; ring
      rw [key]
      have h_rem : 0 ≤ z.width - 1 - cell ∧ z.width - 1 - cell < z.width := by omega
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt h_rem.1 h_rem.2

    simp only [h_lane, h_odd, ↓reduceIte, h_mod, Prod.mk.injEq]
    constructor <;> omega

  · -- normal lane (even)
    -- Position is: lane * width + cell
    set pos := lane * z.width + cell with h_pos

    -- Compute lane_of pos
    have h_lane : pos / z.width = lane := by
      rw [h_pos]
      rw [Int.add_mul_ediv_right cell lane w_ne]
      rw [Int.ediv_eq_zero_of_lt h_cell.1 h_cell.2]
      ring

    -- Compute pos % width
    have h_mod : pos % z.width = cell := by
      rw [h_pos]
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt h_cell.1 h_cell.2

    simp only [h_lane, h_odd, ↓reduceIte, h_mod, Prod.mk.injEq, and_self]

/-! ## Neighborhood Preservation -/

-- When moving left (p → p-1), how does (cell, lane) change?
inductive StepResult
  | same_lane (new_cell : ℤ)       -- stay in same lane, cell changes
  | cross_boundary                  -- move to adjacent lane

-- Helper: compute result of stepping left
def step_left_result (z : Zigzag) (cell lane : ℤ) : StepResult :=
  if is_reversed lane then
    -- In reversed lane: left in world = right in cell coords
    if cell < z.width - 1 then .same_lane (cell + 1)
    else .cross_boundary
  else
    -- In normal lane: left in world = left in cell coords
    if cell > 0 then .same_lane (cell - 1)
    else .cross_boundary

-- Helper: compute result of stepping right
def step_right_result (z : Zigzag) (cell lane : ℤ) : StepResult :=
  if is_reversed lane then
    -- In reversed lane: right in world = left in cell coords
    if cell > 0 then .same_lane (cell - 1)
    else .cross_boundary
  else
    -- In normal lane: right in world = right in cell coords
    if cell < z.width - 1 then .same_lane (cell + 1)
    else .cross_boundary

-- The key lemma: stepping left in position space
lemma fold_pred (z : Zigzag) (p : ℤ) :
    let (cell, lane) := fold z p
    match step_left_result z cell lane with
    | .same_lane c => fold z (p - 1) = (c, lane)
    | .cross_boundary => fold z (p - 1) = (if is_reversed lane then 0 else z.width - 1, lane - 1) := by
  unfold fold cell_of lane_of step_left_result is_reversed
  have w_pos := width_pos z
  have w_ne := width_ne_zero z

  set lane := p / z.width with h_lane_def
  set rem := p % z.width with h_rem_def

  have h_div_mod : p = lane * z.width + rem := by
    rw [h_lane_def, h_rem_def]
    exact (Int.ediv_add_emod p z.width).symm

  have h_rem_range : 0 ≤ rem ∧ rem < z.width := by
    rw [h_rem_def]
    exact ⟨Int.emod_nonneg p w_ne, Int.emod_lt_of_pos p w_pos⟩

  -- Case split on whether lane is odd
  by_cases h_odd : lane % 2 ≠ 0
  · -- Odd lane (reversed)
    simp only [h_odd, ↓reduceIte, decide_not, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, ne_eq, ite_not]
    set cell := z.width - 1 - rem with h_cell_def

    -- Case split on whether cell < width - 1 (i.e., rem > 0)
    by_cases h_not_boundary : cell < z.width - 1
    · -- Not at boundary: stay in lane, cell increases
      simp only [h_not_boundary, ↓reduceIte, Prod.mk.injEq]
      have h_rem_pos : rem > 0 := by omega

      have h_lane' : (p - 1) / z.width = lane := by
        have key : p - 1 = lane * z.width + (rem - 1) := by omega
        rw [key]
        have h_rem' : 0 ≤ rem - 1 ∧ rem - 1 < z.width := by omega
        rw [Int.add_mul_ediv_right _ lane w_ne]
        rw [Int.ediv_eq_zero_of_lt h_rem'.1 h_rem'.2]
        ring

      have h_mod' : (p - 1) % z.width = rem - 1 := by
        have key : p - 1 = lane * z.width + (rem - 1) := by omega
        rw [key]
        have h_rem' : 0 ≤ rem - 1 ∧ rem - 1 < z.width := by omega
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt h_rem'.1 h_rem'.2

      simp only [h_lane', h_odd, ne_eq, ↓reduceIte, ite_not, h_mod']
      constructor <;> omega

    · -- At boundary (cell = width - 1, so rem = 0): cross to lane - 1
      simp only [h_not_boundary, ↓reduceIte, Prod.mk.injEq]
      have h_rem_zero : rem = 0 := by omega

      have h_lane' : (p - 1) / z.width = lane - 1 := by
        have key : p - 1 = (lane - 1) * z.width + (z.width - 1) := by
          rw [h_div_mod, h_rem_zero]; ring
        rw [key]
        have h_rem' : 0 ≤ z.width - 1 ∧ z.width - 1 < z.width := by omega
        rw [Int.add_mul_ediv_right _ (lane - 1) w_ne]
        rw [Int.ediv_eq_zero_of_lt h_rem'.1 h_rem'.2]
        ring

      have h_mod' : (p - 1) % z.width = z.width - 1 := by
        have key : p - 1 = (lane - 1) * z.width + (z.width - 1) := by
          rw [h_div_mod, h_rem_zero]; ring
        rw [key]
        have h_rem' : 0 ≤ z.width - 1 ∧ z.width - 1 < z.width := by omega
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt h_rem'.1 h_rem'.2

      -- lane - 1 has opposite parity
      have h_even' : (lane - 1) % 2 = 0 := by omega

      simp only [h_lane', h_even', ne_eq, not_true_eq_false, ↓reduceIte, ite_not, h_mod',
        Prod.mk.injEq]
      omega

  · -- Even lane (not reversed)
    simp only [h_odd, not_not, not_true_eq_false, ↓reduceIte, decide_not, decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_false, ite_not, ne_eq]
    set cell := rem with h_cell_def

    -- Case split on whether cell > 0
    by_cases h_not_boundary : cell > 0
    · -- Not at boundary: stay in lane, cell decreases
      simp only [h_not_boundary, ↓reduceIte, Prod.mk.injEq]

      have h_lane' : (p - 1) / z.width = lane := by
        have key : p - 1 = lane * z.width + (rem - 1) := by omega
        rw [key]
        have h_rem' : 0 ≤ rem - 1 ∧ rem - 1 < z.width := by omega
        rw [Int.add_mul_ediv_right _ lane w_ne]
        rw [Int.ediv_eq_zero_of_lt h_rem'.1 h_rem'.2]
        ring

      have h_mod' : (p - 1) % z.width = rem - 1 := by
        have key : p - 1 = lane * z.width + (rem - 1) := by omega
        rw [key]
        have h_rem' : 0 ≤ rem - 1 ∧ rem - 1 < z.width := by omega
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt h_rem'.1 h_rem'.2

      simp only [h_lane', h_odd, not_not, not_false_eq_true, ↓reduceIte, ite_not, h_mod', ne_eq]
      omega

    · -- At boundary (cell = 0): cross to lane - 1
      simp only [h_not_boundary, ↓reduceIte, Prod.mk.injEq]
      have h_rem_zero : rem = 0 := by omega

      have h_lane' : (p - 1) / z.width = lane - 1 := by
        have key : p - 1 = (lane - 1) * z.width + (z.width - 1) := by
          rw [h_div_mod, h_rem_zero]; ring
        rw [key]
        have h_rem' : 0 ≤ z.width - 1 ∧ z.width - 1 < z.width := by omega
        rw [Int.add_mul_ediv_right _ (lane - 1) w_ne]
        rw [Int.ediv_eq_zero_of_lt h_rem'.1 h_rem'.2]
        ring

      have h_mod' : (p - 1) % z.width = z.width - 1 := by
        have key : p - 1 = (lane - 1) * z.width + (z.width - 1) := by
          rw [h_div_mod, h_rem_zero]; ring
        rw [key]
        have h_rem' : 0 ≤ z.width - 1 ∧ z.width - 1 < z.width := by omega
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt h_rem'.1 h_rem'.2

      -- lane - 1 has opposite parity (now odd)
      have h_odd' : (lane - 1) % 2 ≠ 0 := by omega

      simp only [h_lane', h_odd', ne_eq, not_false_eq_true, ↓reduceIte, ite_not, h_mod',
        Prod.mk.injEq]
      omega

-- The key lemma: stepping right in position space
lemma fold_succ (z : Zigzag) (p : ℤ) :
    let (cell, lane) := fold z p
    match step_right_result z cell lane with
    | .same_lane c => fold z (p + 1) = (c, lane)
    | .cross_boundary => fold z (p + 1) = (if is_reversed lane then z.width - 1 else 0, lane + 1) := by
  unfold fold cell_of lane_of step_right_result is_reversed
  have w_pos := width_pos z
  have w_ne := width_ne_zero z

  set lane := p / z.width with h_lane_def
  set rem := p % z.width with h_rem_def

  have h_div_mod : p = lane * z.width + rem := by
    rw [h_lane_def, h_rem_def]
    exact (Int.ediv_add_emod p z.width).symm

  have h_rem_range : 0 ≤ rem ∧ rem < z.width := by
    rw [h_rem_def]
    exact ⟨Int.emod_nonneg p w_ne, Int.emod_lt_of_pos p w_pos⟩

  -- Case split on whether lane is odd
  by_cases h_odd : lane % 2 ≠ 0
  · -- Odd lane (reversed)
    simp only [h_odd, ↓reduceIte, decide_not, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, ne_eq, ite_not]
    set cell := z.width - 1 - rem with h_cell_def

    -- Case split on whether cell > 0 (i.e., rem < width - 1)
    by_cases h_not_boundary : cell > 0
    · -- Not at boundary: stay in lane, cell decreases
      simp only [h_not_boundary, ↓reduceIte, Prod.mk.injEq]
      have h_rem_lt : rem < z.width - 1 := by omega

      have h_lane' : (p + 1) / z.width = lane := by
        have key : p + 1 = lane * z.width + (rem + 1) := by omega
        rw [key]
        have h_rem' : 0 ≤ rem + 1 ∧ rem + 1 < z.width := by omega
        rw [Int.add_mul_ediv_right _ lane w_ne]
        rw [Int.ediv_eq_zero_of_lt h_rem'.1 h_rem'.2]
        ring

      have h_mod' : (p + 1) % z.width = rem + 1 := by
        have key : p + 1 = lane * z.width + (rem + 1) := by omega
        rw [key]
        have h_rem' : 0 ≤ rem + 1 ∧ rem + 1 < z.width := by omega
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt h_rem'.1 h_rem'.2

      simp only [h_lane', h_odd, ne_eq, ↓reduceIte, ite_not, h_mod']
      omega

    · -- At boundary (cell = 0, so rem = width - 1): cross to lane + 1
      simp only [h_not_boundary, ↓reduceIte, Prod.mk.injEq]
      have h_rem_max : rem = z.width - 1 := by omega

      have h_lane' : (p + 1) / z.width = lane + 1 := by
        have key : p + 1 = (lane + 1) * z.width + 0 := by
          rw [h_div_mod, h_rem_max]; ring
        rw [key]
        simp only [add_zero, Int.mul_ediv_cancel_left _ w_ne]

      have h_mod' : (p + 1) % z.width = 0 := by
        have key : p + 1 = (lane + 1) * z.width + 0 := by
          rw [h_div_mod, h_rem_max]; ring
        rw [key]
        simp only [add_zero, Int.mul_emod_left]

      -- lane + 1 has opposite parity (now even)
      have h_even' : (lane + 1) % 2 = 0 := by omega

      simp only [h_lane', h_even', ne_eq, not_true_eq_false, ↓reduceIte, ite_not, h_mod',
        Prod.mk.injEq]
      omega

  · -- Even lane (not reversed)
    simp only [h_odd, not_not, not_true_eq_false, ↓reduceIte, decide_not, decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_false, ite_not, ne_eq]
    set cell := rem with h_cell_def

    -- Case split on whether cell < width - 1
    by_cases h_not_boundary : cell < z.width - 1
    · -- Not at boundary: stay in lane, cell increases
      simp only [h_not_boundary, ↓reduceIte, Prod.mk.injEq]

      have h_lane' : (p + 1) / z.width = lane := by
        have key : p + 1 = lane * z.width + (rem + 1) := by omega
        rw [key]
        have h_rem' : 0 ≤ rem + 1 ∧ rem + 1 < z.width := by omega
        rw [Int.add_mul_ediv_right _ lane w_ne]
        rw [Int.ediv_eq_zero_of_lt h_rem'.1 h_rem'.2]
        ring

      have h_mod' : (p + 1) % z.width = rem + 1 := by
        have key : p + 1 = lane * z.width + (rem + 1) := by omega
        rw [key]
        have h_rem' : 0 ≤ rem + 1 ∧ rem + 1 < z.width := by omega
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt h_rem'.1 h_rem'.2

      simp only [h_lane', h_odd, not_not, ↓reduceIte, ite_not, h_mod', ne_eq]
      omega

    · -- At boundary (cell = width - 1): cross to lane + 1
      simp only [h_not_boundary, ↓reduceIte, Prod.mk.injEq]
      have h_rem_max : rem = z.width - 1 := by omega

      have h_lane' : (p + 1) / z.width = lane + 1 := by
        have key : p + 1 = (lane + 1) * z.width + 0 := by
          rw [h_div_mod, h_rem_max]; ring
        rw [key]
        simp only [add_zero, Int.mul_ediv_cancel_left _ w_ne]

      have h_mod' : (p + 1) % z.width = 0 := by
        have key : p + 1 = (lane + 1) * z.width + 0 := by
          rw [h_div_mod, h_rem_max]; ring
        rw [key]
        simp only [add_zero, Int.mul_emod_left]

      -- lane + 1 has opposite parity (now odd)
      have h_odd' : (lane + 1) % 2 ≠ 0 := by omega

      simp only [h_lane', h_odd', ne_eq, not_false_eq_true, ↓reduceIte, ite_not, h_mod',
        Prod.mk.injEq]
      omega

/-! ## Tests -/

#guard fold (Zigzag.mk 3) 0 = (0, 0)
#guard fold (Zigzag.mk 3) 1 = (1, 0)
#guard fold (Zigzag.mk 3) 2 = (2, 0)
#guard fold (Zigzag.mk 3) 3 = (2, 1)  -- Reversed!
#guard fold (Zigzag.mk 3) 4 = (1, 1)
#guard fold (Zigzag.mk 3) 5 = (0, 1)
#guard fold (Zigzag.mk 3) 6 = (0, 2)
#guard fold (Zigzag.mk 3) 7 = (1, 2)
#guard fold (Zigzag.mk 3) 8 = (2, 2)

#guard fold (Zigzag.mk 3) (-1) = (0, -1)  -- Negative: reversed!
#guard fold (Zigzag.mk 3) (-2) = (1, -1)
#guard fold (Zigzag.mk 3) (-3) = (2, -1)
#guard fold (Zigzag.mk 3) (-4) = (2, -2)  -- Back to normal
#guard fold (Zigzag.mk 3) (-5) = (1, -2)
#guard fold (Zigzag.mk 3) (-6) = (0, -2)

end Zigzag

end CellularAutomatas
