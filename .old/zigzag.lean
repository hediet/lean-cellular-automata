/-
Zigzag folding geometry, factored out from cellular automata concerns.

The "zigzag" pattern maps positions p ∈ ℤ to (cell, lane) pairs where:
- lane = p / width
- cell = p % width  (if lane is even)
- cell = width - 1 - (p % width)  (if lane is odd, i.e., reversed)
-/

import Mathlib.Tactic
import CellularAutomatas.proofs.int_lemmas

open CellularAutomatas

/-- Coordinate in the zigzag folding: cell index within a lane, and lane number -/
@[ext]
structure Coord where
  cell : ℤ
  lane : ℤ
  deriving DecidableEq

namespace Coord

/-- Whether the lane is reversed (odd lanes run backwards) -/
def is_reversed (c : Coord) : Prop := c.lane % 2 ≠ 0

instance (c : Coord) : Decidable c.is_reversed := by unfold is_reversed; infer_instance

end Coord

/-- A zigzag folding with a given lane width -/
structure ZigzagFold where
  width : ℕ
  width_pos : width > 0

namespace ZigzagFold

variable (z : ZigzagFold)

/-- Whether the lane is reversed (odd lanes run backwards) -/
def is_reversed (lane : ℤ) : Prop := lane % 2 ≠ 0

instance (lane : ℤ) : Decidable (is_reversed lane) := by unfold is_reversed; infer_instance

/-- Map a position to (cell, lane) coordinates -/
def fold (p : ℤ) : Coord :=
  let lane := p / z.width
  let rem := p % z.width
  let cell := if is_reversed lane then (z.width : ℤ) - 1 - rem else rem
  ⟨cell, lane⟩

/-- Map (cell, lane) back to position -/
def unfold (c : Coord) : ℤ :=
  if is_reversed c.lane then (c.lane + 1) * z.width - 1 - c.cell
  else c.lane * z.width + c.cell

theorem width_pos_int : (z.width : ℤ) > 0 := Int.natCast_pos.mpr z.width_pos
theorem width_ne_zero : (z.width : ℤ) ≠ 0 := ne_of_gt z.width_pos_int

/-- unfold ∘ fold = id -/
theorem unfold_fold (p : ℤ) : z.unfold (z.fold p) = p := by
  simp only [fold, unfold]
  have w_pos := z.width_pos_int
  split_ifs <;> (have h := Int.emod_add_mul_ediv p z.width; linarith)

/-- fold ∘ unfold = id (when cell is in valid range) -/
theorem fold_unfold (c : Coord) (h_cell : 0 ≤ c.cell ∧ c.cell < z.width) :
    z.fold (z.unfold c) = c := by
  have w_pos := z.width_pos_int
  have w_ne := z.width_ne_zero
  simp only [fold, unfold]
  by_cases h_odd : is_reversed c.lane
  · -- Odd lane
    have h_rem : 0 ≤ (z.width : ℤ) - 1 - c.cell ∧ (z.width : ℤ) - 1 - c.cell < z.width := ⟨by linarith, by linarith⟩
    have key : (c.lane + 1) * z.width - 1 - c.cell = ((z.width : ℤ) - 1 - c.cell) + z.width * c.lane := by ring
    simp only [h_odd, ↓reduceIte, key]
    have h_div : (((z.width : ℤ) - 1 - c.cell) + z.width * c.lane) / z.width = c.lane := by
      rw [Int.add_mul_ediv_left _ _ w_ne, Int.ediv_eq_zero_of_lt h_rem.1 h_rem.2]; ring
    have h_mod : (((z.width : ℤ) - 1 - c.cell) + z.width * c.lane) % z.width = (z.width : ℤ) - 1 - c.cell := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h_rem.1 h_rem.2]
    rw [h_div, h_mod]
    simp only [h_odd, ↓reduceIte, sub_sub_cancel]
  · -- Even lane
    have key : c.lane * z.width + c.cell = c.cell + z.width * c.lane := by ring
    simp only [h_odd, ↓reduceIte, key]
    have h_div : (c.cell + z.width * c.lane) / z.width = c.lane := by
      rw [Int.add_mul_ediv_left _ _ w_ne, Int.ediv_eq_zero_of_lt h_cell.1 h_cell.2]; ring
    have h_mod : (c.cell + z.width * c.lane) % z.width = c.cell := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h_cell.1 h_cell.2]
    rw [h_div, h_mod]
    simp only [h_odd, ↓reduceIte]

/-- fold(p-1) when in same lane -/
theorem fold_pred_same_lane (p : ℤ) (h : p % z.width > 0) :
    (z.fold (p - 1)).lane = (z.fold p).lane ∧
    (z.fold (p - 1)).cell = if is_reversed (z.fold p).lane then (z.fold p).cell + 1 else (z.fold p).cell - 1 := by
  have w_pos := z.width_pos_int
  simp only [fold]
  rw [Int.ediv_sub_one_of_emod_pos w_pos h, Int.emod_sub_one_of_emod_pos w_pos h]
  constructor
  · rfl
  · split_ifs <;> ring

/-- fold(p-1) crosses to previous lane from EVEN lane (cell=0 → prev lane cell=0) -/
theorem fold_pred_cross_lane_even (p : ℤ) (h : p % z.width = 0)
    (h_even : (p / z.width) % 2 = 0) :
    z.fold (p - 1) = ⟨0, p / z.width - 1⟩ := by
  have w_pos := z.width_pos_int
  simp only [fold]
  rw [Int.ediv_sub_one_of_emod_eq_zero w_pos h, Int.emod_sub_one_of_emod_eq_zero w_pos h]
  have h_new_odd : is_reversed (p / z.width - 1) := by unfold is_reversed; omega
  simp only [h_new_odd, ↓reduceIte, sub_self]

/-- fold(p-1) crosses to previous lane from ODD lane (cell=width-1 → prev lane cell=width-1) -/
theorem fold_pred_cross_lane_odd (p : ℤ) (h : p % z.width = 0)
    (h_odd : (p / z.width) % 2 ≠ 0) :
    z.fold (p - 1) = ⟨(z.width : ℤ) - 1, p / z.width - 1⟩ := by
  have w_pos := z.width_pos_int
  simp only [fold]
  rw [Int.ediv_sub_one_of_emod_eq_zero w_pos h, Int.emod_sub_one_of_emod_eq_zero w_pos h]
  have h_new_even : ¬is_reversed (p / z.width - 1) := by unfold is_reversed; omega
  simp only [h_new_even, ↓reduceIte]

/-- fold(p+1) when in same lane -/
theorem fold_succ_same_lane (p : ℤ) (h : p % z.width < z.width - 1) :
    (z.fold (p + 1)).lane = (z.fold p).lane ∧
    (z.fold (p + 1)).cell = if is_reversed (z.fold p).lane then (z.fold p).cell - 1 else (z.fold p).cell + 1 := by
  have w_pos := z.width_pos_int
  simp only [fold]
  rw [Int.ediv_add_one_of_emod_lt_sub_one w_pos h, Int.emod_add_one_of_emod_lt_sub_one w_pos h]
  constructor
  · rfl
  · split_ifs <;> ring

/-- fold(p+1) crosses to next lane from EVEN lane (cell=width-1 → next lane cell=width-1) -/
theorem fold_succ_cross_lane_even (p : ℤ) (h : p % z.width = z.width - 1)
    (h_even : (p / z.width) % 2 = 0) :
    z.fold (p + 1) = ⟨(z.width : ℤ) - 1, p / z.width + 1⟩ := by
  have w_pos := z.width_pos_int
  simp only [fold]
  rw [Int.ediv_add_one_of_emod_eq_sub_one w_pos h, Int.emod_add_one_of_emod_eq_sub_one h]
  have h_new_odd : is_reversed (p / z.width + 1) := by unfold is_reversed; omega
  simp only [h_new_odd, ↓reduceIte, sub_zero]

/-- fold(p+1) crosses to next lane from ODD lane (cell=0 → next lane cell=0) -/
theorem fold_succ_cross_lane_odd (p : ℤ) (h : p % z.width = z.width - 1)
    (h_odd : (p / z.width) % 2 ≠ 0) :
    z.fold (p + 1) = ⟨0, p / z.width + 1⟩ := by
  have w_pos := z.width_pos_int
  simp only [fold]
  rw [Int.ediv_add_one_of_emod_eq_sub_one w_pos h, Int.emod_add_one_of_emod_eq_sub_one h]
  have h_new_even : ¬is_reversed (p / z.width + 1) := by unfold is_reversed; omega
  simp only [h_new_even, ↓reduceIte]

/-- The lane changes by at most 1 when moving left -/
theorem lane_pred_cases (p : ℤ) :
    (z.fold (p - 1)).lane = (z.fold p).lane ∨ (z.fold (p - 1)).lane = (z.fold p).lane - 1 := by
  have w_pos := z.width_pos_int
  have h_mod_nonneg : 0 ≤ p % z.width := Int.emod_nonneg _ (by omega)
  by_cases h : p % z.width = 0
  · right
    simp only [fold]
    rw [Int.ediv_sub_one_of_emod_eq_zero w_pos h]
  · left
    exact (z.fold_pred_same_lane p (by omega)).1

/-- The lane changes by at most 1 when moving right -/
theorem lane_succ_cases (p : ℤ) :
    (z.fold (p + 1)).lane = (z.fold p).lane ∨ (z.fold (p + 1)).lane = (z.fold p).lane + 1 := by
  have w_pos := z.width_pos_int
  have h_mod_lt : p % z.width < z.width := Int.emod_lt_of_pos _ w_pos
  by_cases h : p % z.width = z.width - 1
  · right
    simp only [fold]
    rw [Int.ediv_add_one_of_emod_eq_sub_one w_pos h]
  · left
    exact (z.fold_succ_same_lane p (by omega)).1

end ZigzagFold
