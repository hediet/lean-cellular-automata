import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

namespace CellularAutomatas

structure DeadBorderCoord where
  c: ℕ

namespace DeadBorderCoord

  variable (e: DeadBorderCoord)

  def is_valid_idx (p: ℤ): Prop := -e.c ≤ p ∧ p ≤ e.c
  instance : DecidablePred (e.is_valid_idx) := fun _ => inferInstanceAs (Decidable (_ ∧ _))
  abbrev LaneIdx := { p: ℤ // is_valid_idx e p }

  def lanes_finset : Finset ℤ := Finset.Icc (-e.c) e.c
  instance : Fintype (e.LaneIdx) := Fintype.ofFinset (lanes_finset e) (by
    intro i
    rw [lanes_finset, Finset.mem_Icc]
    exact Iff.rfl)
  instance : Inhabited (e.LaneIdx) := ⟨⟨0, by simp [is_valid_idx]; try omega⟩⟩


  abbrev FoldedPos := ℤ × e.LaneIdx

  instance : Repr e.FoldedPos where
    reprPrec p _ := "(p: " ++ repr p.1 ++ ", laneIdx: " ++ repr p.2.val ++ ")"


  def map_coord (w_len: ℕ) (p: ℤ): Option e.FoldedPos :=
    if w_len = 0 then
      none
    else
      let lane_idx := p / w_len
      if h_lane : e.is_valid_idx lane_idx then
        let p := if lane_idx % 2 = 0 then p % w_len else w_len - 1 - (p % w_len)
        some (p, ⟨lane_idx, h_lane⟩)
      else
        none

  lemma map_coord_p_lane_0 (w_len: ℕ) (p: ℤ) (h: 0 ≤ p ∧ p < w_len): e.map_coord w_len p = some (p, ⟨0, by simp [is_valid_idx]⟩) := by
    unfold map_coord
    have h_nz : w_len ≠ 0 := by omega
    simp [h_nz]
    have h_div : p / (w_len : ℤ) = 0 := by
       apply Int.ediv_eq_zero_of_lt h.1 h.2
    rw [h_div]
    simp [is_valid_idx]
    apply Int.emod_eq_of_lt h.1 h.2

  lemma map_coord_p_lane (w_len: ℕ) (p cell_p: ℤ) (lane_idx) (h: e.map_coord w_len p = some (cell_p, lane_idx)):
      0 ≤ cell_p ∧ cell_p < w_len := by
    simp [map_coord] at h
    obtain ⟨_, eq_p, eq_l⟩ := h
    rw [←eq_p]
    have : (w_len : ℤ) > 0 := by omega
    have h_mod_nonneg : 0 ≤ p % (w_len : ℤ) := Int.emod_nonneg p (by omega)
    have h_mod_lt : p % (w_len : ℤ) < w_len := Int.emod_lt_of_pos p (by omega)
    omega

  lemma map_coord_p_range (w_len: ℕ) (p cell_p: ℤ) (lane_idx)
    (h1: e.map_coord w_len p = some (cell_p, lane_idx))
    (h2: ¬(0 ≤ p ∧ p < w_len)):
      lane_idx.val ≠ 0 := by
    simp [map_coord] at h1
    obtain ⟨_, _, eq_l⟩ := h1
    have : (w_len : ℤ) > 0 := by omega
    rw [←eq_l]
    intro h_div_zero
    have : 0 ≤ p ∧ p < w_len := by
      have : p = p % w_len := by
          rw [←Int.mul_ediv_add_emod p w_len]
          simp [h_div_zero]
      rw [this]
      constructor
      · apply Int.emod_nonneg; omega
      · apply Int.emod_lt_of_pos; omega
    contradiction


  /-
  ...  #  # -6 -5 -4 -3 -2 -1 [ 0  1  2] 3  4  5  6  7  8  #  #
  ...
  ...  laneIdx: -2             -6 -5 -4
  ...  laneIdx: -1             -1 -2 -3
  ...  laneIdx:  0    #  #  # [ 0  1  2] #  #  #
  ...  laneIdx:  1              5  4  3
  ...  laneIdx:  2              6  7  8
  -/
/-

-/
  #guard reprStr (
      [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map
        (fun val => (val, (DeadBorderCoord.mk 2).map_coord 3 val))
    )
    = "[(-5, some (p: 1, laneIdx: -2)),
 (-4, some (p: 2, laneIdx: -2)),
 (-3, some (p: 2, laneIdx: -1)),
 (-2, some (p: 1, laneIdx: -1)),
 (-1, some (p: 0, laneIdx: -1)),
 (0, some (p: 0, laneIdx: 0)),
 (1, some (p: 1, laneIdx: 0)),
 (2, some (p: 2, laneIdx: 0)),
 (3, some (p: 2, laneIdx: 1)),
 (4, some (p: 1, laneIdx: 1)),
 (5, some (p: 0, laneIdx: 1)),
 (6, some (p: 0, laneIdx: 2)),
 (7, some (p: 1, laneIdx: 2)),
 (8, some (p: 2, laneIdx: 2)),
 (9, none)]"



end DeadBorderCoord

def get_local_neighborhood (C: CellAutomaton α β) (c: Config C.Q) (i: ℤ) : C.Q × C.Q × C.Q :=
  (c (i - 1), c i, c (i + 1))

structure DeadBorder extends DeadBorderCoord where
  {α: Type}
  {β: Type}
  [inst: Alphabet α]
  C_orig: CellAutomaton α？ β

attribute [instance] DeadBorder.inst

namespace DeadBorder

  variable {e: DeadBorder}

  abbrev Cell := e.LaneIdx → e.C_orig.Q



  def Cell.get_z (q: e.Cell) (lane_idx: ℤ): e.C_orig.Q :=
    if h: e.is_valid_idx lane_idx
    then q ⟨lane_idx, h⟩
    else e.C_orig.border


  def get_local_neighborhood_on_folded (q_left: e.Cell？) (q_center: e.Cell) (q_right: e.Cell？) (lane_idx: e.LaneIdx) : e.C_orig.Q × e.C_orig.Q × e.C_orig.Q :=
    let is_even := lane_idx.val % 2 == 0
    let (l, r) := if is_even then (q_left, q_right) else (q_right, q_left)
    let a := l.getD (q_center.get_z $ · - 1) lane_idx
    let b := q_center lane_idx
    let c := r.getD (q_center.get_z $ · + 1) lane_idx
    (a, b, c)

  def C: CellAutomaton e.α？ e.β :=
    {
      Q := Option e.Cell
      δ := fun qL qC qR =>
        qC.map (
          fun qC' lane_idx =>
            let (a, b, c) := get_local_neighborhood_on_folded qL qC' qR lane_idx
            e.C_orig.δ a b c
        )

      embed
      | none => none
      | some a' => fun (lane_idx: e.LaneIdx) => e.C_orig.embed (if lane_idx.val = 0 then some a' else none)

      project
      | none => e.C_orig.project e.C_orig.border
      | some q => e.C_orig.project (Cell.get_z q 0)
    }


  def unfold (c: Config e.Cell？) (w_len: ℕ): Config e.C_orig.Q :=
    fun i =>
      match e.map_coord w_len i with
      | none => e.C_orig.border
      | some (p, lane_idx) => (c p).get! lane_idx

  lemma inv (w: Word e.α) (t: ℕ) (p: ℤ) (h: |p| < e.c * w.length - t):
      unfold (C.nextt w t) w.length p = e.C_orig.nextt w t p := by
    induction t generalizing p with
    | zero =>
      dsimp [nextt0]
      unfold unfold

      by_cases h: p ∈ w.range
      · rw [e.map_coord_p_lane_0 w.length p (by simp_all [Word.range])]
        simp [h, C, embed_word_at_eq]

      · have : e.C_orig.embed_word w p = e.C_orig.border := by
          simp [embed_word_at_eq, h, CellAutomaton.border]
        rw [this]
        split
        case h_1 => simp
        case h_2 h fp cell_p lane_idx eq =>

          have lane_idx_neq_0 : lane_idx.val ≠ 0 := by
            apply e.map_coord_p_range
            apply eq
            simp_all [Word.range]

          rw [embed_word_at_eq]
          have := e.map_coord_p_lane w.length p cell_p lane_idx eq
          simp [Word.range, this, C, lane_idx_neq_0, CellAutomaton.border]


    | succ t ih =>

      sorry



  lemma spec_comp_trace (w: Word e.α) (t: ℕ) (h: t < e.c * w.length): e.C.trace w t = e.C_orig.trace w t := by
    sorry


  lemma spec_left_border_dead: e.C.dead e.C.border := by
    sorry

end DeadBorder
end CellularAutomatas
