import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.int_lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

namespace CellularAutomatas

  lemma dead_border_prop {α β : Type}
      (C: CellAutomaton (Option α) β) (h_dead: C.dead C.border)
      (w: Word α) (t: ℕ) (p: ℤ) (h_p: p ∉ w.range):
      C.nextt (C.embed_word w) t p = C.border := by
    induction t with
    | zero =>
      simp only [CellAutomaton.nextt_zero]
      rw [embed_word_at_eq2 (C:=C) w p h_p]
      rfl
    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next]
      apply h_dead
      exact ih

  lemma initial_border_prop {α β : Type}
      (C: CellAutomaton (Option α) β) (h_initial_border: C.initial C.border)
      (h: ∀ a, C.embed (some a) ≠ C.border)
      (w: Word α) (t: ℕ) (p: ℤ) (h_p: p ∈ w.range):
      C.nextt (C.embed_word w) t p ≠ C.border := by
      induction t with
      | zero =>
        simp only [CellAutomaton.nextt_zero]
        rw [embed_word_at_eq1 (C:=C) w p h_p]
        apply h
      | succ t ih =>
        rw [CellAutomaton.nextt_succ]
        intro h
        apply ih
        rw [CellAutomaton.next] at h
        apply h_initial_border _ _ _ h

  lemma to_word_exists_generic {α : Type} [Inhabited α] {c: Config (Option α)} {len: ℕ}
    (h: ∀ p, (c p).isSome ↔ 0 ≤ p ∧ p < len):
    ∃ w': Word α, w'.length = len ∧ c = word_to_config w' := by

    set l := (List.range len).map (fun (i: ℕ) => (c i).get!)
    exists l

    constructor
    · simp [l]
    · funext p
      simp only [word_to_config]
      have h_len_l : l.length = len := by simp [l]
      by_cases hp: 0 ≤ p ∧ p < len
      · have hp_l : 0 ≤ p ∧ p < l.length := by rw [h_len_l]; exact hp
        simp_all
        simp_all [l]
        have : (c p).isSome := by
          grind

        rw [←Option.get_eq_get! (h := by simp_all)]
        rw [Option.some_get]

      · have hp_l : ¬(0 ≤ p ∧ p < l.length) := by rw [h_len_l]; exact hp
        rw [dif_neg hp_l]
        match hc : c p with
        | some v =>
           have : (c p).isSome := by simp [hc]
           rw [h] at this
           contradiction
        | none => rfl

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



  lemma map_coord_iff (w_len: ℕ) (p: ℤ) (cp: ℤ) (li: e.LaneIdx)
    (h_pos: w_len > 0) :
    e.map_coord w_len p = some (cp, li) ↔
      (e.is_valid_idx (p / w_len) ∧
       li.val = p / w_len ∧
       cp = if li.val % 2 = 0 then p % w_len else w_len - 1 - p % w_len) := by
    rw [DeadBorderCoord.map_coord]
    have : (w_len : ℤ) ≠ 0 := by omega
    simp [this]
    split_ifs with h_valid
    · grind
    · grind
    grind
    grind

  lemma map_coord_prev (w_len: ℕ) (p: ℤ) (cp: ℤ) (li: e.LaneIdx)
    (h_pos: w_len > 0)
    (h1: e.map_coord w_len p = some (cp, li)) :
    e.map_coord w_len (p - 1) =
      if li.val % 2 = 0 then
        if cp > 0 then some (cp - 1, li)
        else if h: e.is_valid_idx (li.val - 1) then some (0, ⟨li.val - 1, h⟩) else none
      else
        if cp < w_len - 1 then some (cp + 1, li)
        else if h: e.is_valid_idx (li.val - 1) then some (w_len - 1, ⟨li.val - 1, h⟩) else none := by
    rw [map_coord_iff e _ _ _ _ h_pos] at h1
    obtain ⟨h_valid, h_li, h_cp⟩ := h1
    have w_len_pos : (w_len : ℤ) > 0 := by omega

    split_ifs with h_even h_cp_check h_valid_prev

    -- Case 1: Even lane, cp > 0. Same lane, cp decreases.
    · rw [map_coord_iff e _ _ _ _ h_pos]
      have : p % w_len > 0 := by
         rw [if_pos h_even] at h_cp
         subst h_cp
         exact h_cp_check
      constructor
      · rw [Int.ediv_sub_one_of_emod_pos w_len_pos (by assumption)]; exact h_valid
      constructor
      · rw [Int.ediv_sub_one_of_emod_pos w_len_pos (by assumption)]; rw [←h_li]
      · rw [if_pos h_even]
        rw [Int.emod_sub_one_of_emod_pos w_len_pos (by assumption)]
        rw [if_pos h_even] at h_cp
        subst h_cp
        simp

    -- Case 2: Even lane, cp <= 0.
    · -- cp must be 0
      rw [if_pos h_even] at h_cp
      have p_mod_0 : p % w_len = 0 := by
         have : 0 ≤ p % w_len := Int.emod_nonneg _ (by omega)
         omega
      subst h_cp

      -- Check if we have valid prev lane
      rw [map_coord_iff e _ _ _ _ h_pos]
      constructor
      · rw [Int.ediv_sub_one_of_emod_eq_zero w_len_pos p_mod_0]
        rw [←h_li]
        exact h_valid_prev
      constructor
      · rw [Int.ediv_sub_one_of_emod_eq_zero w_len_pos p_mod_0]
        rw [←h_li]
      · -- Lane became odd
        have h_odd : (li.val - 1) % 2 ≠ 0 := by omega
        rw [if_neg h_odd]
        rw [Int.emod_sub_one_of_emod_eq_zero w_len_pos p_mod_0]
        simp

    -- Case 3: Even lane, cp <= 0, but invalid prev lane
    · -- cp must be 0
      rw [if_pos h_even] at h_cp
      have p_mod_0 : p % w_len = 0 := by
         have : 0 ≤ p % w_len := Int.emod_nonneg _ (by omega)
         omega
      subst h_cp

      -- Result is none
      -- We must show map_coord is none.
      rw [map_coord]
      simp []
      rw [Int.ediv_sub_one_of_emod_eq_zero w_len_pos p_mod_0]
      rw [←h_li]
      simp [h_valid_prev]

    -- Case 4: Odd lane, cp < w_len - 1. Same lane, cp increases.
    · rw [map_coord_iff e _ _ _ _ h_pos]
      rw [if_neg h_even] at h_cp
      have p_mod_gt_0 : p % w_len > 0 := by
         have : p % w_len ≥ 0 := Int.emod_nonneg _ (by omega)
         omega

      constructor
      · rw [Int.ediv_sub_one_of_emod_pos w_len_pos p_mod_gt_0]; exact h_valid
      constructor
      · rw [Int.ediv_sub_one_of_emod_pos w_len_pos p_mod_gt_0]; rw [←h_li]
      · rw [if_neg h_even]
        rw [Int.emod_sub_one_of_emod_pos w_len_pos p_mod_gt_0]
        subst h_cp
        ring

    -- Case 5: Odd lane, cp >= w_len - 1.
    · rename_i h_valid_prev
      -- cp must be w_len - 1
      rw [if_neg h_even] at h_cp
      have p_mod_0 : p % w_len = 0 := by
         have : 0 ≤ p % w_len := Int.emod_nonneg _ (by omega)
         have : p % w_len < w_len := Int.emod_lt_of_pos _ w_len_pos
         omega
      subst h_cp

      -- Valid prev lane
      rw [map_coord_iff e _ _ _ _ h_pos]
      constructor
      · rw [Int.ediv_sub_one_of_emod_eq_zero w_len_pos p_mod_0]; rw [←h_li]; exact h_valid_prev
      constructor
      · rw [Int.ediv_sub_one_of_emod_eq_zero w_len_pos p_mod_0]; rw [←h_li]
      · -- Lane became even
        have h_odd : (li.val - 1) % 2 = 0 := by omega
        rw [if_pos h_odd]
        rw [Int.emod_sub_one_of_emod_eq_zero w_len_pos p_mod_0]


    -- Case 6: Odd lane, cp >= w_len - 1, invalid prev lane
    · rename_i h_valid_prev
      -- cp must be w_len - 1
      rw [if_neg h_even] at h_cp
      have p_mod_0 : p % w_len = 0 := by
         have : 0 ≤ p % w_len := Int.emod_nonneg _ (by omega)
         have : p % w_len < w_len := Int.emod_lt_of_pos _ w_len_pos
         omega

      rw [map_coord]
      simp []
      rw [Int.ediv_sub_one_of_emod_eq_zero w_len_pos p_mod_0]
      rw [←h_li]
      simp [h_valid_prev]

  lemma map_coord_next (w_len: ℕ) (p: ℤ) (cp: ℤ) (li: e.LaneIdx)
    (h_pos: w_len > 0)
    (h1: e.map_coord w_len p = some (cp, li)) :
    e.map_coord w_len (p + 1) =
      if li.val % 2 = 0 then
        if cp < w_len - 1 then some (cp + 1, li)
        else if h: e.is_valid_idx (li.val + 1) then some (w_len - 1, ⟨li.val + 1, h⟩) else none
      else
        if cp > 0 then some (cp - 1, li)
        else if h: e.is_valid_idx (li.val + 1) then some (0, ⟨li.val + 1, h⟩) else none := by
    rw [map_coord_iff e _ _ _ _ h_pos] at h1
    obtain ⟨h_valid, h_li, h_cp⟩ := h1
    have w_len_pos : (w_len : ℤ) > 0 := by omega

    split_ifs with h_even h_cp_check h_valid_next

    -- Case 1: Even lane, cp < w_len - 1.
    · rw [map_coord_iff e _ _ _ _ h_pos]
      rw [if_pos h_even] at h_cp
      have p_mod_lt : p % w_len < w_len - 1 := by
         omega
      subst h_cp

      constructor
      · rw [Int.ediv_add_one_of_emod_lt_sub_one w_len_pos p_mod_lt]; exact h_valid
      constructor
      · rw [Int.ediv_add_one_of_emod_lt_sub_one w_len_pos p_mod_lt]; rw [←h_li]
      · rw [if_pos h_even]
        rw [Int.emod_add_one_of_emod_lt_sub_one w_len_pos p_mod_lt]

    -- Case 2: Even lane, cp >= w_len - 1.
    · -- cp must be w_len - 1
      rw [if_pos h_even] at h_cp
      have p_mod_eq : p % w_len = w_len - 1 := by
         have : p % w_len < w_len := Int.emod_lt_of_pos _ w_len_pos
         omega
      subst h_cp

      -- Valid next lane
      rw [map_coord_iff e _ _ _ _ h_pos]
      constructor
      · rw [Int.ediv_add_one_of_emod_eq_sub_one w_len_pos p_mod_eq]
        rw [←h_li]
        exact h_valid_next
      constructor
      · rw [Int.ediv_add_one_of_emod_eq_sub_one w_len_pos p_mod_eq]
        rw [←h_li]
      · -- Lane became odd
        have h_odd : (li.val + 1) % 2 ≠ 0 := by omega
        rw [if_neg h_odd]
        rw [Int.emod_add_one_of_emod_eq_sub_one p_mod_eq]
        simp

    -- Case 3: Even lane, cp >= w_len - 1, invalid next lane
    · -- cp must be w_len - 1
      rw [if_pos h_even] at h_cp
      have p_mod_eq : p % w_len = w_len - 1 := by
         have : p % w_len < w_len := Int.emod_lt_of_pos _ w_len_pos
         omega
      subst h_cp

      rw [map_coord]
      simp
      rw [Int.ediv_add_one_of_emod_eq_sub_one w_len_pos p_mod_eq]
      rw [←h_li]
      simp [h_valid_next]

    -- Case 4: Odd lane, cp > 0.
    · rw [map_coord_iff e _ _ _ _ h_pos]
      rw [if_neg h_even] at h_cp
      have p_mod_lt : p % w_len < w_len - 1 := by
         have : p % w_len < w_len := Int.emod_lt_of_pos _ w_len_pos
         omega

      constructor
      · rw [Int.ediv_add_one_of_emod_lt_sub_one w_len_pos p_mod_lt]; exact h_valid
      constructor
      · rw [Int.ediv_add_one_of_emod_lt_sub_one w_len_pos p_mod_lt]; rw [←h_li]
      · rw [if_neg h_even]
        rw [Int.emod_add_one_of_emod_lt_sub_one w_len_pos p_mod_lt]
        subst h_cp
        ring

    -- Case 5: Odd lane, cp <= 0.
    · rename_i h_valid_next
      -- cp must be 0
      rw [if_neg h_even] at h_cp
      have p_mod_eq : p % w_len = w_len - 1 := by
         have : p % w_len < w_len := Int.emod_lt_of_pos _ w_len_pos
         have : 0 ≤ p % w_len := Int.emod_nonneg _ (by omega)
         omega
      subst h_cp

      -- Valid next lane
      rw [map_coord_iff e _ _ _ _ h_pos]
      constructor
      · rw [Int.ediv_add_one_of_emod_eq_sub_one w_len_pos p_mod_eq]; rw [←h_li]; exact h_valid_next
      constructor
      · rw [Int.ediv_add_one_of_emod_eq_sub_one w_len_pos p_mod_eq]; rw [←h_li]
      · -- Lane became even
        have h_odd : (li.val + 1) % 2 = 0 := by omega
        rw [if_pos h_odd]
        rw [Int.emod_add_one_of_emod_eq_sub_one p_mod_eq]

    -- Case 6: Odd lane, cp <= 0, invalid next lane
    · rename_i h_valid_next
      -- cp must be 0
      rw [if_neg h_even] at h_cp
      have p_mod_eq : p % w_len = w_len - 1 := by
         have : p % w_len < w_len := Int.emod_lt_of_pos _ w_len_pos
         have : 0 ≤ p % w_len := Int.emod_nonneg _ (by omega)
         omega

      rw [map_coord]
      simp
      rw [Int.ediv_add_one_of_emod_eq_sub_one w_len_pos p_mod_eq]
      rw [←h_li]
      simp [h_valid_next]

end DeadBorderCoord

def Neighborhood (α: Type) := α × α × α
def Neighborhood.left {α : Type} (n : Neighborhood α) : α := n.1
def Neighborhood.center {α : Type} (n : Neighborhood α) : α := n.2.1
def Neighborhood.right {α : Type} (n : Neighborhood α) : α := n.2.2

def neighborhood_at (c: Config α) (p: ℤ) : Neighborhood α :=
  (c (p - 1), c p, c (p + 1))

def CellAutomaton.δn (C: CellAutomaton α β) (n: Neighborhood C.Q) : C.Q :=
  let (a, b, c) := n
  C.δ a b c

lemma next_eq (C: CellAutomaton α β) (c: Config C.Q) (p: ℤ):
    C.next c p = C.δn (neighborhood_at c p) := by
  simp [neighborhood_at, CellAutomaton.δn, CellAutomaton.next]

structure DeadBorder extends DeadBorderCoord where
  {α: Type}
  {β: Type}
  [inst: Alphabet α]
  C_orig: CellAutomaton α？ β

attribute [instance] DeadBorder.inst

namespace DeadBorder

  open DeadBorderCoord

  variable {e: DeadBorder}

  abbrev Cell := e.LaneIdx → e.C_orig.Q



  def Cell.get_z (q: e.Cell) (lane_idx: ℤ): e.C_orig.Q :=
    if h: e.is_valid_idx lane_idx
    then q ⟨lane_idx, h⟩
    else e.C_orig.border


  def unfold_neighborhood (n: Neighborhood e.Cell？) (lane_idx: e.LaneIdx) : e.C_orig.Q × e.C_orig.Q × e.C_orig.Q :=
    let (q_left, q_center, q_right) := n
    let is_even := lane_idx.val % 2 == 0
    let (l, r) := if is_even then (q_left, q_right) else (q_right, q_left)
    let q_center' := q_center.getD (fun _ => e.C_orig.border)
    let a := l.getD (q_center'.get_z $ · - 1) lane_idx
    let b := q_center' lane_idx
    let c := r.getD (q_center'.get_z $ · + 1) lane_idx
    (a, b, c)

  def C: CellAutomaton e.α？ e.β :=
    {
      Q := Option e.Cell
      δ
      | _, none, _ => none
      | qL, qC, qR => fun lane_idx => e.C_orig.δn (unfold_neighborhood (qL, qC, qR) lane_idx)


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



  lemma spec_left_border_dead: e.C.dead e.C.border := by
    dsimp [CellAutomaton.dead, CellAutomaton.dead]
    intro a b c h
    subst h
    rfl


  lemma main_center (c: Word e.Cell) (p: ℤ) (cell_p: ℤ) (lane_idx: e.LaneIdx)
    (h1: e.map_coord c.length p = some (cell_p, lane_idx)):
      (unfold_neighborhood (neighborhood_at ⟬c⟭ cell_p) lane_idx).2.1
        = (unfold ⟬c⟭ c.length p) := by
    dsimp [unfold_neighborhood, neighborhood_at, unfold]
    rw [h1]
    dsimp
    have h_len : c.length > 0 := by
       apply Nat.pos_of_ne_zero; intro h; rw [h] at h1; simp [DeadBorderCoord.map_coord] at h1
    have h_map_iff := e.map_coord_iff c.length p cell_p lane_idx h_len
    obtain ⟨h_valid, h_lane_eq, h_cp_eq⟩ := h_map_iff.mp h1
    have range_ok : 0 ≤ cell_p ∧ cell_p < c.length := by
        simp [h_cp_eq]
        split_ifs
        · apply And.intro (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ (by omega))
        · apply And.intro
          · have := Int.emod_lt_of_pos p (by omega : (c.length : ℤ) > 0)
            omega
          · have := Int.emod_nonneg p (by omega : (c.length : ℤ) ≠ 0)
            omega
    simp [word_to_config, range_ok]

  lemma main_left (c: Word e.Cell) (p: ℤ) (cell_p: ℤ) (lane_idx: e.LaneIdx)
    (h_pos: c.length > 0)
    (h_map: e.map_coord c.length p = some (cell_p, lane_idx))
    (h_prev: e.map_coord c.length (p - 1) =
      if lane_idx.val % 2 = 0 then
        if cell_p > 0 then some (cell_p - 1, lane_idx)
        else if h: e.is_valid_idx (lane_idx.val - 1) then some (0, ⟨lane_idx.val - 1, h⟩) else none
      else
        if cell_p < c.length - 1 then some (cell_p + 1, lane_idx)
        else if h: e.is_valid_idx (lane_idx.val - 1) then some (c.length - 1, ⟨lane_idx.val - 1, h⟩) else none
    ):
    (unfold_neighborhood (neighborhood_at ⟬c⟭ cell_p) lane_idx).1 = unfold ⟬c⟭ c.length (p - 1) := by
    dsimp [unfold_neighborhood, neighborhood_at, unfold]
    rw [h_prev]

    have range_ok : 0 ≤ cell_p ∧ cell_p < c.length :=
      DeadBorderCoord.map_coord_p_lane e.toDeadBorderCoord c.length p cell_p lane_idx h_map

    split_ifs <;>
    try simp [*] at * <;>
    try simp [Cell.get_z, word_to_config, *] <;>
    try split_ifs <;>
    try simp [*] at * <;>
    try omega
    grind
    grind
    grind

  lemma main_right (c: Word e.Cell) (p: ℤ) (cell_p: ℤ) (lane_idx: e.LaneIdx)
    (h_pos: c.length > 0)
    (h_map: e.map_coord c.length p = some (cell_p, lane_idx))
    (h_next: e.map_coord c.length (p + 1) =
      if lane_idx.val % 2 = 0 then
        if cell_p < c.length - 1 then some (cell_p + 1, lane_idx)
        else if h: e.is_valid_idx (lane_idx.val + 1) then some (c.length - 1, ⟨lane_idx.val + 1, h⟩) else none
      else
        if cell_p > 0 then some (cell_p - 1, lane_idx)
        else if h: e.is_valid_idx (lane_idx.val + 1) then some (0, ⟨lane_idx.val + 1, h⟩) else none
    ):
    (unfold_neighborhood (neighborhood_at ⟬c⟭ cell_p) lane_idx).2.2 = unfold ⟬c⟭ c.length (p + 1) := by
    dsimp [unfold_neighborhood, neighborhood_at, unfold]
    rw [h_next]

    have range_ok : 0 ≤ cell_p ∧ cell_p < c.length :=
      DeadBorderCoord.map_coord_p_lane e.toDeadBorderCoord c.length p cell_p lane_idx h_map

    split_ifs <;>
    try simp [*] at * <;>
    try simp [Cell.get_z, word_to_config, *] <;>
    try split_ifs <;>
    try simp [*] at * <;>
    try omega

    grind
    grind
    grind

  lemma main (c: Word e.Cell) (p: ℤ)
    (h1: e.map_coord c.length p = some (cell_p, lane_idx)):
      unfold_neighborhood (neighborhood_at ⟬c⟭ cell_p) lane_idx
        = neighborhood_at (unfold ⟬c⟭ c.length) p := by

    have h_len : c.length > 0 := by
       apply Nat.pos_of_ne_zero; intro h; rw [h] at h1; simp [DeadBorderCoord.map_coord] at h1

    have h_geo_prev : e.map_coord c.length (p - 1) =
      if lane_idx.val % 2 = 0 then
        if cell_p > 0 then some (cell_p - 1, lane_idx)
        else if h: e.is_valid_idx (lane_idx.val - 1) then some (0, ⟨lane_idx.val - 1, h⟩) else none
      else
        if cell_p < c.length - 1 then some (cell_p + 1, lane_idx)
        else if h: e.is_valid_idx (lane_idx.val - 1) then some (c.length - 1, ⟨lane_idx.val - 1, h⟩) else none := by
        exact e.map_coord_prev c.length p cell_p lane_idx h_len h1

    have h_geo_next : e.map_coord c.length (p + 1) =
      if lane_idx.val % 2 = 0 then
        if cell_p < c.length - 1 then some (cell_p + 1, lane_idx)
        else if h: e.is_valid_idx (lane_idx.val + 1) then some (c.length - 1, ⟨lane_idx.val + 1, h⟩) else none
      else
        if cell_p > 0 then some (cell_p - 1, lane_idx)
        else if h: e.is_valid_idx (lane_idx.val + 1) then some (0, ⟨lane_idx.val + 1, h⟩) else none := by
        exact e.map_coord_next c.length p cell_p lane_idx h_len h1

    apply Prod.ext
    · -- Left component
      exact main_left c p cell_p lane_idx h_len h1 h_geo_prev
    · apply Prod.ext
      · -- Center component
        exact main_center c p cell_p lane_idx h1
      · -- Right component
        exact main_right c p cell_p lane_idx h_len h1 h_geo_next



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

      set len := w.length
      by_cases h_len_neq_0: len = 0
      · sorry -- special case

      rw [LCellAutomaton.nextt_succ_eq]
      rw [LCellAutomaton.nextt_succ_eq]

      rw [next_eq]

      have : neighborhood_at (e.C_orig.nextt w t) p =
            neighborhood_at (unfold (C.nextt w t) len) p := by
        sorry -- by ih

      rw [this]
      clear ih this

      rw [←next_eq]

      set c := C.nextt ⦋w⦌ t

      rw [unfold]
      split
      case h_1 => sorry -- by contradiction

      case h_2 fp cell_p lane_idx eq =>



        rw [CellAutomaton.next]
        dsimp [C]

        have : (c cell_p).isSome := by sorry
        cases h_c: (c cell_p)
        · sorry -- contradiction

        dsimp
        rw [←h_c]
        rw [←neighborhood_at]
        rw [next_eq]
        congr

        have : ∃ w: Word e.Cell, len = w.length ∧ c = (@word_to_config e.Cell w) := by
          sorry

        obtain ⟨w', this⟩ := this
        rw [this.1] at eq
        rw [this.1]
        rw [this.2]
        have := main w' p eq
        exact this


  lemma spec_comp_trace (w: Word e.α) (t: ℕ) (h: t < e.c * w.length): e.C.trace w t = e.C_orig.trace w t := by
    sorry -- follows from inv


end DeadBorder
end CellularAutomatas
