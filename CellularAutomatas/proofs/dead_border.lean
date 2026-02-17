import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.border
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

  -- map_coord returns some when |p| < e.c * len
  lemma map_coord_isSome_of_bound (w_len: ℕ) (p: ℤ)
    (h_len: w_len > 0) (h_bound: |p| < e.c * w_len):
    (e.map_coord w_len p).isSome := by
    unfold map_coord
    simp [Nat.pos_iff_ne_zero.mp h_len]
    -- Need to show: e.is_valid_idx (p / w_len)
    -- i.e., -e.c ≤ p / w_len ∧ p / w_len ≤ e.c
    simp only [is_valid_idx]
    simp only [abs_lt] at h_bound
    have w_len_pos : (w_len : ℤ) > 0 := by omega
    have w_len_ne : (w_len : ℤ) ≠ 0 := by omega
    constructor
    · -- -e.c ≤ p / w_len
      have key : -↑e.c * w_len ≤ p := by linarith
      have := Int.le_ediv_of_mul_le w_len_pos key
      linarith
    · -- p / w_len ≤ e.c
      have key : p < ↑e.c * w_len + w_len := by linarith
      have key2 : p < (↑e.c + 1) * w_len := by ring_nf; linarith
      -- p < (e.c + 1) * w_len implies p / w_len < e.c + 1 implies p / w_len ≤ e.c
      have := Int.ediv_lt_of_lt_mul w_len_pos key2
      omega


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
    simp
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

  lemma spec_initial_border: e.C.initial e.C.border := by
    intro a b c h
    simp only [CellAutomaton.border, C] at h ⊢
    cases b <;> simp_all

  lemma spec_inj_embed_none: e.C.inj_embed none := by
    intro q' h
    simp only [CellAutomaton.border, C] at h
    cases q' <;> simp_all

  -- Shape preservation: outside word range → none (border)
  lemma shape_outside (w: Word e.α) (t: ℕ) (p: ℤ) (h_p: p ∉ w.range):
      C.nextt (C.embed_word w) t p = C.border :=
    dead_border_prop C spec_left_border_dead w t p h_p

  -- Shape preservation: inside word range → not none (not border)
  lemma shape_inside (w: Word e.α) (t: ℕ) (p: ℤ) (h_p: p ∈ w.range):
      C.nextt (C.embed_word w) t p ≠ C.border :=
    initial_border_prop C spec_initial_border spec_inj_embed_none w t p h_p

  -- Combined: configuration after t steps has the word shape
  lemma shape_preserved (w: Word e.α) (t: ℕ):
      ∀ p: ℤ, (C.nextt (C.embed_word w) t p).isSome ↔ p ∈ w.range := by
    intro p
    constructor
    · intro h
      by_contra h_not_range
      have hout := shape_outside w t p h_not_range
      simp only [CellAutomaton.border, C] at hout h
      rw [hout] at h
      simp at h
    · intro h
      have hin := shape_inside w t p h
      simp only [CellAutomaton.border, C] at hin
      cases hval : C.nextt (C.embed_word w) t p
      · simp only [C] at hval
        exact absurd hval hin
      · simp


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
    simp only [unfold_neighborhood, neighborhood_at, unfold, h_prev]
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

    have h_geo_prev := e.map_coord_prev c.length p cell_p lane_idx h_len h1
    have h_geo_next := e.map_coord_next c.length p cell_p lane_idx h_len h1

    apply Prod.ext
    · -- Left component
      exact main_left c p cell_p lane_idx h_len h1 h_geo_prev
    · apply Prod.ext
      · -- Center component
        exact main_center c p cell_p lane_idx h1
      · -- Right component
        exact main_right c p cell_p lane_idx h_len h1 h_geo_next



  lemma inv (w: Word e.α) (t: ℕ) (p: ℤ) (h: |p| < e.c * w.length - t): unfold (C.nextt w t) w.length p = e.C_orig.nextt w t p := by
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
      · -- special case: when len = 0, the bound |p| < e.c * 0 - (t+1) = -(t+1) is impossible
        simp_all
        have : |p| ≥ 0 := abs_nonneg p
        omega

      rw [LCellAutomaton.nextt_succ_eq]
      rw [LCellAutomaton.nextt_succ_eq]

      rw [next_eq]

      have h_neigh_eq : neighborhood_at (e.C_orig.nextt w t) p =
            neighborhood_at (unfold (C.nextt w t) len) p := by
        -- Apply ih to p-1, p, p+1
        simp only [neighborhood_at]
        have h_abs : |p| < e.c * len - (t + 1) := h
        have h_bound_m1 : |p - 1| < e.c * len - t := by
          simp only [abs_lt] at h_abs ⊢
          omega
        have h_bound_p : |p| < e.c * len - t := by omega
        have h_bound_p1 : |p + 1| < e.c * len - t := by
          simp only [abs_lt] at h_abs ⊢
          omega
        rw [ih (p - 1) h_bound_m1, ih p h_bound_p, ih (p + 1) h_bound_p1]

      rw [h_neigh_eq]
      clear ih h_neigh_eq

      rw [←next_eq]

      set c := C.nextt ⦋w⦌ t

      rw [unfold]
      split
      case h_1 h_none =>
        -- Contradiction: |p| < e.c * len - (t+1) implies map_coord returns some
        have h_bound : |p| < e.c * len := by omega
        have h_len_pos : len > 0 := Nat.pos_of_ne_zero h_len_neq_0
        have := e.map_coord_isSome_of_bound len p h_len_pos h_bound
        simp [h_none] at this

      case h_2 fp cell_p lane_idx eq =>

        rw [CellAutomaton.next]
        dsimp [C]

        -- cell_p is in range 0..len, so c cell_p is some by shape preservation
        have h_cell_p_range : cell_p ∈ w.range := by
          have ⟨h1, h2⟩ := e.map_coord_p_lane len p cell_p lane_idx eq
          simp only [Word.range, ge_iff_le, Set.mem_setOf_eq]
          exact ⟨h1, h2⟩
        have h_isSome : (c cell_p).isSome := (shape_preserved w t cell_p).mpr h_cell_p_range
        cases h_c: (c cell_p)
        · simp [h_c] at h_isSome

        dsimp
        rw [←h_c]
        rw [←neighborhood_at]
        rw [next_eq]
        congr

        -- c has word shape, so it can be represented as word_to_config w'
        have h_word_exists : ∃ w': Word e.Cell, len = w'.length ∧ c = (@word_to_config e.Cell w') := by
          have h_shape : ∀ p: ℤ, (c p).isSome ↔ 0 ≤ p ∧ p < len := by
            intro q
            have := shape_preserved w t q
            simp only [Word.range, ge_iff_le, Set.mem_setOf_eq] at this
            exact this
          obtain ⟨w', hw'⟩ := to_word_exists_generic h_shape
          exact ⟨w', hw'.1.symm, hw'.2⟩

        obtain ⟨w', h_eq⟩ := h_word_exists
        rw [h_eq.1] at eq
        rw [h_eq.1]
        rw [h_eq.2]
        have := main w' p eq
        exact this


  -- Key observation 1: e.C.trace is e.C_orig.project of unfold at position 0
  lemma trace_eq_project_unfold (w: Word e.α) (t: ℕ) (h: w.length > 0):
      e.C.trace w t = e.C_orig.project (unfold (C.nextt ⦋w⦌ t) w.length 0) := by
    simp only [CellAutomaton.trace, CellAutomaton.comp, Function.comp_apply,
               CellAutomaton.project_config, embed_word_word_to_config_eq]
    -- Goal: C.project (C.nextt ⦋w⦌ t 0) = e.C_orig.project (unfold (C.nextt ⦋w⦌ t) w.length 0)

    -- unfold at 0: (c 0).get! ⟨0, _⟩
    simp only [unfold, e.map_coord_p_lane_0 w.length 0 ⟨le_refl 0, Nat.cast_pos.mpr h⟩]

    -- C.nextt w t 0 = some cell by shape preservation
    have h_range : (0 : ℤ) ∈ w.range := by simp [Word.range]; omega
    obtain ⟨cell, h_cell⟩ := Option.isSome_iff_exists.mp ((shape_preserved w t 0).mpr h_range)
    simp only [h_cell, Option.get!_some]

    -- C.project (some cell) = e.C_orig.project (cell ⟨0, _⟩)
    have h_valid : e.is_valid_idx 0 := by simp [is_valid_idx]
    simp only [C, Cell.get_z, h_valid, dite_true]

  -- Key observation 2 (from inv): unfold (C.nextt w t) w.length 0 = e.C_orig.nextt w t 0
  -- (This is just `inv w t 0` specialized)

  lemma spec_comp_trace (w: Word e.α) (t: ℕ) (h: t < e.c * w.length): e.C.trace w t = e.C_orig.trace w t := by
    have h_len_pos : w.length > 0 := by by_contra hz; simp_all

    -- e.C.trace w t = e.C_orig.project (unfold ... 0)
    rw [trace_eq_project_unfold w t h_len_pos]

    -- unfold ... 0 = e.C_orig.nextt w t 0 (by inv at p=0)
    have h_bnd : |(0 : ℤ)| < (e.c : ℤ) * w.length - t := by
      simp only [abs_zero]
      have : (t : ℤ) < (e.c : ℤ) * w.length := by exact_mod_cast h
      linarith
    rw [inv w t 0 h_bnd]

    -- e.C_orig.project (e.C_orig.nextt w t 0) = e.C_orig.trace w t
    simp only [CellAutomaton.trace, CellAutomaton.comp, Function.comp_apply,
               CellAutomaton.project_config, embed_word_word_to_config_eq]

end DeadBorder
end CellularAutomatas
