import CellularAutomatas.defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

notation:max x "³"  => Fin 3 → x

/-
  DiagLeft: A cellular automaton that propagates a "virtual fire" signal to the left.

  Key timing (for non-empty input):
  - Cell 0 reaches hold at t=4
  - Cell at position -k (k > 0) fires at t = 3 + 2*k
-/

inductive Q_DL
| idle
| p_s0 | p_s1 | p_s2 | p_fire | hold | v_fire | dead
deriving DecidableEq, Inhabited, Fintype

open Q_DL in
def diag_left {α β: Type} [Alphabet α] [Alphabet β] : CellAutomaton α？ ((β？)³)？ := {
  Q := Q_DL
  δ := fun _ c r =>
    match c with
    | p_s0 => p_s1
    | p_s1 => p_s2
    | p_s2 => p_fire
    | p_fire => hold
    | hold => dead
    | dead => dead
    | v_fire => hold
    | idle => if r == hold then v_fire else idle
  embed := fun
    | some _ => p_s0
    | none => idle
  project := fun
    | v_fire => some (fun _ => none)
    | _ => none
}

namespace DiagLeftSpec

variable {α β: Type} [Alphabet α] [Alphabet β]

-- The expected state at each (t, p) for a given word
def expected_state (w: Word α) (t: ℕ) (p: ℤ) : Q_DL :=
  if w = [] then Q_DL.idle
  else if p ≥ w.length then Q_DL.idle
  else if p ≥ 0 then
    -- Input cell: deterministic sequence
    match t with
    | 0 => Q_DL.p_s0
    | 1 => Q_DL.p_s1
    | 2 => Q_DL.p_s2
    | 3 => Q_DL.p_fire
    | 4 => Q_DL.hold
    | _ => Q_DL.dead
  else
    -- Negative cell: fires at t = 3 + 2*|p|
    let fire_time := 3 + 2 * p.natAbs
    if t < fire_time then Q_DL.idle
    else if t = fire_time then Q_DL.v_fire
    else if t = fire_time + 1 then Q_DL.hold
    else Q_DL.dead

-- The actual initial config
def init (w: Word α) : Config Q_DL :=
  fun p => if 0 ≤ p ∧ p < w.length then Q_DL.p_s0 else Q_DL.idle

-- Local notation for the CA
-- Key lemma: actual state matches expected state
-- This is the main inductive proof
lemma state_eq_expected (w: Word α) (t: ℕ) (p: ℤ) :
    (diag_left (α := α) (β := β)).nextt (init w) t p = expected_state w t p := by
  -- Induction on t
  induction t generalizing p with
  | zero =>
    -- Base case: t = 0, we just need init
    simp only [CellAutomaton.nextt_zero]
    unfold expected_state init
    by_cases hw : w = []
    · simp [hw]
    · by_cases hge : p ≥ w.length
      · simp [hw, hge, show ¬(0 ≤ p ∧ p < ↑w.length) by omega]
      · by_cases hp : p ≥ 0
        · simp [hw, hge, hp, show 0 ≤ p ∧ p < ↑w.length by omega]
        · simp [hw, hge, hp]
  | succ t ih =>
    -- Inductive step
    rw [CellAutomaton.nextt_succ]
    -- Use the IH for t at positions p-1, p, p+1
    have ih_l := ih (p - 1)
    have ih_c := ih p
    have ih_r := ih (p + 1)
    -- Now unfold and do case analysis
    unfold expected_state at ih_l ih_c ih_r ⊢
    unfold CellAutomaton.next diag_left
    simp only
    by_cases hw : w = []
    · -- w = []: stays idle
      simp only [hw, ↓reduceIte] at ih_l ih_c ih_r ⊢
      rw [ih_c, ih_r]
      decide
    · -- w ≠ []
      simp only [hw, ↓reduceIte] at ih_l ih_c ih_r ⊢
      by_cases hge : p ≥ w.length
      · -- p ≥ w.length: stays idle (right neighbor also idle)
        have hge_r : p + 1 ≥ w.length := by omega
        simp only [hge, hge_r, ↓reduceIte] at ih_c ih_r ⊢
        rw [ih_c, ih_r]
        decide
      · -- p < w.length
        simp only [hge, ↓reduceIte] at ih_c ih_r ⊢
        by_cases hp : p ≥ 0
        · -- 0 ≤ p < w.length: deterministic sequence
          simp only [hp, ↓reduceIte] at ih_c ⊢
          -- State transitions based on t
          match t with
          | 0 => simp [ih_c]
          | 1 => simp [ih_c]
          | 2 => simp [ih_c]
          | 3 => simp [ih_c]
          | _ + 4 => simp [ih_c]
        · -- p < 0: need to check hold propagation
          simp only [hp, ↓reduceIte] at ih_c ⊢
          push_neg at hp
          set fire_time := 3 + 2 * p.natAbs with ft
          set fire_time_r := 3 + 2 * (p + 1).natAbs with ft_r
          -- Right neighbor fire time
          have hp1_neg : p + 1 ≤ 0 := by omega
          -- Case on whether right is in input region
          by_cases hp1_ge0 : p + 1 ≥ 0
          · -- p = -1, so p + 1 = 0, right is in input region
            have hp_eq : p = -1 := by omega
            simp only [hp1_ge0, ↓reduceIte] at ih_r
            -- Right cell is at position 0, follows deterministic sequence
            by_cases hge_r : p + 1 ≥ w.length
            · simp [hge_r] at ih_r
              -- But w ≠ [] so w.length ≥ 1, but p + 1 = 0 so 0 ≥ w.length is false
              simp only [List.ne_nil_iff_length_pos] at hw
              omega
            · simp only [hge_r, ↓reduceIte] at ih_r
              -- Right cell follows: p_s0, p_s1, p_s2, p_fire, hold, dead
              -- For p = -1, fire_time = 3 + 2*1 = 5
              subst hp_eq
              simp only [Int.natAbs_neg, Int.natAbs_one] at ft ⊢
              -- At t+1 = 5, cell -1 should fire (right was hold at t=4)
              match t with
              | 0 => simp [ih_c, ih_r, Q_DL.idle]
              | 1 => simp [ih_c, ih_r, Q_DL.idle]
              | 2 => simp [ih_c, ih_r, Q_DL.idle]
              | 3 => simp [ih_c, ih_r, Q_DL.idle]
              | 4 => simp [ih_c, ih_r, Q_DL.v_fire, Q_DL.hold]
              | 5 => simp [ih_c, ih_r, Q_DL.hold]
              | _ + 6 => simp [ih_c, ih_r, Q_DL.dead]
          · -- p + 1 < 0, both cells in negative region
            push_neg at hp1_ge0
            by_cases hge_r : p + 1 ≥ w.length
            · omega  -- impossible since p + 1 < 0 < w.length
            · simp only [hp1_ge0, hge_r, ↓reduceIte] at ih_r
              -- Both cells use the fire_time formula
              -- Key: fire_time_r = 3 + 2*(|p| - 1) = fire_time - 2 (for p < -1)
              have hp_lt_neg1 : p < -1 := by omega
              have natAbs_rel : (p + 1).natAbs = p.natAbs - 1 := by
                have : p.natAbs ≥ 2 := by
                  simp only [Int.natAbs]
                  split <;> omega
                omega
              rw [natAbs_rel] at ft_r
              have ft_rel : fire_time_r = fire_time - 2 := by omega
              -- Case analysis on t vs fire_time
              by_cases ht_lt : t + 1 < fire_time
              · -- Too early: both idle
                have ht_lt_r : t < fire_time_r := by omega
                simp only [ht_lt, ht_lt_r, ↓reduceIte, reduceDIte] at ih_c ih_r ⊢
                have : ¬(Q_DL.idle == Q_DL.hold) := by decide
                simp [ih_c, this]
              · by_cases ht_eq : t + 1 = fire_time
                · -- Firing time: right was in hold at t
                  have ht_r_hold : t = fire_time_r + 1 := by omega
                  simp only [ht_eq, ↓reduceIte, reduceDIte] at ⊢
                  simp only [show ¬(t < fire_time_r) by omega, ↓reduceIte] at ih_r
                  simp only [show ¬(t = fire_time_r) by omega, ↓reduceIte] at ih_r
                  simp only [ht_r_hold, ↓reduceIte] at ih_r
                  simp only [show ¬(t < fire_time - 1) by omega, ↓reduceIte] at ih_c
                  simp only [show ¬(t = fire_time - 1) by omega, ↓reduceIte] at ih_c
                  simp only [show t = fire_time - 1 + 1 by omega, ↓reduceIte] at ih_c
                  -- ih_r says right is hold, ih_c says center is hold but we're looking at next step
                  -- Actually ih_c is for t, not t+1
                  have : Q_DL.hold == Q_DL.hold := by decide
                  simp [ih_r, this]
                · by_cases ht_hold : t + 1 = fire_time + 1
                  · -- Going to hold
                    simp only [ht_hold, ↓reduceIte, reduceDIte] at ⊢
                    simp only [show ¬(t < fire_time - 1) by omega, ↓reduceIte] at ih_c
                    simp only [show ¬(t = fire_time - 1) by omega, ↓reduceIte] at ih_c
                    simp only [show t = fire_time by omega, ↓reduceIte] at ih_c
                    simp [ih_c]
                  · -- Dead
                    simp only [show ¬(t + 1 < fire_time) by omega, ↓reduceIte] at ⊢
                    simp only [show ¬(t + 1 = fire_time) by omega, ↓reduceIte] at ⊢
                    simp only [show ¬(t + 1 = fire_time + 1) by omega, ↓reduceIte] at ⊢
                    simp only [show ¬(t < fire_time - 1) by omega, ↓reduceIte] at ih_c
                    simp only [show ¬(t = fire_time - 1) by omega, ↓reduceIte] at ih_c
                    simp only [show ¬(t = fire_time) by omega, ↓reduceIte] at ih_c
                    by_cases ht_was_hold : t = fire_time + 1
                    · simp [ht_was_hold] at ih_c
                      simp [ih_c]
                    · simp only [show ¬(t = fire_time + 1) by omega, ↓reduceIte] at ih_c
                      simp [ih_c]

-- Main theorem
lemma diag_left_spec (w: Word α) (t: ℕ) (p: ℤ):
    (diag_left (α := α) (β := β)).comp (CellAutomaton.embed_word w) t p =
      if w ≠ [] ∧ p < 0 ∧ t = 3 + 2 * p.natAbs
      then some (fun _ => none)
      else none := by
  unfold CellAutomaton.comp CellAutomaton.project_config
  simp only [Function.comp_apply]
  -- First show that embed_word matches init
  have h_init : CellAutomaton.embed_word (C := diag_left (α := α) (β := β)) w = init w := by
    funext p
    simp only [CellAutomaton.embed_word, CellAutomaton.embed_config, word_to_config, diag_left, init]
    split_ifs <;> rfl
  conv_lhs => rw [h_init]
  rw [state_eq_expected]
  -- Now we just need to show expected_state projects to the right value
  unfold expected_state diag_left
  -- Case analysis
  by_cases hw : w = []
  · simp [hw]
  · by_cases hge : p ≥ w.length
    · -- p ≥ w.length means p ≥ 0 (since w ≠ [] means w.length ≥ 1)
      have hp0 : p ≥ 0 := by simp only [List.ne_nil_iff_length_pos] at hw; omega
      simp [hw, hge, show ¬(p < 0) by omega]
    · by_cases hp : p ≥ 0
      · -- Input position: never v_fire
        simp only [hw, hge, hp, ↓reduceIte]
        simp [show ¬(w ≠ [] ∧ p < 0 ∧ t = 3 + 2 * p.natAbs) by omega]
        match t with
        | 0 | 1 | 2 | 3 | 4 | _ + 5 => rfl
      · -- Negative position
        simp only [hw, hge, hp, ↓reduceIte]
        push_neg at hw hge hp
        set fire_time := 3 + 2 * p.natAbs with ft
        by_cases ht1 : t < fire_time
        · simp [ht1, show t ≠ fire_time by omega]
        · by_cases ht2 : t = fire_time
          · simp [ht2, hw, hp]
          · by_cases ht3 : t = fire_time + 1
            · simp [ht3]
            · simp [ht1, ht2, ht3]

end DiagLeftSpec

-- Export the spec
lemma diag_left_spec {α β: Type} [Alphabet α] [Alphabet β] (w: Word α) (t: ℕ) (p: ℤ):
    (@diag_left α β _ _).comp (CellAutomaton.embed_word w) t p =
      if w ≠ [] ∧ p < 0 ∧ t = 3 + 2 * p.natAbs
      then some (fun _ => none)
      else none := DiagLeftSpec.diag_left_spec w t p

end CellularAutomatas
