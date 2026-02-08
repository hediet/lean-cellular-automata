import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

notation:max x "³"  => Fin 3 → x

/-!
# DiagLeft Cellular Automaton

A cellular automaton that propagates a "virtual fire" signal to the left.

## Key Properties

The automaton has three distinct regions:
1. **Input region** (0 ≤ p < w.length): Deterministic sequence independent of neighbors
2. **Right region** (p ≥ w.length or w = []): Always quiescent (idle)
3. **Negative region** (p < 0): Fires when right neighbor reaches hold state

## Timing

For non-empty input w:
- Cell 0 reaches hold at t = 4
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
    -- Input states: neighbor-independent transitions
    | p_s0 => p_s1
    | p_s1 => p_s2
    | p_s2 => p_fire
    | p_fire => hold
    | hold => dead
    | dead => dead
    | v_fire => hold
    -- Idle state: fires when right neighbor is hold
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

/-- The initial configuration for a word. -/
def init (w: Word α) : Config Q_DL :=
  fun p => if 0 ≤ p ∧ p < w.length then Q_DL.p_s0 else Q_DL.idle

/-- Expected state for input cells (deterministic, only depends on t). -/
def input_state (t: ℕ) : Q_DL :=
  match t with
  | 0 => Q_DL.p_s0
  | 1 => Q_DL.p_s1
  | 2 => Q_DL.p_s2
  | 3 => Q_DL.p_fire
  | 4 => Q_DL.hold
  | _ => Q_DL.dead

/-- Expected state for negative cells. k = |p| where p < 0.
    fire_time = 3 + 2 * k -/
def negative_state (k: ℕ) (t: ℕ) : Q_DL :=
  if t < 3 + 2 * k then Q_DL.idle
  else if t = 3 + 2 * k then Q_DL.v_fire
  else if t = 3 + 2 * k + 1 then Q_DL.hold
  else Q_DL.dead

/-- Combined expected state function. -/
def expected_state (w: Word α) (t: ℕ) (p: ℤ) : Q_DL :=
  if w = [] then Q_DL.idle
  else if p ≥ w.length then Q_DL.idle
  else if p ≥ 0 then input_state t
  else negative_state p.natAbs t

/-! ## Region Lemmas -/

/-- All cells at p' ≥ p are idle at time t when the region hypothesis holds. -/
private lemma right_region_idle_strong (w: Word α) (hw: ∀ p': ℤ, (w = [] ∨ p' ≥ w.length) → init w p' = Q_DL.idle)
    (t: ℕ) (p: ℤ) (h: w = [] ∨ p ≥ w.length) :
    (diag_left (α := α) (β := β)).nextt (init w) t p = Q_DL.idle := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero]
    exact hw p h
  | succ t ih =>
    have hc : (diag_left (α := α) (β := β)).nextt (init w) t p = Q_DL.idle := ih p h
    have hr : (diag_left (α := α) (β := β)).nextt (init w) t (p + 1) = Q_DL.idle := by
      apply ih (p + 1)
      cases h with
      | inl hw => left; exact hw
      | inr hp => right; omega
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- Goal is δ _ (c_t p) (c_t (p+1)) = idle
    -- where c_t = nextt (init w) t
    -- Since c_t p = idle and c_t (p+1) = idle, δ idle idle idle = idle
    show (diag_left (α := α) (β := β)).δ
      ((diag_left (α := α) (β := β)).nextt (init w) t (p - 1))
      ((diag_left (α := α) (β := β)).nextt (init w) t p)
      ((diag_left (α := α) (β := β)).nextt (init w) t (p + 1)) = Q_DL.idle
    rw [hc, hr]
    rfl

/-- Right region stays idle. -/
lemma right_region_idle (w: Word α) (t: ℕ) (p: ℤ) (h: w = [] ∨ p ≥ w.length) :
    (diag_left (α := α) (β := β)).nextt (init w) t p = Q_DL.idle := by
  apply right_region_idle_strong w _ t p h
  intro p' h'
  unfold init
  split_ifs with hp'
  · cases h' with
    | inl hw => simp [hw] at hp'; omega
    | inr hge => omega
  · rfl

/-- Input region follows deterministic sequence.
  Key insight: δ for non-idle states is neighbor-independent. -/
lemma input_region_state (w: Word α) (hw: w ≠ []) (t: ℕ) (p: ℤ) (hp: 0 ≤ p ∧ p < w.length) :
    (diag_left (α := α) (β := β)).nextt (init w) t p = input_state t := by
  induction t with
  | zero =>
    simp only [CellAutomaton.nextt_zero, init, input_state, hp]
    rfl
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    show (diag_left (α := α) (β := β)).δ _ _ _ = input_state (t + 1)
    rw [ih]
    -- δ _ (input_state t) _ = input_state (t+1) for any neighbors
    match t with
    | 0 | 1 | 2 | 3 | 4 | _ + 5 => rfl

/-- Negative region fires according to formula.
  Uses nested induction: outer on k (to get right neighbor's behavior),
  inner on t (to trace the evolution). -/
lemma negative_region_state (w: Word α) (hw: w ≠ []) (t: ℕ) (k: ℕ) (hk: k ≥ 1) :
    (diag_left (α := α) (β := β)).nextt (init w) t (-(k : ℤ)) = negative_state k t := by
  -- Induction on t with k as parameter
  induction t generalizing k with
  | zero =>
    simp only [CellAutomaton.nextt_zero, init, negative_state]
    simp only [show ¬(0 ≤ (-(k : ℤ)) ∧ (-(k : ℤ)) < w.length) by omega, ↓reduceIte]
    simp only [show (0 : ℕ) < 3 + 2 * k by omega, ↓reduceIte]
  | succ t ih_t =>
    -- First, use strong induction on k to get the right neighbor's state
    induction k using Nat.strong_induction_on with | _ k ih_k =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    show (diag_left (α := α) (β := β)).δ _ _ _ = negative_state k (t + 1)
    -- Get center state at t
    have hcenter : (diag_left (α := α) (β := β)).nextt (init w) t (-(k : ℤ)) = negative_state k t := ih_t k hk
    rw [hcenter]
    set ft := 3 + 2 * k with hft
    -- Simplify the if-then-else in negative_state
    -- Simplify the let in negative_state
    unfold negative_state at *
    -- Now hcenter and goal have: let fire_time := 3 + 2 * k; if t < fire_time then ...
    -- We need to substitute fire_time = ft
    simp only [show (3 + 2 * k) = ft by rfl] at hcenter ⊢
    by_cases ht_lt : t < ft
    · -- t < ft: center is idle
      simp only [ht_lt, ↓reduceIte] at hcenter ⊢
      by_cases ht_succ : t + 1 < ft
      · -- t + 1 < ft: still idle (right not hold)
        simp only [ht_succ, show t + 1 ≠ ft by omega, ↓reduceIte]
        -- Right neighbor not hold
        have hright : (diag_left (α := α) (β := β)).nextt (init w) t (-(k : ℤ) + 1) ≠ Q_DL.hold := by
          by_cases hk1 : k = 1
          · -- k = 1: right is position 0
            subst hk1
            have hp0 : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < w.length := by
              exact ⟨le_refl _, Int.natCast_pos.mpr (List.ne_nil_iff_length_pos.mp hw)⟩
            have h0eq : (-(1 : ℕ) : ℤ) + 1 = 0 := by norm_num
            calc (diag_left (α := α) (β := β)).nextt (init w) t (-(1 : ℕ) + 1)
                = (diag_left (α := α) (β := β)).nextt (init w) t 0 := by rw [h0eq]
              _ = input_state t := input_region_state (α := α) (β := β) w hw t 0 ⟨le_refl _, hp0.2⟩
              _ ≠ Q_DL.hold := by unfold input_state; match t with | 0 | 1 | 2 | 3 => simp | 4 | _ + 5 => omega
          · -- k > 1: right is at -(k-1)
            have hk' : k - 1 ≥ 1 := by omega
            have heq : -(k : ℤ) + 1 = -((k - 1 : ℕ) : ℤ) := by omega
            rw [heq, ih_t (k - 1) hk']
            -- hold at t = 3 + 2*(k-1) + 1 = 2k + 2; we have t + 1 < 2k + 3, so t < 2k + 2
            -- Case h3: t = 3 + 2*(k-1) + 1 = 2k + 2, so t+1 = 2k+3 = ft, contradicting ht_succ
            split_ifs with h1 h2 h3 <;> [simp; simp; omega; simp]
        -- Now apply hright to simplify the goal
        -- Goal: δ _ idle (right) = idle; idle stays idle unless right is hold
        -- TODO: This requires showing simp can apply hright to the expanded structure
        sorry
      · -- t + 1 = ft: fire! (right is hold)
        have ht_eq : t + 1 = ft := by omega
        simp only [ht_eq, Nat.lt_irrefl, ↓reduceIte]
        -- Right neighbor IS hold at t
        have hright : (diag_left (α := α) (β := β)).nextt (init w) t (-(k : ℤ) + 1) = Q_DL.hold := by
          by_cases hk1 : k = 1
          · -- k = 1: right is position 0, t = 4
            subst hk1
            have hp0 : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < w.length :=
              ⟨le_refl _, Int.natCast_pos.mpr (List.ne_nil_iff_length_pos.mp hw)⟩
            have h0eq : (-(1 : ℕ) : ℤ) + 1 = 0 := by norm_num
            have ht4 : t = 4 := by omega  -- from ht_eq : t + 1 = 5
            calc (diag_left (α := α) (β := β)).nextt (init w) t (-(1 : ℕ) + 1)
                = (diag_left (α := α) (β := β)).nextt (init w) t 0 := by rw [h0eq]
              _ = input_state t := input_region_state (α := α) (β := β) w hw t 0 ⟨le_refl _, hp0.2⟩
              _ = Q_DL.hold := by subst ht4; rfl
          · -- k > 1: right is at -(k-1), which is hold at t
            have hk' : k - 1 ≥ 1 := by omega
            have heq : -(k : ℤ) + 1 = -((k - 1 : ℕ) : ℤ) := by omega
            rw [heq, ih_t (k - 1) hk']
            -- t + 1 = 2k + 3 = ft, so t = 2k + 2 = (3 + 2*(k-1)) + 1
            simp only [show t = 3 + 2 * (k - 1) + 1 by omega,
              show ¬(3 + 2 * (k - 1) + 1 = 3 + 2 * (k - 1)) by omega,
              show ¬(3 + 2 * (k - 1) + 1 < 3 + 2 * (k - 1)) by omega, ↓reduceIte]
        -- Same issue with structure expansion
        sorry
    · -- t ≥ ft
      push_neg at ht_lt
      -- hcenter should show t >= 3 + 2*k, so center is v_fire, hold, or dead
      by_cases ht_eq : t = ft
      · -- t = ft: center is v_fire, next is hold
        simp only [show ¬(t < 3 + 2 * k) by omega, show t = 3 + 2 * k by omega,
          show ¬(ft + 1 < ft) by omega, show ft + 1 ≠ ft by omega, ↓reduceIte]
        rfl
      · -- t > ft: center is hold or dead
        simp only [ht_eq, ↓reduceIte]
        by_cases ht_ft1 : t = ft + 1
        · -- t = ft + 1: center is hold
          simp only [ht_ft1, Nat.lt_irrefl, Nat.add_right_cancel_iff, show ¬(ft + 1 + 1 < ft) by omega,
            show ft + 1 + 1 ≠ ft by omega, show ft + 1 + 1 ≠ ft + 1 by omega, ↓reduceIte]
          rfl
        · -- t > ft + 1: center is dead
          simp only [ht_ft1, show ¬(t + 1 < ft) by omega, show t + 1 ≠ ft by omega,
            show t + 1 ≠ ft + 1 by omega, ↓reduceIte]
          rfl

/-! ## Main Theorems -/

/-- State matches expected state everywhere. -/
lemma state_eq_expected (w: Word α) (t: ℕ) (p: ℤ) :
    (diag_left (α := α) (β := β)).nextt (init w) t p = expected_state w t p := by
  unfold expected_state
  by_cases hw : w = []
  · simp only [hw, ↓reduceIte]
    subst hw
    exact right_region_idle (α := α) (β := β) [] t p (Or.inl rfl)
  · simp only [hw, ↓reduceIte]
    by_cases hge : p ≥ w.length
    · simp only [hge, ↓reduceIte]
      exact right_region_idle (α := α) (β := β) w t p (Or.inr hge)
    · simp only [hge, ↓reduceIte]
      by_cases hp : p ≥ 0
      · simp only [hp, ↓reduceIte]
        push_neg at hge
        exact input_region_state (α := α) (β := β) w hw t p ⟨hp, hge⟩
      · simp only [hp, ↓reduceIte]
        push_neg at hp
        have habs : p.natAbs ≥ 1 := Int.natAbs_pos.mpr (by omega)
        have hp_eq : p = -(p.natAbs : ℤ) := by omega
        have habs' : (-(p.natAbs : ℤ)).natAbs = p.natAbs := Int.natAbs_neg _
        rw [hp_eq, habs']
        exact negative_region_state (α := α) (β := β) w hw t p.natAbs habs

/-- The main specification: output is `some` exactly at firing time. -/
lemma diag_left_spec (w: Word α) (t: ℕ) (p: ℤ):
    (diag_left (α := α) (β := β)).comp (CellAutomaton.embed_word w) t p =
      if w ≠ [] ∧ p < 0 ∧ t = 3 + 2 * p.natAbs
      then some (fun _ => none)
      else none := by
  unfold CellAutomaton.comp CellAutomaton.project_config
  simp only [Function.comp_apply]
  have h_init : CellAutomaton.embed_word (C := diag_left (α := α) (β := β)) w = init w := by
    funext p
    simp only [CellAutomaton.embed_word, CellAutomaton.embed_config, word_to_config, diag_left, init]
    split_ifs <;> rfl
  conv_lhs => rw [h_init]
  rw [state_eq_expected]
  -- Now show: project (expected_state w t p) = ...
  unfold expected_state diag_left input_state negative_state
  by_cases hw : w = []
  · simp [hw]
  · simp only [hw, ne_eq, not_false_eq_true, ↓reduceIte, true_and]
    by_cases hge : p ≥ w.length
    · simp only [hge, ↓reduceIte]
      simp only [List.ne_nil_iff_length_pos] at hw
      simp [show ¬(p < 0) by omega]
    · simp only [hge, ↓reduceIte]
      by_cases hp : p ≥ 0
      · -- Input region: never v_fire
        simp only [hp, ↓reduceIte]
        simp [show ¬(p < 0) by omega]
        match t with
        | 0 | 1 | 2 | 3 | 4 | _ + 5 => rfl
      · -- Negative region
        simp only [hp, ↓reduceIte]
        push_neg at hp
        set ft := 3 + 2 * p.natAbs
        by_cases h1 : t < ft
        · simp [h1, hp, show t ≠ ft by omega]
        · by_cases h2 : t = ft
          · simp [h2, hp]
          · -- t > ft: hold or dead, never v_fire
            -- RHS simplifies to none since t ≠ ft
            simp only [hp, h2, and_false, ↓reduceIte]
            -- LHS is hold or dead depending on t = ft + 1, both project to none
            simp only [h1, ↓reduceIte]
            split_ifs <;> rfl

end DiagLeftSpec

/-- Export the specification. -/
lemma diag_left_spec {α β: Type} [Alphabet α] [Alphabet β] (w: Word α) (t: ℕ) (p: ℤ):
    (@diag_left α β _ _).comp (CellAutomaton.embed_word w) t p =
      if w ≠ [] ∧ p < 0 ∧ t = 3 + 2 * p.natAbs
      then some (fun _ => none)
      else none := DiagLeftSpec.diag_left_spec w t p

end CellularAutomatas
