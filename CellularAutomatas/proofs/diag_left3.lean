import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import Mathlib.Tactic.Linarith

namespace CellularAutomatas

open CellAutomaton

/-!
# Diagonal Left Cellular Automata

This file defines:
1. `DiagLeft` - A CA that fires at t = 2*|p| for p ≤ 0 (fires immediately at p=0, t=0)
2. `ConstDelay` - A general construction to delay any CA's output by k steps
3. `DiagLeft3` - DiagLeft delayed by 3 steps, firing at t = 3 + 2*|p|
-/

section DiagLeft

  /-
    DiagLeft: Fires at p ≤ 0 at time t = 2*|p|

    Execution for a single input cell at position 0:

    Time   Space (x)
    (t)    -5 -4 -3 -2 -1  0  1
    ---------------------------
     t=0    .  .  .  .  .  V  .   <-- Cell 0 fires immediately
     t=1    .  .  .  .  .  H  .   <-- Cell 0 in Hold
     t=2    .  .  .  .  V  x  .   <-- Cell -1 sees Hold, fires
     t=3    .  .  .  .  H  x  .
     t=4    .  .  .  V  x  x  .   <-- Cell -2 fires
     t=5    .  .  .  H  x  x  .
     t=6    .  .  V  x  x  x  .   <-- Cell -3 fires
     t=7    .  .  H  x  x  x  .
     t=8    .  V  x  x  x  x  .   <-- Cell -4 fires
     t=9    .  H  x  x  x  x  .
     t=10   V  x  x  x  x  x  .   <-- Cell -5 fires

    States:
    - idle: waiting (border cells)
    - v_fire: cell is firing this step
    - hold: cell fired, now holding to signal left neighbor
    - dead: done
  -/

  inductive Q_DiagLeft
  | idle
  | hold | v_fire | dead
  deriving DecidableEq, Inhabited, Fintype

  def diag_left_base {α: Type} [Alphabet α] : CellAutomaton α？ Bool := {
    Q := Q_DiagLeft
    δ := fun _ c r =>
      match c with
      | .v_fire => .hold
      | .hold => .dead
      | .dead => .dead
      | .idle => if r == .hold then .v_fire else .idle
    embed := fun
      | some _ => .v_fire  -- Input cells fire immediately at t=0
      | none => .idle
    project := fun
      | .v_fire => true
      | _ => false
  }

  lemma diag_left_base_state {α} [Alphabet α] (w: Word α) (t: ℕ) (p: ℤ):
      (@diag_left_base α _).nextt ⦋⟬w⟭⦌ t p =
        if w = [] then Q_DiagLeft.idle
        else if p > 0 then Q_DiagLeft.idle
        else if p = 0 then
          match t with
          | 0 => Q_DiagLeft.v_fire
          | 1 => Q_DiagLeft.hold
          | _ => Q_DiagLeft.dead
        else  -- p < 0, so p = -|p|
          let fire_time := 2 * p.natAbs
          if t < fire_time then Q_DiagLeft.idle
          else if t = fire_time then Q_DiagLeft.v_fire
          else if t = fire_time + 1 then Q_DiagLeft.hold
          else Q_DiagLeft.dead
      := by
    -- Proof idea:
    -- By induction on t.
    -- Base case t=0: initial state from embed - input cells get v_fire, border cells get idle
    -- Inductive case: use transition function δ
    --   - idle cells stay idle unless right neighbor is hold
    --   - v_fire → hold → dead → dead
    --   - Cell at p fires when right neighbor (at p+1) was in hold at t-1
    --   - This happens at t = 2*|p| for p < 0
    sorry

  lemma diag_left_base_spec {α} [Alphabet α] (w: Word α) (t: ℕ) (p: ℤ):
      (@diag_left_base α _).comp w t p = (w ≠ [] ∧ p ≤ 0 ∧ t = 2 * p.natAbs) := by
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply, ←embed_word_word_to_config_eq]
    rw [diag_left_base_state]
    simp only [diag_left_base, eq_iff_iff]
    by_cases hw : w = []
    case pos =>
      simp only [hw, ↓reduceIte, ne_eq, not_true_eq_false, false_and]
      constructor <;> intro h <;> cases h
    case neg =>
      simp only [hw, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
      by_cases hp_pos : p > 0
      case pos =>
        simp only [hp_pos, ↓reduceIte]
        constructor
        · intro h; cases h
        · intro ⟨hp_le, _⟩; omega
      case neg =>
        push_neg at hp_pos
        have hp_not_pos : ¬(p > 0) := not_lt.mpr hp_pos
        simp only [hp_not_pos, hp_pos, true_and, ↓reduceIte]
        by_cases hp_zero : p = 0
        case pos =>
          subst hp_zero
          simp only [↓reduceIte, Int.natAbs_zero, mul_zero]
          match t with
          | 0 => simp
          | 1 => simp
          | _+2 => simp
        case neg =>
          have hp_neg : p < 0 := lt_of_le_of_ne hp_pos hp_zero
          simp only [hp_zero, ↓reduceIte]
          constructor
          · intro h
            split_ifs at h
            all_goals assumption
          · intro ht
            simp only [ht, lt_self_iff_false, ↓reduceIte]

end DiagLeft

section ConstDelay

  /-
    ConstDelay: Delays the output of a CA by k steps.

    Given a CA C that computes f(t, p), ConstDelay k C computes f(t - k, p)
    (or a default value for t < k).
  -/

  inductive DelayState (Q: Type) (k: ℕ)
  | waiting : Fin k → DelayState Q k  -- counting down
  | running : Q → DelayState Q k
  deriving DecidableEq

  instance {Q: Type} [Inhabited Q] {k: ℕ} : Inhabited (DelayState Q k) :=
    ⟨.running default⟩

  instance {Q: Type} [Fintype Q] [DecidableEq Q] {k: ℕ} : Fintype (DelayState Q k) :=
    Fintype.ofEquiv (Fin k ⊕ Q) {
      toFun := fun
        | .inl i => .waiting i
        | .inr q => .running q
      invFun := fun
        | .waiting i => .inl i
        | .running q => .inr q
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun x => by cases x <;> rfl
    }

  structure ConstDelay where
    {α: Type}
    {β: Type}
    [_inst_α: Alphabet α]
    [_inst_β: Alphabet β]
    C_orig: CellAutomaton α β
    k: ℕ
    default_output: β

  attribute [instance] ConstDelay._inst_α
  attribute [instance] ConstDelay._inst_β

  namespace ConstDelay
    variable (e: ConstDelay)

    def C : CellAutomaton e.α e.β := {
      Q := DelayState e.C_orig.Q e.k
      δ := fun l c r =>
        match c with
        | .waiting ⟨0, _⟩ =>
          -- Transition to running state
          let l' := match l with
            | .waiting ⟨0, _⟩ => e.C_orig.embed (default : e.α)  -- will become running next step
            | .waiting _ => e.C_orig.embed (default : e.α)
            | .running q => q
          let c' := e.C_orig.embed (default : e.α)  -- will become running
          let r' := match r with
            | .waiting ⟨0, _⟩ => e.C_orig.embed (default : e.α)
            | .waiting _ => e.C_orig.embed (default : e.α)
            | .running q => q
          .running (e.C_orig.δ l' c' r')
        | .waiting ⟨n+1, h⟩ => .waiting ⟨n, Nat.lt_of_succ_lt h⟩
        | .running q =>
          let l' := match l with
            | .waiting _ => e.C_orig.embed (default : e.α)
            | .running q => q
          let r' := match r with
            | .waiting _ => e.C_orig.embed (default : e.α)
            | .running q => q
          .running (e.C_orig.δ l' q r')
      embed := fun a =>
        if h : e.k > 0
        then .waiting ⟨e.k - 1, Nat.sub_lt h (by omega)⟩
        else .running (e.C_orig.embed a)
      project := fun
        | .waiting _ => e.default_output
        | .running q => e.C_orig.project q
    }

    theorem spec (c: Config e.α) (t: ℕ) (p: ℤ):
        e.C.comp c t p =
          if t < e.k then e.default_output
          else e.C_orig.comp c (t - e.k) p := by
      sorry

    theorem trace_spec (c: Config e.α) (t: ℕ):
        e.C.trace c t =
          if t < e.k then e.default_output
          else e.C_orig.trace c (t - e.k) := by
      unfold CellAutomaton.trace
      rw [spec]

  end ConstDelay

end ConstDelay

section DiagLeft3

  /-
    DiagLeft3: Fires at p ≤ 0 at time t = 3 + 2*|p|

    This is DiagLeft delayed by 3 steps.

    Execution for a single input cell at position 0:

    Time   Space (x)
    (t)    -5 -4 -3 -2 -1  0  1
    ---------------------------
     t=0    .  .  .  .  .  0  .   <-- Delay counter
     t=1    .  .  .  .  .  1  .
     t=2    .  .  .  .  .  2  .
     t=3    .  .  .  .  .  V  .   <-- Cell 0 fires (t = 3 + 2*0 = 3)
     t=4    .  .  .  .  .  H  .
     t=5    .  .  .  .  V  x  .   <-- Cell -1 fires (t = 3 + 2*1 = 5)
     t=6    .  .  .  .  H  x  .
     t=7    .  .  .  V  x  x  .   <-- Cell -2 fires (t = 3 + 2*2 = 7)
     t=8    .  .  .  H  x  x  .
     t=9    .  .  V  x  x  x  .   <-- Cell -3 fires (t = 3 + 2*3 = 9)
     t=10   .  .  H  x  x  x  .
     t=11   .  V  x  x  x  x  .
     t=12   .  H  x  x  x  x  .
     t=13   V  x  x  x  x  x  .
  -/

  def diag_left3_via_delay {α: Type} [Alphabet α] : ConstDelay := {
    α := α？
    β := Bool
    C_orig := diag_left_base
    k := 3
    default_output := false
  }

  def diag_left3 {α: Type} [Alphabet α] : CellAutomaton α？ Bool :=
    (@diag_left3_via_delay α _).C

  lemma diag_left3_spec {α} [Alphabet α] (w: Word α) (t: ℕ) (p: ℤ):
      (@diag_left3 α _).comp w t p = (w ≠ [] ∧ p ≤ 0 ∧ t = 3 + 2 * p.natAbs) := by
    unfold diag_left3 diag_left3_via_delay
    simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply]
    have h := ConstDelay.spec
      (e := { α := α？, β := Bool, C_orig := diag_left_base, k := 3, default_output := false })
      (c := ⟬w⟭) t p
    unfold CellAutomaton.comp CellAutomaton.project_config at h
    simp only [Function.comp_apply] at h
    -- The ConstDelay.C embeds ⟬w⟭ then projects
    -- Need to connect ⦋w⦌ for diag_left3 with the delayed computation
    sorry

  def diag_right3 {α: Type} [Alphabet α] : CellAutomaton α？ Bool :=
    (@diag_left3 α _).flip

  lemma diag_right3_spec {α} [Alphabet α] (w: Word α) (t: ℕ) (p: ℤ):
      (@diag_right3 α _).comp w t p = (w ≠ [] ∧ p ≥ 0 ∧ t = 3 + 2 * p.natAbs) := by
    -- Uses: diag_right3 = diag_left3.flip
    -- By flip_comp: C.flip.comp w t p = C.comp w.flip t (-p)
    -- diag_left3 fires at (t, p) when p ≤ 0 and t = 3 + 2*|p|
    -- For diag_right3: fires when -p ≤ 0 (i.e., p ≥ 0) and t = 3 + 2*|-p| = 3 + 2*|p|
    sorry

end DiagLeft3

end CellularAutomatas
