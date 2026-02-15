import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Iterate

namespace CellularAutomatas

open CellAutomaton

section DiagLeft

  /-
    DiagLeft: Fires at p ≤ 0 at time t = 2*|p|

    Input: Single cell [()] at position 0.

    Execution:

    Time   Space (x)
    (t)    -5 -4 -3 -2 -1  0  1
    ---------------------------
     t=0    .  .  .  .  .  V  .   <-- Cell 0 fires immediately
     t=1    .  .  .  .  .  H  .   <-- Cell 0 in Hold
     t=2    .  .  .  .  V  .  .   <-- Cell -1 sees Hold, fires
     t=3    .  .  .  .  H  .  .
     t=4    .  .  .  V  .  .  .   <-- Cell -2 fires
     ...
     t=2k   V at position -k

    States:
    - idle: waiting (border cells, p ≠ 0)
    - fire: cell is firing this step
    - hold: cell fired, now holding to signal left neighbor
  -/

  inductive Q | idle | hold | fire
  deriving DecidableEq, Inhabited, Fintype

  def diag_left : CellAutomaton Unit？ Bool := {
    Q := Q
    δ := fun _ c r =>
      match c with
      | .fire => .hold
      | .hold => .idle
      | .idle => if r == .hold then .fire else .idle
    embed := fun
      | some () => .fire
      | none => .idle
    project := fun
      | .fire => true
      | _ => false
  }

  -- Helper: embed_word for single-element word
  lemma embed_word_singleton (C: CellAutomaton α？ β) (a: α) (p: ℤ):
      @CellAutomaton.embed_word α β C [a] p = if p = 0 then C.embed (some a) else C.embed none := by
    simp only [CellAutomaton.embed_word, CellAutomaton.embed_config, word_to_config]
    by_cases hp : p = 0
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      split_ifs with h
      · simp only [List.length_singleton] at h; omega
      · rfl

  -- Convert state to canonical form
  def diag_left_expected_state (t: ℕ) (p: ℤ) : Q :=
    if (t : ℤ) = -2 * p then .fire
    else if (t : ℤ) = -2 * p + 1 then .hold
    else .idle

  -- The state at each position and time follows the diagonal pattern
  lemma diag_left_state (t: ℕ) (p: ℤ):
      (diag_left.nextt [()] t) p = diag_left_expected_state t p := by
    induction t generalizing p with
    | zero =>
      simp only [CellAutomaton.nextt_zero, Nat.cast_zero, diag_left_expected_state]
      rw [embed_word_singleton]
      simp only [diag_left]
      by_cases hp : p = 0
      · simp [hp]
      · simp only [hp, ↓reduceIte]
        split_ifs with h1 h2
        · omega
        · omega
        · rfl
    | succ t ih =>
      rw [CellAutomaton.nextt_succ]
      simp only [CellAutomaton.next]
      rw [ih (p - 1), ih p, ih (p + 1)]

      unfold diag_left_expected_state
      simp only [Nat.cast_succ]

      -- The transition function applied to the expected states
      -- First simplify the center state using case analysis
      by_cases h_fire : (t : ℤ) = -2 * p
      -- Center state is .fire
      · rw [if_pos h_fire]
        simp only [diag_left]  -- unfold the match on .fire
        -- After .fire comes .hold
        have h_not_next : ¬((t : ℤ) + 1 = -2 * p) := by omega
        have h_next : (t : ℤ) + 1 = -2 * p + 1 := by omega
        rw [if_neg h_not_next, if_pos h_next]

      · by_cases h_hold : (t : ℤ) = -2 * p + 1
        -- Center state is .hold
        · rw [if_neg h_fire, if_pos h_hold]
          simp only [diag_left]  -- unfold the match on .hold
          -- After .hold comes .idle
          have h1 : ¬((t : ℤ) + 1 = -2 * p) := by omega
          have h2 : ¬((t : ℤ) + 1 = -2 * p + 1) := by omega
          rw [if_neg h1, if_neg h2]

        -- Center state is .idle
        · rw [if_neg h_fire, if_neg h_hold]
          simp only [diag_left]  -- unfold the match on .idle
          -- Check right neighbor for .hold
          by_cases h_right_hold : (t : ℤ) = -2 * (p + 1) + 1
          -- Right is .hold → fire
          · have hR1 : ¬((t : ℤ) = -2 * (p + 1)) := by omega
            rw [if_neg hR1, if_pos h_right_hold]
            -- Right neighbor is .hold, so beq check succeeds
            simp only [beq_self_eq_true, ↓reduceIte]
            have h_next_fire : (t : ℤ) + 1 = -2 * p := by omega
            rw [if_pos h_next_fire]

          · by_cases h_right_fire : (t : ℤ) = -2 * (p + 1)
            -- Right is .fire
            · rw [if_pos h_right_fire]
              have beq_false : (Q.fire == Q.hold) = false := by native_decide
              simp only [beq_false, Bool.false_eq_true, ↓reduceIte]
              have h1 : ¬((t : ℤ) + 1 = -2 * p) := by omega
              have h2 : ¬((t : ℤ) + 1 = -2 * p + 1) := by omega
              rw [if_neg h1, if_neg h2]

            -- Right is .idle
            · rw [if_neg h_right_fire, if_neg h_right_hold]
              have beq_false : (Q.idle == Q.hold) = false := by native_decide
              simp only [beq_false, Bool.false_eq_true, ↓reduceIte]
              have h1 : ¬((t : ℤ) + 1 = -2 * p) := by omega
              have h2 : ¬((t : ℤ) + 1 = -2 * p + 1) := by omega
              rw [if_neg h1, if_neg h2]

  lemma diag_left_spec (t: ℕ) (p: ℤ):
      diag_left.comp [()] t p = ((t : ℤ) = -2 * p) := by
    simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply]
    rw [diag_left_state]
    unfold diag_left_expected_state diag_left
    split_ifs with h1 h2
    · simp [h1]
    · simp; omega
    · simp; omega

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

    Execution for input [()] at position 0:

    Time   Space (x)
    (t)    -5 -4 -3 -2 -1  0  1
    ---------------------------
     t=0    .  .  .  .  .  0  .   <-- Delay counter
     t=1    .  .  .  .  .  1  .
     t=2    .  .  .  .  .  2  .
     t=3    .  .  .  .  .  F  .   <-- Cell 0 fires (t = 3 + 2*0 = 3)
     t=4    .  .  .  .  .  H  .
     t=5    .  .  .  .  F  .  .   <-- Cell -1 fires (t = 3 + 2*1 = 5)
     t=6    .  .  .  .  H  .  .
     t=7    .  .  .  F  .  .  .   <-- Cell -2 fires (t = 3 + 2*2 = 7)
     ...
  -/

  def diag_left3_via_delay : ConstDelay := {
    α := Unit？
    β := Bool
    C_orig := diag_left
    k := 3
    default_output := false
  }

  def diag_left3 : CellAutomaton Unit？ Bool :=
    diag_left3_via_delay.C

  lemma diag_left3_spec (t: ℕ) (p: ℤ):
      diag_left3.comp unit_input t p = (p ≤ 0 ∧ t = 3 + 2 * p.natAbs) := by
    unfold diag_left3 diag_left3_via_delay
    simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply]
    have h := ConstDelay.spec
      (e := { α := Unit？, β := Bool, C_orig := diag_left, k := 3, default_output := false })
      (c := [()]) t p
    unfold CellAutomaton.comp CellAutomaton.project_config at h
    simp only [Function.comp_apply] at h
    -- Use delayed spec and diag_left_spec
    sorry

  def diag_right3 : CellAutomaton Unit？ Bool :=
    diag_left3.flip

  lemma diag_right3_spec (t: ℕ) (p: ℤ):
      diag_right3.comp unit_input t p = (p ≥ 0 ∧ t = 3 + 2 * p.natAbs) := by
    -- diag_right3 = diag_left3.flip
    -- flip reverses the spatial coordinate
    sorry

end DiagLeft3

namespace DiagLeftRight

  inductive Q_DL
  | idle
  | p_s0 | p_s1 | p_s2 | hold | v_fire | dead
  deriving DecidableEq, Inhabited, Fintype

  def diag_left {α: Type} [Alphabet α] : CellAutomaton α？ Bool := {
    Q := Q_DL
    δ := fun _ c r =>
      match c with
      | .p_s0 => .p_s1
      | .p_s1 => .p_s2
      | .p_s2 => .v_fire
      | .v_fire => .hold
      | .hold => .dead
      | .dead => .dead
      | .idle => if r == .hold then .v_fire else .idle
    embed := fun
      | some _ => .p_s0
      | none => .idle
    project := fun
      | .v_fire => true  -- fires at p≤0, t=3+2*|p|
      | _ => false
  }

  /-
    Execution of diag_left for a single input cell at position 0.
    The CA propagates a "virtual fire" (V) signal to the left.

    Time   Space (x)
    (t)    -5 -4 -3 -2 -1  0  1
    ---------------------------
     t=0    .  .  .  .  .  0  .
     t=1    .  .  .  .  .  1  .
     t=2    .  .  .  .  .  2  .
     t=3    .  .  .  .  .  V  .   <-- Cell 0 fires (Output!)
     t=4    .  .  .  .  .  H  .   <-- Cell 0 in Hold
     t=5    .  .  .  .  V  x  .   <-- Cell -1 sees Hold, becomes V_fire (Output!)
     t=6    .  .  .  .  H  x  .   <-- Cell -1 becomes Hold
     t=7    .  .  .  V  x  x  .   <-- Cell -2 sees Hold, becomes V_fire (Output!)
     t=8    .  .  .  H  x  x  .
     t=9    .  .  V  x  x  x  .   <-- Cell -3 sees Hold, becomes V_fire (Output!)
     t=10   .  .  H  x  x  x  .
     t=11   .  V  x  x  x  x  .
     t=12   .  H  x  x  x  x  .
     t=13   V  x  x  x  x  x  .
  -/

  lemma diag_left_spec {α} [Alphabet α] (w: Word α) (t: ℕ) (p: ℤ):
      (@diag_left α _).comp w t p = decide (w ≠ [] ∧ p ≤ 0 ∧ t = 3 + 2 * p.natAbs) := by
    sorry

  def diag_right {α: Type} [Alphabet α] : CellAutomaton α？ Bool :=
    (@diag_left α _).flip

  lemma diag_right_spec {α} [Alphabet α] (w: Word α) (t: ℕ) (p: ℤ):
      (@diag_right α _).comp w t p = decide (w ≠ [] ∧ p ≥ 0 ∧ t = 3 + 2 * p.natAbs) := by
    -- Uses: diag_right = diag_left.flip
    -- flip_comp: C.flip.comp c t p = C.comp c.flip t (-p)
    -- diag_left fires at (t, p) when p ≤ 0 and t = 3 + 2*|p|
    -- So diag_right fires when -p ≤ 0 (i.e., p ≥ 0) and t = 3 + 2*|-p| = 3 + 2*|p|
    sorry

end DiagLeftRight


end CellularAutomatas
