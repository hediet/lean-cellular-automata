import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.basic_compose_k_steps
import CellularAutomatas.proofs.constructions.basic_ca_id
import CellularAutomatas.proofs.constructions.basic_ca_left_edge_marker
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

  -- Helper: embed_config (word_to_config _) for single-element word
  lemma embed_word_singleton (C: CellAutomaton α？ β) (a: α) (p: ℤ):
      CellAutomaton.embed_config (C := C) (word_to_config [a]) p = if p = 0 then C.embed (some a) else C.embed none := by
    simp only [CellAutomaton.embed_config, word_to_config]
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
              have beq_false : (Q.fire == Q.hold) = false := by decide
              simp only [beq_false, Bool.false_eq_true, ↓reduceIte]
              have h1 : ¬((t : ℤ) + 1 = -2 * p) := by omega
              have h2 : ¬((t : ℤ) + 1 = -2 * p + 1) := by omega
              rw [if_neg h1, if_neg h2]

            -- Right is .idle
            · rw [if_neg h_right_fire, if_neg h_right_hold]
              have beq_false : (Q.idle == Q.hold) = false := by decide
              simp only [beq_false, Bool.false_eq_true, ↓reduceIte]
              have h1 : ¬((t : ℤ) + 1 = -2 * p) := by omega
              have h2 : ¬((t : ℤ) + 1 = -2 * p + 1) := by omega
              rw [if_neg h1, if_neg h2]

  lemma diag_left_spec (t: ℕ) (p: ℤ):
      diag_left.comp [()] t p = decide ((t : ℤ) = -2 * p) := by
    simp only [CellAutomaton.comp_apply, CellAutomaton.project_config_apply, Function.comp_apply]
    rw [diag_left_state]
    unfold diag_left_expected_state diag_left
    split_ifs with h1 h2
    · simp [h1]
    · simp; omega
    · simp; omega

  /-- For empty input, diag_left outputs false at all times -/
  lemma diag_left_comp_empty (t: ℕ) (p: ℤ):
      diag_left.comp ([] : Word Unit) t p = false := by
    simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold, Function.comp_apply]
    -- The empty word embeds to all-idle state
    have embed_eq : ∀ q : ℤ, CellAutomaton.embed_config (C := diag_left) (word_to_config ([] : Word Unit)) q = Q.idle := by
      intro q
      unfold CellAutomaton.embed_config diag_left word_to_config
      have : ¬(0 ≤ q ∧ q < 0) := by omega
      simp [this]
    -- All states remain idle for empty input
    have h : ∀ s : ℕ, ∀ q : ℤ, diag_left.nextt (CellAutomaton.embed_config (word_to_config ([] : Word Unit))) s q = Q.idle := by
      intro s
      induction s with
      | zero =>
        intro q
        simp only [CellAutomaton.nextt_zero]
        exact embed_eq q
      | succ s ih =>
        intro q
        rw [CellAutomaton.nextt_succ]
        unfold CellAutomaton.next
        simp only [ih (q-1), ih q, ih (q+1)]
        unfold diag_left
        rfl
    rw [h]
    rfl

end DiagLeft







namespace DiagLeftRight

  def diag_left {α: Type} [Alphabet α] : CellAutomaton α？ Bool :=
    (CellAutomaton.leftEdgeCA α).composeKSteps
      ((CellAutomaton.idCA Unit？).composeKSteps CellularAutomatas.diag_left 2)
      1

  lemma diag_left_spec2 {α} [Alphabet α] (w: Word α) (h: w ≠ []) (t: ℕ) (p: ℤ):
      (@diag_left α _).comp w t p = decide (w ≠ [] ∧ p ≤ 0 ∧ t = 3 + 2 * p.natAbs) := by

    unfold diag_left
    simp only [composeKSteps_comp]
    rw [leftEdgeCA.comp_spec w h]

    simp only [idCA.comp_spec]
    unfold CellAutomaton.embed_config
    unfold idCA
    simp only
    simp only [id_eq]

    · split_ifs
      · change CellularAutomatas.diag_left.comp (CellAutomaton.embed_config (⟬[()]⟭)) (t - 1 - 2) p
          = decide (w ≠ [] ∧ p ≤ 0 ∧ t = 3 + 2 * p.natAbs)
        simp
        rw [diag_left_spec]
        grind
      · case neg h1 h2 =>
          change (false = decide (w ≠ [] ∧ p ≤ 0 ∧ t = 3 + 2 * p.natAbs))
          grind
      · case neg h =>
          change (false = decide (w ≠ [] ∧ p ≤ 0 ∧ t = 3 + 2 * p.natAbs))
          grind


  def diag_right {α: Type} [Alphabet α] : CellAutomaton α？ Bool :=
    (CellAutomaton.leftEdgeCA α).composeKSteps
      ((CellAutomaton.idCA Unit？).composeKSteps CellularAutomatas.diag_left.flip 2)
      1

  /-- diag_right fires at (t, p) iff input is non-empty, p ≥ 0, and t = 3 + 2*|p| -/
  lemma diag_right_spec {α} [Alphabet α] (w: Word α) (h: w ≠ []) (t: ℕ) (p: ℤ):
      (@diag_right α _).comp w t p = decide (w ≠ [] ∧ p ≥ 0 ∧ t = 3 + 2 * p.natAbs) := by

    unfold diag_right
    simp only [composeKSteps_comp]

    have : (leftEdgeCA α).comp w 1 = [()] := by
      rw [leftEdgeCA.comp_spec]
      simp [h]
    rw [this]

    have : (idCA Unit？).comp ⦋⟬[()]⟭⦌ 2 = [()] := by
      rw [idCA.comp_spec]
      rfl

    rw [this]
    simp only [flip_comp]


    · split_ifs
      · have : (⦋⟬[()]⟭⦌: Config CellularAutomatas.diag_left.flip.Q).flip = ([()]: Config CellularAutomatas.diag_left.Q) := by
          funext p
          simp only [Config.flip, CellAutomaton.embed_config, word_to_config, CellAutomaton.flip, embed_config]
          by_cases hp : p = 0
          · simp [hp]
          · have h1 : ¬(p ≤ 0 ∧ -p < 1) := by omega
            have h2 : ¬(0 ≤ p ∧ p < 1) := by omega
            simp [h1, h2]
        rw [this]

        rw [diag_left_spec]
        grind
      · case neg h1 h2 =>
          change (false = decide (w ≠ [] ∧ p ≥ 0 ∧ t = 3 + 2 * p.natAbs))
          grind
      · case neg h =>
          change (false = decide (w ≠ [] ∧ p ≥ 0 ∧ t = 3 + 2 * p.natAbs))
          grind


end DiagLeftRight


end CellularAutomatas
