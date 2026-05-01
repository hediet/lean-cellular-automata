/-
# `Advice.is_even_length` — definition and rt-closedness

`is_even_length` outputs `true` at every position iff the word length is even.

## Proof strategy

Decompose as `(prefix_mem L).compose broadcast_last` where `L` is recognized by a
parity-tracking CA. Then both parts are two-stage, so the composition is rt-closed.

### The parity CA

State Q = Bool.  Rule: `δ _ _ r := !r`.  Embedding: `none ↦ true`, `some _ ↦ false`.

At cell `p` time `t`, state = `init_state(config(p+t)) XOR (t % 2 = 1)`.
At position 0, time `n-1`, this gives `(n % 2 = 0)`.
-/

import CellularAutomatas.proofs.advice_theory.rt_closed.broadcast_last
import CellularAutomatas.proofs.advice_theory.rt_closed.of_prefix_mem
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_two_stage
import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage
import CellularAutomatas.proofs.ca_rt_utils

namespace CellularAutomatas

open CellAutomaton
open FiniteStateTransducer

variable {α : Type} [Alphabet α]

/-- Advice that outputs True at every position iff the word length is even. -/
def Advice.is_even_length (α : Type) [Alphabet α] : Advice α Bool :=
  { f := fun w => List.replicate w.length (w.length % 2 == 0)
    len := by simp }

section EvenLengthCA

  /-- The cell automaton recognizing length-parity. -/
  def evenLengthCAraw (α : Type) [Alphabet α] : CellAutomaton α？ Bool where
    Q := Bool
    δ _ _ r := !r
    embed
      | none => true
      | some _ => false
    project := id

  /-- Real-time CA wrapping `evenLengthCAraw`. -/
  def evenLengthCA (α : Type) [Alphabet α] : CA_rt α :=
    { toCellAutomaton := evenLengthCAraw α }

  private def init_state (a : Option α) : Bool :=
    match a with | none => true | some _ => false

  private lemma init_state_word (w : Word α) (p : ℤ) :
      init_state (word_to_config w p) = if 0 ≤ p ∧ p < w.length then false else true := by
    unfold init_state word_to_config
    by_cases h : 0 ≤ p ∧ p < w.length
    · simp [h]
    · simp [h]

  /-- State propagation: at cell `p` time `t`,
      state = `init_state(config(p+t)) XOR (t % 2 = 1)`. -/
  lemma evenLengthCAraw_nextt (w : Word α) (t : ℕ) (p : ℤ) :
      (evenLengthCAraw α).nextt ⦋⟬w⟭⦌ t p =
        Bool.xor (init_state (word_to_config w (p + t))) (decide (t % 2 = 1)) := by
    induction t generalizing p with
    | zero =>
      show (evenLengthCAraw α).embed (word_to_config w p) = _
      simp only [Nat.cast_zero, add_zero, Nat.zero_mod]
      cases h : word_to_config w p with
      | none => simp [evenLengthCAraw, init_state]
      | some _ => simp [evenLengthCAraw, init_state]
    | succ t ih =>
      rw [nextt_succ]
      simp only [next_apply]
      rw [ih (p + 1)]
      show (evenLengthCAraw α).δ _ _ _ = _
      simp only [evenLengthCAraw]
      have h_pt : (p + 1 + t : ℤ) = p + (t + 1 : ℕ) := by push_cast; ring
      rw [h_pt]
      generalize init_state (word_to_config w (p + ((t + 1 : ℕ) : ℤ))) = b
      have h_par : (t + 1) % 2 = 1 ↔ ¬ (t % 2 = 1) := by omega
      cases b <;> by_cases h : t % 2 = 1 <;> simp [h, h_par]

  /-- The CA accepts a word iff its length is even. -/
  theorem evenLengthCA_L_eq (α : Type) [Alphabet α] :
      (evenLengthCA α).L = { w : Word α | w.length % 2 = 0 } := by
    ext w
    rw [tCellAutomaton.elem_L_iff]
    show (evenLengthCAraw α).comp ⟬w⟭ (w.length - 1) 0 = true ↔ _
    simp only [comp_apply]
    rw [evenLengthCAraw_nextt]
    show (evenLengthCAraw α).project _ = true ↔ _
    simp only [evenLengthCAraw, id_eq]
    rw [zero_add, init_state_word]
    by_cases hn : w.length = 0
    · constructor
      · intro _; show w.length % 2 = 0; rw [hn]
      · intro _; rw [hn]; decide
    · have hn_pos : 0 < w.length := Nat.pos_of_ne_zero hn
      have h_in : 0 ≤ ((w.length - 1 : ℕ) : ℤ) ∧ ((w.length - 1 : ℕ) : ℤ) < w.length := by
        refine ⟨by positivity, ?_⟩; push_cast; omega
      simp only [h_in, ↓reduceIte, and_self]
      show (false ^^ decide ((w.length - 1 : ℕ) % 2 = 1)) = true ↔ w.length % 2 = 0
      simp only [Bool.false_xor, decide_eq_true_eq]; omega

end EvenLengthCA


section IsEvenLengthRtClosed

  /-- `is_even_length` decomposes as `prefix_mem(evenLengthCA.L).compose broadcast_last`. -/
  theorem is_even_length_eq_compose (α : Type) [Alphabet α] :
      Advice.is_even_length α =
        (Advice.prefix_mem (evenLengthCA α).L).compose (Advice.broadcast_last Bool) := by
    apply advice_eq_iff
    funext w
    show List.replicate w.length (w.length % 2 == 0) =
      List.replicate ((Advice.prefix_mem (evenLengthCA α).L).f w).length
        (((Advice.prefix_mem (evenLengthCA α).L).f w).getLast?.getD default)
    have h_len : ((Advice.prefix_mem (evenLengthCA α).L).f w).length = w.length := by
      simp [Advice.prefix_mem]
    rw [h_len]
    by_cases hn : w.length = 0
    · simp [hn]
    · have hn_pos : 0 < w.length := Nat.pos_of_ne_zero hn
      have h_pm_ne : (Advice.prefix_mem (evenLengthCA α).L).f w ≠ [] := by
        intro h; rw [← List.length_eq_zero_iff, h_len] at h; omega
      have h_last_eq : ((Advice.prefix_mem (evenLengthCA α).L).f w).getLast?
                      = some (decide (w ∈ (evenLengthCA α).L)) := by
        rw [List.getLast?_eq_getLast_of_ne_nil h_pm_ne, List.getLast_eq_getElem]
        simp only [Advice.prefix_mem, List.getElem_map, List.getElem_range,
                   List.length_map, List.length_range, List.extract_eq_drop_take,
                   List.drop_zero]
        rw [List.take_of_length_le (by omega)]
        rfl
      rw [h_last_eq]
      simp only [Option.getD_some]
      have hmem : w ∈ (evenLengthCA α).L ↔ w.length % 2 = 0 := by
        rw [evenLengthCA_L_eq]; rfl
      rw [show decide (w ∈ (evenLengthCA α).L) = decide (w.length % 2 = 0) from by simp [hmem]]
      simp [Bool.beq_eq_decide_eq]

  /-- `is_even_length` is a two-stage advice. -/
  def is_even_length_is_two_stage (α : Type) [Alphabet α] :
      (Advice.is_even_length α).is_two_stage_advice := by
    rw [is_even_length_eq_compose]
    refine ⟨ Advice.broadcast_last_is_two_stage.witness ⊚
              (advice_prefix_mem_is_two_stage_advice (evenLengthCA α)).witness, ?_ ⟩
    apply advice_eq_iff
    rw [compose_two_stage_spec,
        Advice.broadcast_last_is_two_stage.spec,
        (advice_prefix_mem_is_two_stage_advice (evenLengthCA α)).spec]
    rfl

  /-- `is_even_length` is rt-closed. -/
  noncomputable def Advice.is_even_length_rt_closed (α : Type) [Alphabet α] :
      (Advice.is_even_length α).rt_closed := by
    rw [← (is_even_length_is_two_stage α).spec]
    exact two_stage_is_rt_closed (is_even_length_is_two_stage α).witness

end IsEvenLengthRtClosed

end CellularAutomatas
