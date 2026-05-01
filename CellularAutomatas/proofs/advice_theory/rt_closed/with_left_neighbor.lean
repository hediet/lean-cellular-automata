/-
# `Advice.with_left_neighbor` — definition and rt-closedness

`with_left_neighbor` pairs each cell with its left neighbor:
  `[a, b, c]` ↦ `[(a, none), (b, some a), (c, some b)]`

## Proof strategy

A CA with state `Q = α？ × α？` where:
- `state.1 = config(p + t)`   (current cell value)
- `state.2 = config(p + t - 1)` for `t ≥ 1`, else `none`

The rule `δ _ s r := (r.1, s.1)` propagates the right neighbour's value
into position 1, while the old position 1 becomes position 2 (dropped).
-/

import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage
import CellularAutomatas.proofs.ca_rt_utils

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [Alphabet α]

/-- Pairs each cell with its left neighbor.
    `[a, b, c]` ↦ `[(a, none), (b, some a), (c, some b)]` -/
def Advice.with_left_neighbor (α : Type) [Alphabet α] : Advice α (α × Option α) :=
  { f := fun w => (List.range w.length).map fun i =>
      (w[i]!, if i > 0 then some w[i - 1]! else none)
    len := by intro w; simp }

section WithLeftNeighborCA

  /-- The CA computing `with_left_neighbor`. -/
  def with_left_neighbor_ca (α : Type) [Alphabet α] : CellAutomaton α？ (α × Option α) where
    Q := α？ × α？
    δ _ s r := (r.1, s.1)
    embed a := (a, none)
    project s := (s.1.getD default, s.2)

  /-- State propagation: at cell `p` time `t`:
      - `state.1 = config(p + t)`
      - `state.2 = config(p + t - 1)` for `t ≥ 1`, `none` for `t = 0`. -/
  lemma with_left_neighbor_ca_nextt (w : Word α) (t : ℕ) (p : ℤ) :
      ((with_left_neighbor_ca α).nextt ⦋⟬w⟭⦌ t p) =
        (word_to_config w (p + t),
          if t = 0 then none else word_to_config w (p + t - 1)) := by
    induction t generalizing p with
    | zero =>
      show (with_left_neighbor_ca α).embed (word_to_config w p) = _
      simp only [Nat.cast_zero, add_zero, ↓reduceIte]
      rfl
    | succ t ih =>
      rw [nextt_succ]
      simp only [next_apply]
      rw [ih (p - 1), ih p, ih (p + 1)]
      show (with_left_neighbor_ca α).δ _ _ _ = _
      simp only [with_left_neighbor_ca]
      have h1 : (p + 1 + (t : ℤ)) = (p + ((t + 1 : ℕ) : ℤ)) := by push_cast; ring
      have h2 : (p + (t : ℤ)) = (p + ((t + 1 : ℕ) : ℤ)) - 1 := by push_cast; ring
      rw [h1, ← h2]; simp

  /-- `with_left_neighbor` is a CArt advice. -/
  def with_left_neighbor_is_cart_advice (α : Type) [Alphabet α] :
      (Advice.with_left_neighbor α).is_cart_advice := by
    refine ⟨ with_left_neighbor_ca α, ?_ ⟩
    apply advice_eq_iff
    funext w
    simp only [CArtTransducer.advice]
    apply List.ext_getElem
    · simp [Advice.with_left_neighbor]
    · intro i hi _
      have hi_w : i < w.length := by
        simp [CellAutomaton.trace_rt] at hi; exact hi
      simp only [Advice.with_left_neighbor, List.getElem_map, List.getElem_range]
      show ((with_left_neighbor_ca α).trace_rt w)[i] = (w[i]!, _)
      simp only [CellAutomaton.trace_rt, List.getElem_map, List.getElem_range]
      show (with_left_neighbor_ca α).trace ⟬w⟭ i = _
      simp only [trace_eq_comp, comp_apply]
      rw [with_left_neighbor_ca_nextt]
      show ((with_left_neighbor_ca α).project _) = _
      simp only [with_left_neighbor_ca, zero_add]
      have h_curr : word_to_config w (i : ℤ) = some w[i] := by
        simp [word_to_config, hi_w]
      have h_w_bang : w[i]! = w[i] := by simp [hi_w]
      rw [h_curr, h_w_bang]
      simp only [Option.getD_some]
      by_cases hi_zero : i = 0
      · subst hi_zero; simp
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
        simp only [hi_zero, ↓reduceIte]
        have hi_pred : i - 1 < w.length := by omega
        have h_prev : word_to_config w ((i : ℤ) - 1) = some (w[i - 1]'hi_pred) := by
          have h_eq : ((i : ℤ) - 1) = ((i - 1 : ℕ) : ℤ) := by push_cast; omega
          rw [h_eq]; simp [word_to_config, hi_pred]
        rw [h_prev]; simp [hi_pos, hi_pred]

end WithLeftNeighborCA

/-- `with_left_neighbor` is rt-closed. -/
noncomputable def Advice.with_left_neighbor_rt_closed (α : Type) [Alphabet α] :
    (Advice.with_left_neighbor α).rt_closed := by
  have hcart := with_left_neighbor_is_cart_advice α
  have hts : (Advice.with_left_neighbor α).is_two_stage_advice := hcart.is_two_stage
  rw [← hts.spec]
  exact two_stage_is_rt_closed hts.witness

end CellularAutomatas
