/-
# `Advice.broadcast_last` — definition and rt-closedness

`broadcast_last` copies the last input symbol uniformly to every output position.
It is rt-closed via a single right-to-left FST (no CA needed).
-/

import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage
import CellularAutomatas.proofs.constructions.trace_id

namespace CellularAutomatas

open CellAutomaton
open FiniteStateTransducer

variable {α : Type} [Alphabet α]

/-- The advice that broadcasts the last input element to every position. -/
def Advice.broadcast_last (α : Type) [Alphabet α] : Advice α α where
  f w := List.replicate w.length (w.getLast?.getD default)
  len := by simp

/-- FST that broadcasts the last input. Scanning right-to-left, the first input
    seen is the rightmost (= last). We latch it in the state and emit forever. -/
def fst_broadcast_last (α : Type) [Alphabet α] : FiniteStateTransducer α α where
  Q := Option α
  δ q a := match q with | none => some a | some x => some x
  q0 := none
  f q := q.getD default

/-- After processing a list right-to-left, the FST state equals `w.getLast?`. -/
lemma fst_broadcast_last_reduce (w : Word α) :
    (fst_broadcast_last α).scanr_reduce w = w.getLast? := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [scanr_reduce, scanr_reduce_q]
    change (fst_broadcast_last α).δ ((fst_broadcast_last α).scanr_reduce_q
      (fst_broadcast_last α).q0 as) a = _
    change (fst_broadcast_last α).δ ((fst_broadcast_last α).scanr_reduce as) a = _
    rw [ih]
    cases as with
    | nil => rfl
    | cons b bs =>
      show (fst_broadcast_last α).δ (b :: bs).getLast? a = (a :: b :: bs).getLast?
      simp only [List.getLast?_cons_cons]
      cases h : (b :: bs).getLast? with
      | none =>
        exfalso
        rw [List.getLast?_eq_none_iff] at h
        exact List.cons_ne_nil _ _ h
      | some x => rfl

/-- The FST output at every position equals the last input. -/
lemma fst_broadcast_last_scanr_eq (w : Word α) :
    (fst_broadcast_last α).scanr w =
      List.replicate w.length (w.getLast?.getD default) := by
  apply List.ext_getElem (by simp)
  intro i hi _
  have hi_w : i < w.length := by simpa using hi
  have h_idx := scanr_get'_eq1 (M := fst_broadcast_last α) w ⟨i, hi_w⟩
  simp only [List.getElem_replicate]
  have h_idx' : ((fst_broadcast_last α).scanr w)[i]'(by simpa) =
      (fst_broadcast_last α).f
        ((fst_broadcast_last α).δ
          ((fst_broadcast_last α).scanr_reduce (w.drop (i + 1))) w[i]) := h_idx
  rw [h_idx', fst_broadcast_last_reduce]
  have h_drop_last : (w.drop (i + 1)).getLast? = if i + 1 < w.length then w.getLast? else none := by
    by_cases h : i + 1 < w.length
    · simp only [h, ↓reduceIte]
      rw [List.getLast?_drop]
      have : ¬ (w.length ≤ i + 1) := by omega
      simp [this]
    · push_neg at h
      have : w.drop (i + 1) = [] := List.drop_eq_nil_of_le h
      simp [this, h]
  rw [h_drop_last]
  by_cases h_lt : i + 1 < w.length
  · simp only [h_lt, ↓reduceIte]
    have h_last_some : ∃ x, w.getLast? = some x := by
      cases h : w.getLast? with
      | some x => exact ⟨x, rfl⟩
      | none =>
        rw [List.getLast?_eq_none_iff] at h; subst h; simp at hi_w
    obtain ⟨x, hx⟩ := h_last_some
    rw [hx]
    change (fst_broadcast_last α).f ((fst_broadcast_last α).δ (some x) w[i]) = _
    change x = (some x).getD default
    rfl
  · push_neg at h_lt
    simp only [show ¬(i + 1 < w.length) from by omega, ↓reduceIte]
    change (fst_broadcast_last α).f ((fst_broadcast_last α).δ none w[i]) = _
    simp only [fst_broadcast_last, Option.getD_some]
    have h_last : w.getLast? = some w[i] := by
      have hw_ne : w ≠ [] := by intro hw; rw [hw] at hi_w; simp at hi_w
      rw [List.getLast?_eq_getLast_of_ne_nil hw_ne]
      congr 1
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    rw [h_last]
    rfl

/-- `broadcast_last` is a two-stage advice: identity CArt + broadcast FST. -/
def Advice.broadcast_last_is_two_stage :
    (Advice.broadcast_last α).is_two_stage_advice :=
  ⟨ TwoStageAdvice.from_transducers (fst_broadcast_last α) (ca_trace_id_word α), by
    apply advice_eq_iff
    funext w
    simp only [TwoStageAdvice.from_transducers_eq, Function.comp_apply,
               FiniteStateTransducer.advice, CArtTransducer.advice,
               ca_trace_id_scan_temporal, id_eq]
    exact fst_broadcast_last_scanr_eq w ⟩

/-- `broadcast_last` is rt-closed. -/
noncomputable def Advice.broadcast_last_rt_closed :
    (Advice.broadcast_last α).rt_closed := by
  rw [← Advice.broadcast_last_is_two_stage.spec]
  exact two_stage_is_rt_closed Advice.broadcast_last_is_two_stage.witness

end CellularAutomatas
