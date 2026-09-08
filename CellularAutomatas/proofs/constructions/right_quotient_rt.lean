import CellularAutomatas.proofs.constructions.basic_compose_k_steps
import CellularAutomatas.proofs.constructions.speedup_k_step
import CellularAutomatas.proofs.constructions.cart_fix_empty_word

/-!
# Real-time closure under fixed right quotients

One initialization step appends a letter to every nonempty input. Composing
with the original recognizer costs two steps relative to the original input's
real-time deadline. Constant additive speedup removes both steps, and the
empty word is handled separately.

The same initialization-and-speedup technique realizes inverse images under
last-position marking. Together the constructions recognize a marked prefix
followed by an arbitrary fixed unmarked continuation.
-/

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [Alphabet α]

namespace RightQuotient

/-- Grow a single cell at the right edge of a nonempty input. -/
def appendOne (a : α) : CellAutomaton (Option α) (Option α) where
  Q := Option α
  embed := id
  project := id
  δ := fun left center _ =>
    match center, left with
    | some x, _ => some x
    | none, some _ => some a
    | none, none => none

lemma appendOne_config (a : α) (w : Word α) (hw : w ≠ []) :
    (appendOne a).comp w 1 = word_to_config (w ++ [a]) := by
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  funext p
  change (match word_to_config w p, word_to_config w (p - 1) with
    | some x, _ => some x
    | none, some _ => some a
    | none, none => none) = word_to_config (w ++ [a]) p
  by_cases hp : 0 ≤ p ∧ p < w.length
  · show _ = _
    have hp' : 0 ≤ p ∧ p < (w ++ [a]).length := by simp; omega
    simp only [word_to_config, hp, hp', and_self, ↓reduceDIte]
    rw [List.getElem_append_left (by omega)]
  · show _ = _
    by_cases he : p = w.length
    · subst p
      have hleft : 0 ≤ (w.length : ℤ) - 1 ∧
          (w.length : ℤ) - 1 < w.length := by omega
      have hone : 1 ≤ w.length := hn
      simp [word_to_config, hone, List.getElem_append_right]
    · have hleft : ¬ (0 ≤ p - 1 ∧ p - 1 < w.length) := by omega
      have hout : ¬ (0 ≤ p ∧ p < (w ++ [a]).length) := by simp; omega
      rw [word_to_config_apply w p, dif_neg hp,
        word_to_config_apply w (p - 1), dif_neg hleft,
        word_to_config_apply (w ++ [a]) p, dif_neg hout]

/-- Initialize the appended letter, then run the original automaton. -/
def delayed (C : CA_rt α) (a : α) : CellAutomaton (Option α) Bool :=
  (appendOne a).composeKSteps C.toCellAutomaton 1

lemma delayed_trace (C : CA_rt α) (a : α) (w : Word α) (hw : w ≠ []) :
    (delayed C a).trace w (w.length + 1) =
      C.trace (w ++ [a]) w.length := by
  show ((appendOne a).composeKSteps C.toCellAutomaton 1).trace w
    (w.length + 1) = _
  rw [CellAutomaton.composeKSteps_trace]
  simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
  rw [appendOne_config a w hw]

lemma accelerated_trace (C : CA_rt α) (a : α) (w : Word α) (hw : w ≠ []) :
    (SpBDk 3 2 (delayed C a)).trace w (w.length - 1) =
      C.trace (w ++ [a]) ((w ++ [a]).length - 1) := by
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  calc
    (SpBDk 3 2 (delayed C a)).trace w (w.length - 1)
        = (delayed C a).trace w (w.length - 1 + 2) := by
          apply SpBDk_trace_eq <;> omega
    _ = (delayed C a).trace w (w.length + 1) := by
          congr 1
          omega
    _ = C.trace (w ++ [a]) w.length := delayed_trace C a w hw
    _ = C.trace (w ++ [a]) ((w ++ [a]).length - 1) := by simp

end RightQuotient

/-- Recognize `w ++ [a]` at the original input's exact real-time deadline. -/
def CA_rt.rightQuotientLetter (C : CA_rt α) (a : α) : CA_rt α :=
  fix_empty (C.trace [a] 0)
    (toRtCa (SpBDk 3 2 (RightQuotient.delayed C a)))

@[simp]
theorem CA_rt.rightQuotientLetter_spec (C : CA_rt α) (a : α) (w : Word α) :
    w ∈ (C.rightQuotientLetter a).L ↔ w ++ [a] ∈ C.L := by
  rw [CA_rt.rightQuotientLetter, fix_empty_spec]
  by_cases hw : w = []
  · subst w
    show _ ↔ [a] ∈ C.L
    simpa using (trace_L (C := C) (w := [a]))
  · show _ ↔ w ++ [a] ∈ C.L
    simp only [show (w == []) = false by simp [hw], Bool.false_eq_true,
      ↓reduceIte, decide_eq_true_eq]
    rw [← trace_L, ← trace_L]
    change (SpBDk 3 2 (RightQuotient.delayed C a)).trace w (w.length - 1) =
      true ↔ _
    rw [RightQuotient.accelerated_trace C a w hw]

/-- Eliminate any fixed suffix from an ordinary real-time recognizer. -/
def CA_rt.rightQuotientWord (C : CA_rt α) : Word α → CA_rt α
  | [] => C
  | a :: z => (C.rightQuotientWord z).rightQuotientLetter a

@[simp]
theorem CA_rt.rightQuotientWord_spec (C : CA_rt α) (z w : Word α) :
    w ∈ (C.rightQuotientWord z).L ↔ w ++ z ∈ C.L := by
  induction z generalizing w with
  | nil =>
      show w ∈ C.L ↔ w ++ [] ∈ C.L
      simp
  | cons a z ih =>
      show w ∈ ((C.rightQuotientWord z).rightQuotientLetter a).L ↔
        w ++ a :: z ∈ C.L
      rw [CA_rt.rightQuotientLetter_spec, ih]
      simp only [List.append_assoc, List.singleton_append]

/-- Decorate exactly the last symbol; the empty word has no marked position. -/
def markLast (w : Word α) : Word (α × Bool) :=
  w.mapIdx fun i a => (a, decide (i + 1 = w.length))

omit [Alphabet α] in
@[simp]
lemma markLast_length (w : Word α) : (markLast w).length = w.length := by
  simp [markLast]

namespace RightQuotient

/-- Store the original center and its right neighbor for one-step edge marking. -/
def markLastInitializer (α : Type) [Alphabet α] :
    CellAutomaton (Option α) (Option (α × Bool)) where
  Q := Option α × Option α
  embed := fun a => (a, none)
  δ := fun _ center right => (center.1, right.1)
  project := fun state => state.1.map fun a => (a, state.2.isNone)

lemma markLastInitializer_config (w : Word α) :
    (markLastInitializer α).comp w 1 = word_to_config (markLast w) := by
  funext p
  change (word_to_config w p).map
    (fun a => (a, (word_to_config w (p + 1)).isNone)) =
      word_to_config (markLast w) p
  by_cases hp : 0 ≤ p ∧ p < w.length
  · show _ = _
    have hmarked : 0 ≤ p ∧ p < (markLast w).length := by simpa using hp
    rw [word_to_config_apply w p, dif_pos hp,
      word_to_config_apply (markLast w) p, dif_pos hmarked]
    simp only [Option.map_some, markLast, List.getElem_mapIdx]
    by_cases hr : 0 ≤ p + 1 ∧ p + 1 < w.length
    · show _ = _
      rw [word_to_config_apply w (p + 1), dif_pos hr]
      simp [show p.toNat + 1 ≠ w.length by omega]
    · show _ = _
      rw [word_to_config_apply w (p + 1), dif_neg hr]
      simp [show p.toNat + 1 = w.length by omega]
  · show _ = _
    have hmarked : ¬ (0 ≤ p ∧ p < (markLast w).length) := by simpa using hp
    rw [word_to_config_apply w p, dif_neg hp,
      word_to_config_apply (markLast w) p, dif_neg hmarked]
    rfl

def markedDelayed (C : CA_rt (α × Bool)) : CellAutomaton (Option α) Bool :=
  (markLastInitializer α).composeKSteps C.toCellAutomaton 1

lemma markedAccelerated_trace (C : CA_rt (α × Bool)) (w : Word α)
    (hw : w ≠ []) :
    (SpBDk 2 1 (markedDelayed C)).trace w (w.length - 1) =
      C.trace (markLast w) ((markLast w).length - 1) := by
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  calc
    (SpBDk 2 1 (markedDelayed C)).trace w (w.length - 1)
        = (markedDelayed C).trace w (w.length - 1 + 1) := by
          apply SpBDk_trace_eq <;> omega
    _ = (markedDelayed C).trace w w.length := by
          congr 1
          omega
    _ = C.trace (markLast w) ((markLast w).length - 1) := by
          unfold markedDelayed
          rw [CellAutomaton.composeKSteps_trace]
          simp only [show w.length ≥ 1 by omega, ↓reduceIte,
            markLastInitializer_config, markLast_length]

end RightQuotient

/-- Recognize last-position-decorated input at the original real-time deadline. -/
def CA_rt.preimageMarkLast (C : CA_rt (α × Bool)) : CA_rt α :=
  fix_empty (C.trace ([] : Word (α × Bool)) 0)
    (toRtCa (SpBDk 2 1 (RightQuotient.markedDelayed C)))

@[simp]
theorem CA_rt.preimageMarkLast_spec (C : CA_rt (α × Bool)) (w : Word α) :
    w ∈ C.preimageMarkLast.L ↔ markLast w ∈ C.L := by
  rw [CA_rt.preimageMarkLast, fix_empty_spec]
  by_cases hw : w = []
  · subst w
    show _ ↔ markLast [] ∈ C.L
    simpa [markLast] using (trace_L (C := C) (w := []))
  · show _ ↔ markLast w ∈ C.L
    simp only [show (w == []) = false by simp [hw], Bool.false_eq_true,
      ↓reduceIte, decide_eq_true_eq]
    rw [← trace_L, ← trace_L]
    change (SpBDk 2 1 (RightQuotient.markedDelayed C)).trace w (w.length - 1) =
      true ↔ _
    rw [RightQuotient.markedAccelerated_trace C w hw]

end CellularAutomatas
