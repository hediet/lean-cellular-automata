import CellularAutomatas.defs
import Mathlib.Data.List.Basic

def LastInputFSM (Q) [Alphabet Q]: FiniteStateMachine Q := {
  Q := Q
  δ := fun _ a => a
  q0 := default
}

@[simp]
lemma LastInputFSM_scanr_eq [Alphabet Q]:
  (LastInputFSM Q).scanr = id := by
  funext w
  simp [FiniteStateMachine.scanr, FiniteStateMachine.scanr_q]
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [FiniteStateMachine.scanr_step]
    rw [ih]
    cases w <;> simp [LastInputFSM]
