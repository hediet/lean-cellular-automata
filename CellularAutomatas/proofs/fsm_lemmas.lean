import CellularAutomatas.defs
import Mathlib.Data.List.Basic

namespace fsm_lemmas

def IdentityReconstructM (Q: Type u) [Alphabet Q]: FiniteStateMachine Q := {
  Q := Q
  δ := fun _ a => a
  q0 := default
}

lemma scanr_identity (Q: Type u) [Alphabet Q] (w: Word Q):
  (IdentityReconstructM Q).scanr w = w := by
  simp [FiniteStateMachine.scanr, FiniteStateMachine.scanr_q]
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [FiniteStateMachine.scanr_step]
    rw [ih]
    cases w <;> simp [IdentityReconstructM]

end fsm_lemmas
