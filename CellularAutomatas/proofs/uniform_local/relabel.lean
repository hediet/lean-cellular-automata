import CellularAutomatas.proofs.uniform_local.program
import CellularAutomatas.proofs.basic

namespace CellularAutomatas.UniformLocal

open CellAutomaton

theorem relabel_state {source input output : Type} (g : source → input)
    (target : CellAutomaton input output) (config : Config source) (t : ℕ) (p : ℤ) :
    (((relabel output g).compile target).nextt ⦋config⦌ t p).2 0 =
      target.nextt ⦋fun p => g (config p)⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    rw [nextt_succ, nextt_succ, next_apply, next_apply]
    change target.δ
      ((((relabel output g).compile target).nextt ⦋config⦌ t (p - 1)).2 0)
      ((((relabel output g).compile target).nextt ⦋config⦌ t p).2 0)
      ((((relabel output g).compile target).nextt ⦋config⦌ t (p + 1)).2 0) = _
    rw [ih, ih, ih]

theorem relabel_comp {source input output : Type} (g : source → input)
    (target : CellAutomaton input output) (config : Config source) (t : ℕ) (p : ℤ) :
    ((relabel output g).compile target).comp ⦋config⦌ t p =
      target.comp ⦋fun p => g (config p)⦌ t p := by
  change target.project ((((relabel output g).compile target).nextt ⦋config⦌ t p).2 0) = _
  rw [relabel_state]
  rfl

/-- Identity leaves the target CA unchanged. -/
theorem identity_comp {input output : Type} (target : CellAutomaton input output)
    (config : Config input) (t : ℕ) (p : ℤ) :
    ((identity input output).compile target).comp ⦋config⦌ t p =
      target.comp ⦋config⦌ t p :=
  rfl

theorem relabel_word {α β output : Type} (g : α → β)
    (target : CellAutomaton (Option β) output) (w : Word α) (t : ℕ) (p : ℤ) :
    ((relabel output (Option.map g)).compile target).comp w t p =
      target.comp (w.map g) t p := by
  rw [relabel_comp]
  have hconfig : (fun p => (word_to_config w p).map g) = word_to_config (w.map g) := by
    funext p
    simp [word_to_config]
  rw [hconfig]

end CellularAutomatas.UniformLocal
