import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

lemma embed_word_p_eq {α} [Alphabet α] (w: Word α) {C: CellAutomaton α？ β} (p: ℤ):
    CellAutomaton.embed_config (C := C) (word_to_config w) p = C.embed (if h: p ≥ 0 ∧ p < w.length then w[p.toNat] else none) := by
  unfold CellAutomaton.embed_config word_to_config
  grind

section CisBorder

def c_is_border (α) [Alphabet α]: CellAutomaton α？ Bool :=
  {
    Q := Bool
    δ := fun _ val _ => val
    embed
    | none => true
    | some _ => false
    project := id
  }

@[simp]
lemma c_is_border_spec {α} [Alphabet α] (w: Word α):
    (c_is_border α).comp w t 0 = (w == []) := by
  unfold comp
  erw [Function.id_comp]

  induction t with
  | zero =>
    rw [nextt_zero]
    rw [embed_word_p_eq]
    unfold c_is_border
    cases w
    · simp
    · simp
  | succ t ih =>
    rw [nextt_succ]
    unfold CellAutomaton.next
    rw [ih]
    simp [c_is_border]

end CisBorder

end CellularAutomatas
