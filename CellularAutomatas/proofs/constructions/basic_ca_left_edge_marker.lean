import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

/-- Left edge detector CA: outputs [some ()] at position 0 after 1 step on non-empty words -/
def CellAutomaton.leftEdgeCA (α: Type) [Alphabet α]: CellAutomaton α？ Unit？ := {
  Q := Bool
  δ := fun l c _ => !l && c
  embed := fun
    | some _ => true
    | none => false
  project := fun
    | true => some ()
    | false => none
}

namespace CellAutomaton.leftEdgeCA
  variable {α: Type} [Alphabet α]

  @[simp]
  theorem comp_spec (w: Word α) (hw: w ≠ []):
      (leftEdgeCA α).comp ⟬w⟭ 1 = ⟬[()]⟭ := by
    have hw' : w.length > 0 := by cases w <;> simp_all
    funext p
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply, CellAutomaton.nextt_succ, CellAutomaton.nextt_zero]
    unfold CellAutomaton.next CellAutomaton.embed_config leftEdgeCA word_to_config
    simp only [ge_iff_le, List.length_singleton]
    split_ifs <;> first | rfl | omega

  @[simp]
  theorem trace_spec (w: Word α) (hw: w ≠ []):
      (leftEdgeCA α).trace ⟬w⟭ 1 = some () := by
    unfold CellAutomaton.trace
    rw [comp_spec w hw]
    unfold word_to_config
    simp

  /-- For empty input, leftEdgeCA outputs empty at all times -/
  @[simp]
  theorem comp_empty (t: ℕ):
      (leftEdgeCA α).comp ⟬([] : Word α)⟭ t = ⟬[]⟭ := by
    funext p
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply]
    -- The empty word embeds to all-false state
    have embed_eq : ∀ q : ℤ, (leftEdgeCA α).embed_config ⟬([] : Word α)⟭ q = false := by
      intro q
      unfold CellAutomaton.embed_config leftEdgeCA word_to_config
      have : ¬(0 ≤ q ∧ q < 0) := by omega
      simp [this]
    -- All states remain false for empty input
    have h : ∀ s : ℕ, ∀ q : ℤ, (leftEdgeCA α).nextt ((leftEdgeCA α).embed_config ⟬([] : Word α)⟭) s q = false := by
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
        unfold leftEdgeCA
        rfl
    rw [h]
    unfold leftEdgeCA word_to_config
    have : ¬(0 ≤ p ∧ p < 0) := by omega
    simp [this]

end CellAutomaton.leftEdgeCA

end CellularAutomatas
