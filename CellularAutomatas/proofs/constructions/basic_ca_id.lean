import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

/-- Identity CA: computes identity after 1 step. State = input alphabet, δ returns center. -/
def CellAutomaton.idCA (α: Type) [Alphabet α]: CellAutomaton α α := {
  Q := α
  δ := fun _ c _ => c
  embed := id
  project := id
}

namespace CellAutomaton.idCA
  variable {α: Type} [Alphabet α]

  private lemma nextt_eq (c: Config α) (t: ℕ) (p: ℤ):
      (idCA α).nextt c t p = c p := by
    induction t generalizing p with
    | zero => rfl
    | succ t ih =>
      rw [CellAutomaton.nextt_succ]
      unfold CellAutomaton.next idCA
      exact ih p

  @[simp]
  theorem comp_spec (c: Config α) (t: ℕ):
      (idCA α).comp c t = c := by
    funext p
    rw [CellAutomaton.comp_apply]
    rw [nextt_eq]
    rfl

  @[simp]
  theorem trace_spec (c: Config α) (t: ℕ):
      (idCA α).trace c t = c 0 := by
    rw [CellAutomaton.trace_eq_comp, comp_spec]
    simp [embed_config, idCA]

end CellAutomaton.idCA

end CellularAutomatas
