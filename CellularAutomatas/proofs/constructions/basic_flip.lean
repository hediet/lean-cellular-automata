import CellularAutomatas.defs

namespace CellularAutomatas

open CellAutomaton

def config_to_trace {α: Type} (c: Config α): Trace α := fun t => c t

section flip

  def Config.flip {α: Type} (c: Config α): Config α := fun p => c (-p)

  @[simp]
  lemma Config.flip_flip {α: Type} (c: Config α): c.flip.flip = c := by
    funext p; simp [Config.flip]

  @[simp]
  lemma Config.flip_apply {α: Type} (c: Config α) (p: ℤ): c.flip p = c (-p) := rfl

  def CellAutomaton.flip {α β: Type} (C: CellAutomaton α β): CellAutomaton α β := {
    Q := C.Q
    δ := fun a b c => C.δ c b a
    embed := C.embed
    project := C.project
  }

  @[simp]
  lemma CellAutomaton.flip_flip {α β: Type} (C: CellAutomaton α β): C.flip.flip = C := by
    simp only [CellAutomaton.flip]

  lemma CellAutomaton.flip_embed_config {α β: Type} (C: CellAutomaton α β) (c: Config α):
      C.flip.embed_config c = (C.embed_config c.flip).flip := by
    funext p
    simp only [embed_config_apply, Config.flip_apply, CellAutomaton.flip, neg_neg]

  lemma CellAutomaton.flip_next {α β: Type} (C: CellAutomaton α β) (c: Config C.Q):
      C.flip.next c = (C.next c.flip).flip := by
    funext p
    simp only [next_apply, Config.flip_apply, CellAutomaton.flip]
    ring_nf

  lemma CellAutomaton.flip_nextt {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t: ℕ):
      C.flip.nextt c t = (C.nextt c.flip t).flip := by
    induction t with
    | zero => simp only [nextt_zero]; funext p; simp [Config.flip]
    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      rw [ih]
      rw [C.flip_next]
      simp

  @[simp] theorem CellAutomaton.flip_comp {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t: ℕ) (p: ℤ):
      C.flip.comp c t p = C.comp c.flip t (-p) := by
    simp only [comp_apply]
    rw [C.flip_nextt]
    simp only [Config.flip_apply, CellAutomaton.flip]

  lemma CellAutomaton.flip_embed_config' {α β: Type} (C: CellAutomaton α β) (c: Config α):
      (C.embed_config c).flip = C.embed_config c.flip := by
    funext p
    simp only [embed_config_apply, Config.flip_apply]

  @[simp] theorem CellAutomaton.flip_trace {α β: Type} (C: CellAutomaton α β) (c: Config α) (t: ℕ):
      C.flip.trace c t = C.trace c.flip t := by
    simp only [trace_eq_comp, flip_comp, neg_zero]
    have : (@embed_config _ _ C.flip c).flip = @embed_config _ _ C c.flip := by
      funext p; simp only [Config.flip_apply, embed_config_apply, CellAutomaton.flip]
    rw [this]

end flip

end CellularAutomatas
