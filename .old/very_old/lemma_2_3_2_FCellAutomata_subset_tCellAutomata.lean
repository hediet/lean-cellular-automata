import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca
import CellularAutomatas.lemma_2_3_1_FCellAutomaton_accept_delta_closed

variable [Alphabet]
variable {C: FCellAutomaton.{u}}



instance { n: ℕ }: Finite { w: Word | w.length = n } := sorry

def max_set' (s: Set ℕ) [Finite s] : ℕ := sorry

noncomputable def t_max' [DefinesTime CA] (ca: CA) (n: ℕ): ℕ :=
  max_set' (time' ca '' { w: Word | w.length = n })

theorem lemma_2_3_2_FCellAutomaton_subset_tCellAutomaton (C: FCellAutomaton.{u}):
  ∃ C': tCellAutomaton.{u},
    C'.L = C.L
  := by

  let ⟨ Cm, h ⟩ := lemma_2_3_1_FCellAutomaton_accept_delta_closed C

  let C't := fun n => t_max' C n

  let C': tCellAutomaton := {
    Q := Cm.Q,
    δ := Cm.δ,
    inv_fin_q := Cm.inv_fin_q,
    inv_decidable_q := Cm.inv_decidable_q,

    embed := Cm.embed,
    border := Cm.border,
    t := C't,
    F_pos := Cm.F_pos,
  }

  have h1: C'.L = C.L := by
    funext w
    suffices : C'.comp w (C'.t w.length) 0 ∈ C'.F_pos ↔ Cm.accepts w
    · sorry
    have ⟨ td, t'_h ⟩  : ∃ td, Cm.time' w + td = C't w.length := by
      sorry

    rw [accept_delta_closed Cm h.2 td]
    rw [t'_h]
