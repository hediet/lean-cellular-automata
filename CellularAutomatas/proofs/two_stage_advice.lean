import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs

variable {α Γ: Type u} [Alphabet α] [Alphabet Γ]

theorem advice_two_stage_closed_under_composition {O': Type u} [Alphabet O'] (a1: TwoStageAdvice α O') (a2: TwoStageAdvice O' Γ):
        ∃ a: TwoStageAdvice α Γ, a.advice.f = a2.advice.f ∘ a1.advice.f := by
    sorry




lemma ℒ_oca_def (adv: Advice α Γ) (L: Language α):
        L ∈ ℒ (CA_rt (α × Γ) + adv) ↔ ∃ C ∈ CA_rt (α × Γ), L = { w | (w ⊗ (adv.f w)) ∈ C.L } := by
    sorry

lemma ℒ_tCellAutomaton_def (L: Language α):
        L ∈ ℒ (CA_rt α) ↔ ∃ C ∈ CA_rt α, C.L = L := by
    sorry

def tCellAutomaton.map_alphabet (C: tCellAutomaton α) (f: Γ → α): tCellAutomaton Γ := {
    Q := C.Q,
    δ := C.δ,
    border := C.border,
    embed := C.embed ∘ f,
    F_pos := fun n => C.F_pos n,
    p := C.p,
    t := C.t,
}

lemma tCellAutomaton.map_alphabet_language (C: tCellAutomaton α) (f: Γ → α):
        (tCellAutomaton.map_alphabet C f).L = { w | w.map f ∈ C.L } := by
    sorry

@[simp]
lemma zip_advice_first (w: Word α) (v: Word Γ):
        (w ⊗ v).map Prod.fst = w := by
    sorry

lemma CA_rt_subseteq_CA_rt_with_advice (adv: Advice α Γ):
        (ℒ (CA_rt α)) ⊆ ((ℒ (CA_rt (α × Γ) + adv)): Set (Language α)) := by

    intro L hL
    rw [ℒ_tCellAutomaton_def] at hL

    obtain ⟨C, hC⟩ := hL

    rw [ℒ_oca_def]

    let x: ((α × Γ) → α) := Prod.fst
    let C' := tCellAutomaton.map_alphabet C x
    use C'

    constructor

    show C' ∈ CA_rt (α × Γ)
    {
        simp_all [CA_rt, t_rt, CA, tCellAutomatons, C', tCellAutomaton.map_alphabet]
    }

    show L = {w | w ⊗ adv.f w ∈ C'.L}
    {
        rw [tCellAutomaton.map_alphabet_language]
        unfold x
        show L = {w | List.map Prod.fst (w ⊗ adv.f w) ∈ C.L}
        simp [zip_advice_first, hC.2]
        rfl
    }




lemma rt_closed (adv: Advice α Γ):
    adv.rt_closed
    ↔ ∀ C ∈ CA_rt (α × Γ), ∃ C' ∈ CA_rt α, C'.L = { w | (w ⊗ (adv.f w)) ∈ C.L }

  := sorry

theorem advice_two_stage_rt_closed (a: TwoStageAdvice α Γ):
        a.advice.rt_closed := by
    rw [rt_closed]
    intro C h

    sorry
