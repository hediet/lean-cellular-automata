import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs

variable {A: Alphabet}


theorem advice_two_stage_closed_under_composition {A O' O: Alphabet} (a1: TwoStageAdvice A O') (a2: TwoStageAdvice O' O):
        ∃ a: TwoStageAdvice A O, a.advice.f = a2.advice.f ∘ a1.advice.f := by
    sorry




lemma ℒ_oca_def {A Γ: Alphabet} (adv: Advice A Γ) (L: Language A.α):
        L ∈ ℒ (@CA_rt (A ⨉ Γ) + adv) ↔ ∃ C ∈ @CA_rt (A ⨉ Γ), L = { w | (w ⊗ (adv.f w)) ∈ C.L } := by
    sorry

lemma ℒ_tCellAutomaton_def {A: Alphabet} (L: Language A.α):
        L ∈ ℒ (CA_rt) ↔ ∃ C ∈ CA_rt, C.L = L := by
    sorry

def tCellAutomaton.map_alphabet {A' A: Alphabet} (C: @tCellAutomaton A) (f: A'.α → A.α): @tCellAutomaton A' := {
    Q := C.Q,
    δ := C.δ,
    border := C.border,
    embed := C.embed ∘ f,
    F_pos := fun n => C.F_pos n,
    p := C.p,
    t := C.t,
}

lemma tCellAutomaton.map_alphabet_language {A' A: Alphabet} (C: @tCellAutomaton A) (f: A'.α → A.α):
        (tCellAutomaton.map_alphabet C f).L = { w | w.map f ∈ C.L } := by
    sorry

@[simp]
lemma zip_advice_first {A Γ: Alphabet} (w: @Word A) (v: @Word Γ):
        (w ⊗ v).map Prod.fst = w := by
    sorry

lemma CA_rt_subseteq_CA_rt_with_advice {A Γ: Alphabet} (adv: Advice A Γ):
        (ℒ (@CA_rt A)) ⊆ ((ℒ (@CA_rt (A ⨉ Γ) + adv)): Set (Language A.α)) := by

    intro L hL
    rw [ℒ_tCellAutomaton_def] at hL

    obtain ⟨C, hC⟩ := hL

    rw [ℒ_oca_def]

    let x: ((A ⨉ Γ).α → A.α) := Prod.fst
    let C' := tCellAutomaton.map_alphabet C x
    use C'

    constructor

    show C' ∈ @CA_rt (A ⨉ Γ)
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




lemma rt_closed (adv: Advice A Γ):
    adv.rt_closed
    ↔ ∀ C ∈ @CA_rt (A ⨉ Γ), ∃ C' ∈ CA_rt, C'.L = { w | (w ⊗ (adv.f w)) ∈ C.L }

 := sorry

theorem advice_two_stage_rt_closed {A O: Alphabet} (a: TwoStageAdvice A O):
        a.advice.rt_closed := by
    rw [rt_closed]
    intro C h

    sorry
