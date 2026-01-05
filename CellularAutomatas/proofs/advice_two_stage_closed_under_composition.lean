import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Option.Basic
import CellularAutomatas.defs
import CellularAutomatas.proofs.finite_state_transducers
import Mathlib.Tactic
import CellularAutomatas.proofs.composition
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open FiniteStateTransducer (M_map M_prod M_projQ M_id)


namespace backwards_fsm


  structure Params where
    {α: Type}
    {β: Type}
    {γ: Type}
    [inst1: Alphabet α]
    [inst2: Alphabet β]
    [inst3: Alphabet γ]
    M: FiniteStateTransducer α β
    C: CArtTransducer β γ

  instance (e : Params) : Alphabet e.α := e.inst1
  instance (e : Params) : Alphabet e.β := e.inst2
  instance (e : Params) : Alphabet e.γ := e.inst3
  variable (e: Params)


  def C': CArtTransducer e.α (e.α × (e.M.Q → e.C.Q)) := {
    Q := Option e.α × (e.M.Q → e.C.Q)
    δ := fun (al, fl) (ac, fc) (ar, fr) =>
      (ar, fun q =>
        let q_right := e.M.δ? q ac
        let q_center := e.M.δ? q_right al
        e.C.δ (fl q_center) (fc q_right) (fr q)
      )
    embed := fun
    | some a => (some a, fun q => e.C.embed (e.M.f q))
    | none => (none, fun _ => e.C.embed none)
    project := fun (a, f) => (a.getD default, f)
  }

  def M_join [Alphabet γ] [Alphabet α] [Alphabet β] (M: FiniteStateTransducer α β): FiniteStateTransducer (α × (β → γ)) γ :=
    (M_map (fun (a, b) => a b)) ⊚ ((M_map Prod.snd) ⨂₂ (M ⊚ M_map Prod.fst))


  lemma M_join_spec (γ) [Alphabet α] [Alphabet β] [Alphabet γ] (M: FiniteStateTransducer α β) (w: Word (α × (β → γ))):
    (M_join M).scanr w = List.zipWith (· ·) w.snd (M.scanr w.fst) := by
    simp [M_join, List.zip_eq_zipWith, Word.fst, Word.snd]


  def M' := M_map e.C.project ⊚ (M_join (M_projQ e.M))


  lemma scanr_get'_eq2 {M: FiniteStateTransducer α β} (w: Word α) (i: ℤ) (h: i ∈ w.range):
    (M.scanr w).get' i (by simp [h]) = M.f (M.scanr_reduce w⟦(i).toNat..*⟧) := by
    rw [Word.get']
    have x := M.scanr_get'_eq2 w ⟨ i.toNat, by simp_all [Word.range] ⟩
    rw [←x]
    congr




  lemma inv (w: Word e.α) (t: ℕ) (p: ℤ):
      let c' := (C' e).nextt w t p
      let q := e.M.scanr_reduce w⟦(p+t).toNat..*⟧
      c'.2 q = (e.C.nextt (e.M.scanr w) t p)
      ∧ c'.1 = w.get'? (p + t) := by

    induction t generalizing p with
    | zero =>
      by_cases h : p ∈ w.range
      <;> simp [h, C', Word.get'?, scanr_get'_eq2]

    | succ t ih =>


      set c' := (C' e).nextt w (t + 1) p with h_c'
      set q := e.M.scanr_reduce w⟦(p + ↑(t+1)).toNat..*⟧ with h_q

      rw [CellAutomaton.nextt_succ] at h_c'

      set c'_t := ((C' e).nextt w t) with h_c'_t

      unfold CellAutomaton.next at h_c'

      set ql := (c'_t (p - 1)) with h_ql
      set qc := (c'_t p) with h_qc
      set qr := (c'_t (p + 1)) with h_qr

      have x: c'.2 q =
          let q_right := e.M.δ? q qc.1
          let q_center := e.M.δ? q_right ql.1
          e.C.δ (ql.2 q_center) (qc.2 q_right) (qr.2 q)
        := by simp [h_ql, h_qc, h_qr, h_c', C']


      simp [C'] at h_c'
      rw [h_c']
      simp

      set q1 := q
      set q2 := e.M.δ? q1 qc.1
      set q3 := e.M.δ? q2 ql.1
      set q4 := e.M.δ? q2 ql.1


      have ih_p1 := ih (p + 1)

      have h1 : qr.2 q1 = e.C.nextt (e.M.scanr w) t (p + 1) ∧ qr.1 = (w.get'? (p + ↑t + 1)) := by
        have q_eq : e.M.scanr_reduce w⟦(p + 1 + ↑t).toNat..*⟧ = q := by
          have : (p + 1 + ↑t).toNat = (p + (↑t + 1)).toNat := by omega
          simp [this, q]
        have ih_p1 := ih (p + 1)
        rw [q_eq] at ih_p1
        simp at ih_p1
        simp [h_qr, ih_p1]
        grind

      have h2_1 : qc.1 = (w.get'? (p + ↑t)) := by
        have ih_0 := ih p
        simp [ih_0, qc]

      have q2_eq : q2 = e.M.scanr_reduce w⟦(p + ↑t).toNat..*⟧ := by
        simp [q2, h_q]
        conv =>
          rhs
          rw [FiniteStateTransducer.scanr_reduce'?]
        simp [h2_1]
        grind

      have h2 : (qc.2 q2) = e.C.nextt (e.M.scanr w) t p := by
        have ih_0 := ih p
        simp [ih_0, q2_eq, qc]


      have h3_1 : ql.1 = (w.get'? (p + ↑t - 1)) := by
        have ih_m1 := ih (p - 1)
        grind

      have q3_eq : q3 = e.M.scanr_reduce w⟦(p - 1 + ↑t).toNat..*⟧ := by
          simp [q3, q2_eq]
          conv =>
            rhs
            rw [FiniteStateTransducer.scanr_reduce'?]
          grind

      have h3 : (ql.2 q3) = e.C.nextt (e.M.scanr w) t (p - 1) := by
        have ih_m1 := ih (p - 1)
        simp [h_ql, ih_m1, q3_eq]

      constructor
      · simp [h1.1, h2, h3, CellAutomaton.next]
      · dsimp
        change (c'_t (p+1)).1 = _
        rw [← h_qr]
        rw [h1.2]
        congr 1
        omega



  lemma spec_: (M' e).advice.f ∘ (C' e).advice.f = e.C.advice.f ∘ e.M.advice.f := by
      funext w

      unfold FiniteStateTransducer.advice
      simp [CArtTransducer.advice, M']

      simp [backwards_fsm.M_join_spec e.C.Q]


      set c' := (C' e).trace_rt w with eq_c'

      apply List.ext_getElem
      · simp_all


      intro i h1 h2
      simp

      have h_w : Word.fst c' = w := by
        apply List.ext_getElem
        · simp_all
        intro t ht1 ht2
        simp [eq_c']

        simp [CellAutomaton.trace_rt, CellAutomaton.trace, comp_word_eq_project_nextt]

        have x := (inv e w t 0).2
        conv in (CellAutomaton.project (C' e)) =>
          simp [C']
        simp [x]
        rw [Word.get'_eq]

      simp [h_w]
      simp [eq_c']
      simp [CellAutomaton.trace_rt, CellAutomaton.trace, comp_word_eq_project_nextt]

      congr


      have x := inv e w i 0
      simp at x
      conv in (CellAutomaton.project (C' e)) =>
        simp [C']
      simp
      rw [x.1]




  theorem spec {α β γ: Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    {M: FiniteStateTransducer α β}
    {C: CArtTransducer β γ}:
      C.advice.f ∘ M.advice.f = (M' ⟨M, C⟩).advice.f ∘ (C' ⟨M, C⟩).advice.f :=
    by grind only [!spec_]

end backwards_fsm



def TwoStageAdvice.from_transducers {β: Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (M: FiniteStateTransducer β γ) (C: CArtTransducer α β): TwoStageAdvice α γ :=
  { C := C, β := β, M := M }

lemma TwoStageAdvice.from_transducers_eq {β: Type} [Alphabet α] [Alphabet β] [Alphabet γ] (M: FiniteStateTransducer β γ) (C: CArtTransducer α β):
    (TwoStageAdvice.from_transducers M C).advice.f = M.advice.f ∘ C.advice.f := by rfl


def compose_two_stage [Alphabet α] [Alphabet Γ1] [Alphabet Γ] (a2: TwoStageAdvice Γ1 Γ) (a1: TwoStageAdvice α Γ1):
    TwoStageAdvice α Γ :=
  let e := backwards_fsm.Params.mk a1.M a2.C
  let ca_new := (backwards_fsm.C' e).compose a1.C
  let fst_new := a2.M ⊚ backwards_fsm.M' e
  TwoStageAdvice.from_transducers fst_new ca_new



variable [Alphabet Γ'] [Alphabet Γ] [Alphabet α]

lemma TwoStageAdvice.advice_eq (t: TwoStageAdvice α Γ):
    t.advice.f = (t.M.advice.f) ∘ (t.C.advice.f) := by
    simp [TwoStageAdvice.advice, FiniteStateTransducer.advice, CArtTransducer.advice]

@[simp]
theorem advice_two_stage_closed_under_composition (a1: TwoStageAdvice α Γ') (a2: TwoStageAdvice Γ' Γ):
    (compose_two_stage a2 a1).advice.f = a2.advice.f ∘ a1.advice.f := by

  rw [Eq.comm]

  let e := backwards_fsm.Params.mk a1.M a2.C
  let ca_new := (backwards_fsm.C' e) ⊚ a1.C
  let fsm_new := a2.M ⊚ backwards_fsm.M' e

  calc (a2.advice.f ∘ a1.advice.f)
    _ = (a2.M.advice.f ∘ a2.C.advice.f) ∘ (a1.M.advice.f ∘ a1.C.advice.f) := by
      simp [TwoStageAdvice.advice_eq]

    _ = a2.M.advice.f ∘ (a2.C.advice.f ∘ a1.M.advice.f) ∘ a1.C.advice.f := by
      simp [Function.comp_assoc]

    _ = a2.M.advice.f ∘ ((backwards_fsm.M' e).advice.f ∘ (backwards_fsm.C' e).advice.f) ∘ a1.C.advice.f := by
      simp [backwards_fsm.spec, e]

    _ = (a2.M.advice.f ∘ (backwards_fsm.M' e).advice.f) ∘ ((backwards_fsm.C' e).advice.f ∘ a1.C.advice.f) := by
      simp [Function.comp_assoc]

    _ = fsm_new.advice.f ∘ ca_new.advice.f := by
      rw [CArtTransducer.compose_spec2]
      rw [FiniteStateTransducer.compose_spec]

    _ = (TwoStageAdvice.from_transducers fsm_new ca_new).advice.f := by simp [TwoStageAdvice.from_transducers_eq]
    _ = (compose_two_stage a2 a1).advice.f := by rfl


infixr:90 " ⊚ "  => compose_two_stage
