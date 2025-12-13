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
import CellularAutomatas.proofs.advice_prefixes_in_L_rt_closed
import CellularAutomatas.proofs.is_two_stage_of_rt_closed_and_prefix_stable
import CellularAutomatas.proofs.cart_transducers
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.lcellautomaton
import Mathlib.Tactic


open FiniteStateTransducer (M_map M_prod M_projQ M_id)

section

  variable {α β: Type} (w: Word (α × β))

  def Word.fst: Word α := w.map Prod.fst
  def Word.snd: Word β := w.map Prod.snd

  @[simp] lemma Word.fst_len: (w.fst).length = w.length := by simp [Word.fst]
  @[simp] lemma Word.snd_len: (w.snd).length = w.length := by simp [Word.snd]

  @[simp] lemma Word.get_fst (t: Fin w.length): (w.fst)[t] = w[t].1 := by simp [Word.fst]
  @[simp] lemma Word.get_snd (t: Fin w.length): (w.snd)[t] = w[t].2 := by simp [Word.snd]

  @[simp] lemma Word.get_fst_ (t: ℕ) (h: t < (w.fst).length): (w.fst)[t]'h = ((w[t]'(by simp_all)).1) := by simp [Word.fst]
  @[simp] lemma Word.get_snd_ (t: ℕ) (h: t < (w.snd).length): (w.snd)[t]'h = ((w[t]'(by simp_all)).2) := by simp [Word.snd]
end


@[simp] lemma LCellAutomaton.scan_temporal_rt_len {C: LCellAutomaton α} {w: Word α}:
    (C.scan_temporal_rt w).length = w.length := by
  simp [LCellAutomaton.scan_temporal_rt, LCellAutomaton.scan_temporal, List.length_map]

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
    border := (none, fun _ => e.C.border)
    embed := fun a => (some a, fun q => e.C.embed (e.M.f q))
    f := fun (a, f) => (a.getD default, f)
  }

  def M_join [Alphabet γ] [Alphabet α] [Alphabet β] (M: FiniteStateTransducer α β): FiniteStateTransducer (α × (β → γ)) γ :=
    (M_map (fun (a, b) => a b)) ⊚ (M_prod
      (M_map Prod.snd)
      (M ⊚ M_map Prod.fst)
    )

  lemma M_join_spec (γ) [Alphabet α] [Alphabet β] [Alphabet γ] (M: FiniteStateTransducer α β) (w: Word (α × (β → γ))):
    (M_join M).scanr w = List.zipWith (· ·) w.snd (M.scanr w.fst) := by
    simp [M_join, List.zip_eq_zipWith, Word.fst, Word.snd]


  def M' := M_map e.C.f ⊚ (M_join (M_projQ e.M))



  lemma scanr_get'_eq2 {M: FiniteStateTransducer α β} (w: Word α) (i: ℤ) (h: i ∈ w.range):
    (M.scanr w).get' i (by simp [h]) = M.f (M.scanr_reduce w⟦(i).toNat..*⟧) := by
    rw [Word.get']
    have x := M.scanr_get'_eq2 w ⟨ i.toNat, by simp_all [Word.range] ⟩
    simp at x
    simp [←x]



  lemma inv (w: Word e.α) (t: ℕ) (p: ℤ):
      let c' := (C' e).comp w t p
      let q := e.M.scanr_reduce w⟦(p+t).toNat..*⟧
      c'.2 q = (e.C.comp (e.M.scanr w) t p)
      ∧ c'.1 = w.get'? (p + t) := by
    induction t generalizing p with
    | zero =>
      rw [LCellAutomaton.comp_zero]
      rw [LCellAutomaton.comp_zero]


      set c' := (C' e).embed_word w p with h_c'
      set c := e.C.embed_word (e.M.scanr w) p with h_c
      set q := e.M.scanr_reduce w⟦(p + (0: ℕ)).toNat..*⟧ with h_q

      constructor

      case zero.right =>
        unfold Word.get'?
        rw [h_c']
        simp [C', LCellAutomaton.embed_word]
        grind

      rw [h_c']
      rw [h_c]
      simp [C', LCellAutomaton.embed_word]

      by_cases h: p ∈ w.range
      case neg => simp [h]
      case pos =>
        simp [h]
        rw [scanr_get'_eq2]
        grind
        simp [h]



    | succ t ih =>

      set c' := (C' e).comp w (t + 1) p with h_c'
      set q := e.M.scanr_reduce w⟦(p + ↑(t+1)).toNat..*⟧ with h_q

      rw [LCellAutomaton.comp_succ_eq] at h_c'
      set c'_t := ((C' e).comp w t) with h_c'_t

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

      have h1 : qr.2 q1 = e.C.comp (e.M.scanr w) t (p + 1) ∧ qr.1 = (w.get'? (p + ↑t + 1)) := by
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

      have h2 : (qc.2 q2) = e.C.comp (e.M.scanr w) t p := by
        have ih_0 := ih p
        simp [ih_0, q2_eq, qc]


      have h3_1 : ql.1 = (w.get'? (p + ↑t - 1)) := by
        have ih_m1 := ih (p - 1)
        grind

      have h3 : (ql.2 q3) = e.C.comp (e.M.scanr w) t (p - 1) := by
        have ih_m1 := ih (p - 1)

        have q3_eq : q3 = e.M.scanr_reduce w⟦(p - 1 + ↑t).toNat..*⟧ := by
          simp [q3, q2_eq]
          conv =>
            rhs
            rw [FiniteStateTransducer.scanr_reduce'?]
          grind
        simp [h_ql, ih_m1, q3_eq]

      constructor
      simp [h1.1, h2, h3, q3, LCellAutomaton.comp_succ_eq, CellAutomaton.next]
      grind

  @[simp]
  lemma Word.get'_eq (w: Word α) (i: ℕ) (h: i < w.length) (val: α): (w.get'? ↑i).getD val = w[i] := by
    simp [Word.get'?]
    by_cases h: ↑↑i ∈ w.range
    simp [h, Word.get']
    simp_all [Word.range]


  lemma spec_: (M' e).advice.f ∘ (C' e).advice.f = e.C.advice.f ∘ e.M.advice.f := by
      funext w

      unfold FiniteStateTransducer.advice
      simp [CArtTransducer.advice, M']
      congr
      rw [M_join_spec]
      set c' := (C' e).scan_temporal_rt w with eq_c'

      have : Word.fst (List.map (C' e).f c') = w := by
        apply List.ext_getElem
        · simp [c']
        intro i h1 h2
        have inv := (inv e w i 0).2
        simp
        simp [LCellAutomaton.scan_temporal_rt, LCellAutomaton.scan_temporal] at eq_c'
        simp [eq_c']
        conv =>
          pattern (C' e).f
          simp [C']
        simp [inv]
        rw [Word.get'_eq]

      rw [this]

      have : Word.snd (List.map (C' e).f c') = c'.snd := by
        unfold C'
        simp [Word.snd]

      rw [this]

      apply List.ext_getElem
      · simp [eq_c']
        rw [LCellAutomaton.scan_temporal_rt_len]


      intro i h1 h2

      simp

      have x := (inv e w i 0).1
      simp at x

      simp [eq_c']

      unfold LCellAutomaton.scan_temporal_rt LCellAutomaton.scan_temporal
      simp [x]


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


def compose_two_stage [Alphabet α] [Alphabet Γ1] [Alphabet Γ] (a1: TwoStageAdvice α Γ1) (a2: TwoStageAdvice Γ1 Γ):
    TwoStageAdvice α Γ :=
  let e := backwards_fsm.Params.mk a1.M a2.C
  let ca_new := (backwards_fsm.C' e).compose a1.C
  let fsm_new := a2.M ⊚ backwards_fsm.M' e
  TwoStageAdvice.from_transducers fsm_new ca_new



variable [Alphabet Γ'] [Alphabet Γ] [Alphabet α]

lemma TwoStageAdvice.advice_eq (t: TwoStageAdvice α Γ):
    t.advice.f = (t.M.advice.f) ∘ (t.C.advice.f) := by
    simp [TwoStageAdvice.advice]

theorem advice_two_stage_closed_under_composition (a1: TwoStageAdvice α Γ') (a2: TwoStageAdvice Γ' Γ):
    (compose_two_stage a1 a2).advice.f = a2.advice.f ∘ a1.advice.f := by

  rw [Eq.comm]

  let e := backwards_fsm.Params.mk a1.M a2.C
  let ca_new := (backwards_fsm.C' e).compose a1.C
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
      rw [CArtTransducer.compose_spec]
      rw [FiniteStateTransducer.compose_spec]

    _ = (TwoStageAdvice.from_transducers fsm_new ca_new).advice.f := by simp [TwoStageAdvice.from_transducers_eq]
    _ = (compose_two_stage a1 a2).advice.f := by rfl
