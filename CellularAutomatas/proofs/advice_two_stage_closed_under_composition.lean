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
import CellularAutomatas.proofs.scan_lemmas
import CellularAutomatas.proofs.fsm_lemmas





  def TwoStageAdvice.cart_transducer (adv: TwoStageAdvice α Γ): CArtTransducer α adv.C.Q :=
    {
      toLCellAutomaton := adv.C,
      f := id
    }




namespace compress_by_3
  variable [Alphabet α] [Alphabet β]

  theorem compression1 (C: LCellAutomaton α):
      ∃ (C': LCellAutomaton α) (f: C'.Q → Option (C.Q × C.Q × C.Q)),
      ∀ w (t: ℕ) (p: ℤ),
        f (C'.comp w t p) =
          if p >= 0 ∧ t = 2 * p + 3
          then
            let i := (3 * p).natAbs;
            some (C.comp w (i) 0, C.comp w (i + 1) 0, C.comp w (i + 2) 0)
          else none
          := by
    sorry

end compress_by_3



namespace speedup_factor_k
  variable [Alphabet α] [Alphabet β]

  variable {Q: Type}
  variable (k: ℕ) [NeZero k]

  def compress (c: Config Q): Config (Fin k → Q) :=
    fun p => fun j => c (p * k + j)

  def decompress (c: Config (Fin k → Q)): Config Q :=
    fun p => c (p / k) (Fin.intCast p)

  lemma compress_decompress (c: Config Q):
      decompress k (compress k c) = c := by
        sorry

  variable (C: CellAutomaton)

  def Q' := Fin k → C.Q

  def local_config (a b c: Q' k C): Config C.Q :=
      fun p => if p <= -k then a (Fin.intCast 0) else
        if p < 0 then a (Fin.intCast (p + k))
        else if p < k then b (Fin.intCast p)
        else c (Fin.intCast (p - k))

  def to_local_config (c: Config (C.Q)): Q' k C := fun j => c j

  def C': CellAutomaton := {
    Q := Fin k → C.Q
    δ := fun a b c =>
      to_local_config k C (C.nextt (local_config k C (a) (b) (c)) k)
  }



  lemma compression_k_step (c: Config C.Q):
      (C' k C).next (compress k c) = compress k (C.nextt c k) :=
        sorry

  theorem spec (c: Config C.Q):
      ∀ t, (C' k C).nextt (compress k c) t = compress k (C.nextt c (k * t)) :=
        sorry

end speedup_factor_k



namespace simulation
  structure Params where
    C_inr: CellAutomaton
    C_ctl: CellAutomaton
    f: C_ctl.Q → Option C_inr.Q

  variable (e: Params)

  structure Q1 where
    state: e.C_ctl.Q
    counter: Fin 3

  def C': CellAutomaton := {
    Q := Option (Q1 e × e.C_inr.Q)
    δ := fun a b c =>
      match (a, b, c) with
      | (some qa, some qb, some qc) =>
        if qb.counter = 2
        then sorry
        else some {
          state := qb.state
          counter := Fin.succ 0
        }
      | _ => none
    decQ := sorry
    finQ := sorry
  }

  variable (c_ctl: Config e.C_ctl.Q)
  variable (c_inr: Config e.C_inr.Q)
  variable (h_CM: ∀ (t: ℕ) (p: ℤ),
    e.f (e.C_ctl.nextt c_ctl t p) =
      if t = 3 + 2 * p.natAbs then some (c_inr p)
      else none
  )

  def to_C'Q: e.C_ctl.Q → (C' e).Q := sorry
  def to_CinrQ: (C' e).Q → e.C_inr.Q := sorry

  theorem spec: ∀ (t: ℕ) (p: ℤ),
    let c' := (to_C'Q e) ∘ c_ctl
    let proj := to_CinrQ e;
    let C' := C' e
    proj (C'.nextt c' (3 + 3 * t) 0) = e.C_inr.nextt c_inr t 0 := by
      sorry

end simulation







namespace backwards_fsm
  variable [Alphabet α] [Alphabet β] [Alphabet γ]

  structure Params where
    {α: Type}
    [inst1: Alphabet α]
    {β: Type}
    [inst2: Alphabet β]
    {γ: Type}
    [inst3: Alphabet γ]
    M: FiniteStateTransducer α β
    C: CArtTransducer β γ

  instance (e : Params) : Alphabet e.α := e.inst1
  instance (e : Params) : Alphabet e.β := e.inst2
  instance (e : Params) : Alphabet e.γ := e.inst3
  variable (e: Params)

  instance [Alphabet α] [Alphabet β] : Alphabet (α × β) := inferInstance
  instance [Alphabet α] [Alphabet β] : Alphabet (α → β) := sorry

  def C': CArtTransducer e.α (e.α × (e.M.Q → e.C.Q)) := {
    Q := e.α × (e.M.Q → e.C.Q)
    decQ := sorry
    finQ := sorry
    δ := sorry
    border := sorry
    embed := sorry
    f := id
  }

  def M' : FiniteStateTransducer (e.α × (e.M.Q → e.C.Q)) e.γ := {
    Q := (e.M.Q × e.C.Q)
    δ := fun (m_q, _) (a, f) => (e.M.δ m_q a, f (e.M.δ m_q a)),
    q0 := (e.M.q0, e.C.border),
    f := fun (_, c_q) => e.C.f c_q,
  }

  theorem spec: (M' e).advice.f ∘ (C' e).advice.f = e.C.advice.f ∘ e.M.advice.f :=
    by
    sorry

  theorem spec2
    {α: Type}
    [inst1: Alphabet α]
    {β: Type}
    [inst2: Alphabet β]
    {γ: Type}
    [inst3: Alphabet γ]
    {M: FiniteStateTransducer α β}
    {C: CArtTransducer β γ}:
      C.advice.f ∘ M.advice.f = let e: Params := ⟨M, C⟩; (M' e).advice.f ∘ (C' e).advice.f :=
    by
    sorry

end backwards_fsm



def CArtTransducer.compose [Alphabet α] [Alphabet β] [Alphabet γ] (t1: CArtTransducer β γ) (t2: CArtTransducer α β):
    CArtTransducer α γ :=
  sorry

def TwoStageAdvice.from_transducers [Alphabet α] [Alphabet β] [Alphabet γ] (M: FiniteStateTransducer β γ) (C: CArtTransducer α β): TwoStageAdvice α γ :=
  TwoStageAdvice.mk C.toLCellAutomaton (M.map_input C.f)

lemma TwoStageAdvice.from_transducers_eq [Alphabet α] [Alphabet β] [Alphabet γ] (M: FiniteStateTransducer β γ) (C: CArtTransducer α β):
    (TwoStageAdvice.from_transducers M C).advice.f = M.advice.f ∘ C.advice.f := by
  sorry


def compose_two_stage [Alphabet α] [Alphabet Γ1] [Alphabet Γ] (a1: TwoStageAdvice α Γ1) (a2: TwoStageAdvice Γ1 Γ):
    TwoStageAdvice α Γ :=
  let e := backwards_fsm.Params.mk a1.M a2.cart_transducer
  let ca_new := (backwards_fsm.C' e).compose a1.cart_transducer
  let fsm_new := a2.M.compose (backwards_fsm.M' e)
  TwoStageAdvice.from_transducers fsm_new ca_new



lemma foo1 [Alphabet α] [Alphabet Γ1] [Alphabet Γ] (t1: TwoStageAdvice α Γ1) (t2: TwoStageAdvice Γ1 Γ):
    (t2.advice.f) ∘ (t1.advice.f) = (t2.M.advice.f) ∘ (t2.cart_transducer.advice.f) ∘ (t1.M.advice.f) ∘ (t1.cart_transducer.advice.f) := by
    sorry


lemma foo2 [Alphabet α] [Alphabet Γ1] [Alphabet Γ] (t1: TwoStageAdvice α Γ1) (t2: TwoStageAdvice Γ1 Γ):
    let e := backwards_fsm.Params.mk t1.M t2.cart_transducer
    (t2.M.advice.f) ∘ (t2.cart_transducer.advice.f) ∘ (t1.M.advice.f) ∘ (t1.cart_transducer.advice.f) =
    (t2.M.advice.f) ∘ (backwards_fsm.M' e).advice.f ∘ (backwards_fsm.C' e).advice.f ∘ (t1.cart_transducer.advice.f)  := by
    sorry



variable [Alphabet Γ'] [Alphabet Γ] [Alphabet α]

lemma TwoStageAdvice.advice_eq2 (t: TwoStageAdvice α Γ):
    t.advice.f = (t.M.advice.f) ∘ (t.cart_transducer.advice.f) := by
    sorry


lemma TwoStageAdvice.advice_eq (t: TwoStageAdvice α Γ):
    t.advice.f = (t.M.advice.f) ∘ (t.cart_transducer.advice.f) := by
    sorry

theorem advice_two_stage_closed_under_composition (a1: TwoStageAdvice α Γ') (a2: TwoStageAdvice Γ' Γ):
    (compose_two_stage a1 a2).advice.f = a2.advice.f ∘ a1.advice.f := by

  rw [Eq.comm]

  let e := backwards_fsm.Params.mk a1.M a2.cart_transducer
  let ca_new := (backwards_fsm.C' e).compose a1.cart_transducer
  let fsm_new := a2.M.compose (backwards_fsm.M' e)

  calc (a2.advice.f ∘ a1.advice.f)
    _ = (a2.M.advice.f ∘ a2.cart_transducer.advice.f) ∘ (a1.M.advice.f ∘ a1.cart_transducer.advice.f) := by
      simp [TwoStageAdvice.advice_eq]

    _ = a2.M.advice.f ∘ (a2.cart_transducer.advice.f ∘ a1.M.advice.f) ∘ a1.cart_transducer.advice.f := by
      simp [Function.comp_assoc]

    _ = a2.M.advice.f ∘ ((backwards_fsm.M' e).advice.f ∘ (backwards_fsm.C' e).advice.f) ∘ a1.cart_transducer.advice.f := by
      simp [backwards_fsm.spec2, e]

    _ = (a2.M.advice.f ∘ (backwards_fsm.M' e).advice.f) ∘ ((backwards_fsm.C' e).advice.f ∘ a1.cart_transducer.advice.f) := by
      simp [Function.comp_assoc]

    _ = fsm_new.advice.f ∘ ca_new.advice.f := by
      simp [ca_new, fsm_new]
      sorry

    _ = (TwoStageAdvice.from_transducers fsm_new ca_new).advice.f := by sorry
    _ = (compose_two_stage a1 a2).advice.f := by sorry
