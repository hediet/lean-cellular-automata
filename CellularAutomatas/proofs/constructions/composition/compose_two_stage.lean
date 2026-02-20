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
import CellularAutomatas.proofs.constructions.composition.compose_cart
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
    have h_fin := M.scanr_get'_eq2 w ⟨ i.toNat, by simp_all [Word.range] ⟩
    rw [←h_fin]
    congr



  -- One-step backward relationship for scanr_reduce:
  -- δ?(q, w.get'?(i)) = scanr_reduce from position i, when q = scanr_reduce from position j ≈ i+1.
  private lemma scanr_reduce_step (w: Word e.α) (i j: ℤ)
      {q: e.M.Q} (h_q : q = e.M.scanr_reduce w⟦j.toNat..*⟧) (h_j : j.toNat = (i + 1).toNat) :
      e.M.δ? q (w.get'? i) = e.M.scanr_reduce w⟦i.toNat..*⟧ := by
    conv => rhs; rw [FiniteStateTransducer.scanr_reduce'?]
    rw [show (i + 1).toNat = j.toNat from h_j.symm, ← h_q]

  -- The key invariant: at each time step t and position p,
  -- .1 propagates the original input word rightward (tracking w at p+t), and
  -- .2 is a function M.Q → C.Q that parametrically simulates C for every FSM state.
  lemma inv (w: Word e.α) (t: ℕ) (p: ℤ):
      let c' := (C' e).nextt w t p
      let q := e.M.scanr_reduce w⟦(p+t).toNat..*⟧
      c'.2 q = (e.C.nextt (e.M.scanr w) t p)
      ∧ c'.1 = w.get'? (p + t) := by

    induction t generalizing p with
    | zero =>
      simp only [Nat.cast_zero, add_zero, CellAutomaton.nextt, Function.iterate_zero, id_eq, C', Word.get'?, Word.range]
      by_cases h : p ∈ w.range
      · have hr : p ∈ (e.M.scanr w).range := by simp [h]
        simp only [embed_word_at_eq1 w p h, embed_word_at_eq1 (e.M.scanr w) p hr, scanr_get'_eq2 w p h]
        simp_all [Word.range]
      · simp_all [embed_word_at_eq2, Word.range]

    | succ t ih =>
      -- Unfold one step: nextt (t+1) = next (nextt t)
      set c' := (C' e).nextt w (t + 1) p with h_c'
      set q := e.M.scanr_reduce w⟦(p + ↑(t+1)).toNat..*⟧ with h_q
      rw [CellAutomaton.nextt_succ] at h_c'
      set cell := ((C' e).nextt w t) with h_cell
      unfold CellAutomaton.next at h_c'

      -- The three neighbor cells at time t
      set left := (cell (p - 1)) with h_left
      set center := (cell p) with h_center
      set right := (cell (p + 1)) with h_right

      -- c'.2 q unfolds via C'.δ: step FSM backwards (right→center→left), then apply C.δ
      simp [C'] at h_c'
      rw [h_c']
      simp

      -- FSM states: q steps backwards through positions p+t+1 → p+t → p-1+t
      set fsm_center := e.M.δ? q center.1
      set fsm_left := e.M.δ? fsm_center left.1

      -- Right neighbor: connect IH's FSM state to q
      have fsm_at_right_eq : e.M.scanr_reduce w⟦(p + 1 + ↑t).toNat..*⟧ = q := by
        have : (p + 1 + ↑t).toNat = (p + (↑t + 1)).toNat := by omega
        simp [this, q]
      have ih_right := ih (p + 1)
      rw [fsm_at_right_eq] at ih_right
      simp at ih_right

      have sim_right : right.2 q = e.C.nextt (e.M.scanr w) t (p + 1) := by
        simp [h_right, ih_right]

      have word_right : right.1 = (w.get'? (p + ↑t + 1)) := by
        simp [h_right, ih_right]
        grind

      -- Center: word tracking → FSM step → simulation
      have word_center : center.1 = (w.get'? (p + ↑t)) := by
        have ih_c := ih p
        simp [ih_c, center]

      have fsm_center_eq : fsm_center = e.M.scanr_reduce w⟦(p + ↑t).toNat..*⟧ := by
        simp only [fsm_center]
        rw [word_center]
        exact scanr_reduce_step e w (p + ↑t) (p + ↑(t+1)) h_q (by omega)

      have sim_center : (center.2 fsm_center) = e.C.nextt (e.M.scanr w) t p := by
        have ih_c := ih p
        rw [fsm_center_eq]
        simp [center, ih_c]

      -- Left neighbor: word tracking → FSM step → simulation
      have word_left : left.1 = (w.get'? (p + ↑t - 1)) := by
        have ih_l := ih (p - 1)
        grind

      have fsm_left_eq : fsm_left = e.M.scanr_reduce w⟦(p - 1 + ↑t).toNat..*⟧ := by
        simp only [fsm_left]
        rw [word_left, show p + ↑t - 1 = p - 1 + ↑t from by ring]
        exact scanr_reduce_step e w (p - 1 + ↑t) (p + ↑t) fsm_center_eq (by omega)

      have sim_left : (left.2 fsm_left) = e.C.nextt (e.M.scanr w) t (p - 1) := by
        have ih_l := ih (p - 1)
        rw [fsm_left_eq]
        simp [h_left, ih_l]

      -- Combine: C'.δ applies C.δ to the three simulated neighbors
      constructor
      · simp [sim_right, sim_center, sim_left, CellAutomaton.next]
      · dsimp
        change (cell (p+1)).1 = _
        rw [← h_right, word_right]
        congr 1
        omega



  -- spec_ proves the functional equation for the backwards FSM construction:
  -- composing M' after C' equals composing C.advice after M.advice.
  lemma spec_: (M' e).advice ∘ (C' e).advice = e.C.advice ∘ e.M.advice := by
      funext w
      unfold FiniteStateTransducer.advice
      simp [CArtTransducer.advice, M', backwards_fsm.M_join_spec e.C.Q]

      set c' := (C' e).trace_rt w with eq_c'
      apply List.ext_getElem
      · simp_all

      intro i h1 h2
      simp

      -- The first projection of c' recovers the original word w
      have h_w : Word.fst c' = w := by
        apply List.ext_getElem
        · simp_all
        intro t ht1 ht2
        simp [eq_c', CellAutomaton.trace_rt, CellAutomaton.trace, comp_word_eq_project_nextt]
        have h_word_track := (inv e w t 0).2
        conv in (CellAutomaton.project (C' e)) => simp [C']
        simp [h_word_track]
        rw [Word.get'_eq]

      simp [h_w]
      simp [eq_c', CellAutomaton.trace_rt, CellAutomaton.trace, comp_word_eq_project_nextt]
      congr

      have h_inv := inv e w i 0
      simp at h_inv
      conv in (CellAutomaton.project (C' e)) => simp [C']
      simp
      rw [h_inv.1]



  theorem spec {α β γ: Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    {M: FiniteStateTransducer α β}
    {C: CArtTransducer β γ}:
      C.advice ∘ M.advice = (M' ⟨M, C⟩).advice ∘ (C' ⟨M, C⟩).advice :=
    by grind only [!spec_]

end backwards_fsm



def TwoStageAdvice.from_transducers {β: Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (M: FiniteStateTransducer β γ) (C: CArtTransducer α β): TwoStageAdvice α γ :=
  { C := C, β := β, M := M }

lemma TwoStageAdvice.from_transducers_eq {β: Type} [Alphabet α] [Alphabet β] [Alphabet γ] (M: FiniteStateTransducer β γ) (C: CArtTransducer α β):
    (TwoStageAdvice.from_transducers M C).advice = M.advice ∘ C.advice := by rfl


def compose_two_stage [Alphabet α] [Alphabet Γ1] [Alphabet Γ] (a2: TwoStageAdvice Γ1 Γ) (a1: TwoStageAdvice α Γ1):
    TwoStageAdvice α Γ :=
  let e := backwards_fsm.Params.mk a1.M a2.C
  let ca_new := (backwards_fsm.C' e) ⊚ a1.C
  let fst_new := a2.M ⊚ backwards_fsm.M' e
  TwoStageAdvice.from_transducers fst_new ca_new

variable [Alphabet Γ'] [Alphabet Γ] [Alphabet α]

lemma TwoStageAdvice.advice_eq (t: TwoStageAdvice α Γ):
    t.advice = t.M.advice ∘ t.C.advice := by
    simp [TwoStageAdvice.advice, FiniteStateTransducer.advice, CArtTransducer.advice]

infixr:90 "⊚"  => compose_two_stage


@[simp]
theorem compose_two_stage_spec (a1: TwoStageAdvice α Γ') (a2: TwoStageAdvice Γ' Γ):
    (a2 ⊚ a1).advice = a2.advice ∘ a1.advice := by

  rw [Eq.comm]

  let e := backwards_fsm.Params.mk a1.M a2.C
  let ca_new := (backwards_fsm.C' e) ⊚ a1.C
  let fsm_new := a2.M ⊚ backwards_fsm.M' e

  calc (a2.advice ∘ a1.advice)
    _ = (a2.M.advice ∘ a2.C.advice) ∘ (a1.M.advice ∘ a1.C.advice) := by
      simp [TwoStageAdvice.advice_eq]

    _ = a2.M.advice ∘ (a2.C.advice ∘ a1.M.advice) ∘ a1.C.advice := by
      simp [Function.comp_assoc]

    _ = a2.M.advice ∘ ((backwards_fsm.M' e).advice ∘ (backwards_fsm.C' e).advice) ∘ a1.C.advice := by
      simp [backwards_fsm.spec, e]

    _ = (a2.M.advice ∘ (backwards_fsm.M' e).advice) ∘ ((backwards_fsm.C' e).advice ∘ a1.C.advice) := by
      simp [Function.comp_assoc]

    _ = fsm_new.advice ∘ ca_new.advice := by
      rw [CArtTransducer.compose_trace_rt_advice_spec]
      rw [FiniteStateTransducer.compose_spec]

    _ = (TwoStageAdvice.from_transducers fsm_new ca_new).advice := by simp [TwoStageAdvice.from_transducers_eq]
    _ = (a2 ⊚ a1).advice := by rfl
