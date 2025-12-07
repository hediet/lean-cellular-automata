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

variable [Alphabet α] [Alphabet Γ]

axiom advice_two_stage_closed_under_composition [Alphabet Γ'] (a1: TwoStageAdvice α Γ') (a2: TwoStageAdvice Γ' Γ):
  ∃ a: TwoStageAdvice α Γ, a.advice.f = a2.advice.f ∘ a1.advice.f

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
lemma rt_closed_iff (adv: Advice α Γ):
    adv.rt_closed
    ↔ ∀ C ∈ CA_rt (α × Γ), ∃ C' ∈ CA_rt α, C'.L = { w | (w ⊗ (adv.f w)) ∈ C.L }

  := sorry

def ProdCA2 (C1: LCellAutomaton α) (C2: LCellAutomaton α): LCellAutomaton α := {
  Q := C1.Q × C2.Q
  δ := fun (l1, l2) (c1, c2) (r1, r2) => (C1.δ l1 c1 r1, C2.δ l2 c2 r2)
  embed := fun a => (C1.embed a, C2.embed a)
  border := (C1.border, C2.border)
}

def ParFSM (M1: FiniteStateMachine α) (M2: FiniteStateMachine β): FiniteStateMachine (α × β) := {
  Q := M1.Q × M2.Q
  δ := fun (q1, q2) (a, b) => (M1.δ q1 a, M2.δ q2 b)
  q0 := (M1.q0, M2.q0)
}

def TwoStageAdvice.pair [Alphabet Γ1] [Alphabet Γ2]
    (adv1: TwoStageAdvice α Γ1) (adv2: TwoStageAdvice α Γ2): TwoStageAdvice α (Γ1 × Γ2) := {
  C := ProdCA2 adv1.C adv2.C
  M := ParFSM adv1.M adv2.M
  t := fun (q1, q2) => (adv1.t q1, adv2.t q2)
}

lemma List.zipWith_map_map {α β γ δ ε : Type _} (f : α → β → γ) (g : δ → α) (h : ε → β) (l1 : List δ) (l2 : List ε) :
  List.zipWith f (l1.map g) (l2.map h) = List.zipWith (fun x y => f (g x) (h y)) l1 l2 := by
  induction l1 generalizing l2 <;> cases l2 <;> simp [*]

lemma ProdCA2_scan_temporal (C1: LCellAutomaton α) (C2: LCellAutomaton α) (w: Word α):
    (ProdCA2 C1 C2).scan_temporal w = (C1.scan_temporal w) ⊗ (C2.scan_temporal w) := by
  sorry

lemma ParFSM_scanr (M1: FiniteStateMachine α) (M2: FiniteStateMachine β) (w: Word (α × β)):
    (ParFSM M1 M2).scanr w = (M1.scanr (w.map Prod.fst)) ⊗ (M2.scanr (w.map Prod.snd)) := by
  sorry

lemma zip_advice_second (w: Word α) (v: Word Γ) (h: w.length = v.length):
        (w ⊗ v).map Prod.snd = v := by
  sorry

lemma TwoStageAdvice.pair_spec [Alphabet Γ1] [Alphabet Γ2]
    (adv1: TwoStageAdvice α Γ1) (adv2: TwoStageAdvice α Γ2):
    (TwoStageAdvice.pair adv1 adv2).advice.f = fun w => (adv1.advice.f w) ⊗ (adv2.advice.f w) := by
  sorry

def OptionAlphabetDef [Alphabet α] : Alphabet (Option α) where
  dec := inferInstance
  fin := inferInstance
  inh := inferInstance

def adv_shift α [Alphabet α]: TwoStageAdvice α α :=
  let M : FiniteStateMachine (Option α) := {
    Q := Option α
    decQ := inferInstance
    finQ := inferInstance
    δ := fun _ _ => default
    q0 := default
  }
  {
    C := LcInRt.DiagonalShiftCA α
    M := M
    t := fun q => q.getD default
  }

lemma adv_shift_spec: (adv_shift α).advice.f = fun w => w := by
  sorry

def adv_lift (adv: TwoStageAdvice α Γ): TwoStageAdvice α (α × Γ) :=
  TwoStageAdvice.pair (adv_shift α) adv

lemma adv_lift_spec (adv: TwoStageAdvice α Γ):
    (adv_lift adv).advice.f = fun w => w ⊗ (adv.advice.f w) := by
  simp [adv_lift]
  rw [TwoStageAdvice.pair_spec]
  simp [adv_shift_spec]


def TwoStageAdvice.L (adv: TwoStageAdvice α Bool) := { w | (adv.advice.f w).getLast? = some true }

def TwoStageAdvice.CA (adv: TwoStageAdvice α Bool): tCellAutomaton α := {
  Q := adv.C.Q
  δ := adv.C.δ
  border := adv.C.border
  embed := adv.C.embed
  F_pos := fun q => adv.t (adv.M.δ adv.M.q0 q)
  t := fun n => n - 1
  p := fun _ => 0
}

lemma FiniteStateMachine.scanr_last (M: FiniteStateMachine α) (w: Word α) (h: w.length > 0):
    (M.scanr w)[w.length - 1]? = some (M.δ M.q0 (w[w.length - 1]'(by omega))) := by
  sorry

lemma TwoStageAdvice.CA_spec (adv: TwoStageAdvice α Bool):
    (TwoStageAdvice.CA adv).L = TwoStageAdvice.L adv := by
  sorry

theorem advice_two_stage_rt_closed (adv: TwoStageAdvice α Γ):
    adv.advice.rt_closed := by
  sorry
