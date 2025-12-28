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

namespace CellularAutomatas
variable [Alphabet α] [Alphabet Γ]

axiom advice_two_stage_closed_under_composition [Alphabet Γ'] (a1: TwoStageAdvice α Γ') (a2: TwoStageAdvice Γ' Γ):
  ∃ a: TwoStageAdvice α Γ, a.advice.f = a2.advice.f ∘ a1.advice.f

lemma ℒ_oca_def (adv: Advice α Γ) (L: Language α):
        L ∈ ℒ (CA_rt (α × Γ) + adv) ↔ ∃ C ∈ CA_rt (α × Γ), L = { w | (w ⊗ (adv.f w)) ∈ C.L } := by
    simp [ℒ, tCellAutomatonWithAdvice.with_advice, tCellAutomatonWithAdvice.L, Advice.annotate]

lemma ℒ_tCellAutomaton_def (L: Language α):
        L ∈ ℒ (CA_rt α) ↔ ∃ C ∈ CA_rt α, C.L = L := by
    simp [ℒ]

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
    ext w
    simp [tCellAutomaton.L, tCellAutomaton.map_alphabet, LCellAutomaton.comp, LCellAutomaton.embed_word, CellAutomaton.nextt, apply_iterated]
    congr 1
    apply congr_arg
    funext i
    simp [LCellAutomaton.embed_word]
    split_ifs
    · simp
    · simp at *
      rw [Word.range] at *
      simp at *
      omega

@[simp]
lemma zip_advice_first (w: Word α) (v: Word Γ) (h: w.length = v.length):
        (w ⊗ v).map Prod.fst = w := by
    induction w generalizing v with
    | nil =>
      cases v
      · simp [tensor_product]
      · simp at h
    | cons a w ih =>
      cases v with
      | nil => simp at h
      | cons b v =>
        simp only [tensor_product, List.map_cons, Prod.fst, List.zipWith_cons_cons]
        congr
        apply ih
        simp at h
        exact h

@[simp]
lemma zip_advice_second (w: Word α) (v: Word Γ) (h: w.length = v.length):
        (w ⊗ v).map Prod.snd = v := by
    induction w generalizing v with
    | nil =>
      cases v
      · simp [tensor_product]
      · simp at h
    | cons a w ih =>
      cases v with
      | nil => simp at h
      | cons b v =>
        simp only [tensor_product, List.map_cons, Prod.snd, List.zipWith_cons_cons]
        congr
        apply ih
        simp at h
        exact h

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
        ext w
        simp
        rw [zip_advice_first]
        · rw [hC.2]
        · simp [adv.len]
    }
lemma rt_closed_iff (adv: Advice α Γ):
    adv.rt_closed
    ↔ ∀ C ∈ CA_rt (α × Γ), ∃ C' ∈ CA_rt α, C'.L = { w | (w ⊗ (adv.f w)) ∈ C.L }

  := by
    unfold Advice.rt_closed
    constructor
    · intro h C hC
      have : { w | w ⊗ adv.f w ∈ C.L } ∈ ℒ (CA_rt (α × Γ) + adv) := by
        rw [ℒ_oca_def]
        use C, hC
      rw [h] at this
      rw [ℒ_tCellAutomaton_def] at this
      exact this
    · intro h
      apply Set.Subset.antisymm
      · intro L hL
        rw [ℒ_oca_def] at hL
        obtain ⟨C, hC, rfl⟩ := hL
        obtain ⟨C', hC', hL'⟩ := h C hC
        rw [ℒ_tCellAutomaton_def]
        use C', hC', hL'
      · apply CA_rt_subseteq_CA_rt_with_advice

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
  unfold LCellAutomaton.scan_temporal
  unfold tensor_product
  rw [List.zipWith_map_map]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp
    have h_embed : (ProdCA2 C1 C2).embed_word w = fun k => (C1.embed_word w k, C2.embed_word w k) := by
      funext k
      unfold LCellAutomaton.embed_word
      split_ifs <;> rfl
    have h_next : ∀ (c1: Config C1.Q) (c2: Config C2.Q) i,
        (ProdCA2 C1 C2).next (fun n => (c1 n, c2 n)) i = (C1.next c1 i, C2.next c2 i) := by
      intro c1 c2 i
      unfold CellAutomaton.next
      rfl
    have h_iter : ∀ n (c1: Config C1.Q) (c2: Config C2.Q),
        (ProdCA2 C1 C2).nextt (fun n => (c1 n, c2 n)) n = (fun i => (C1.nextt c1 n i, C2.nextt c2 n i)) := by
      intro n c1 c2
      induction n with
      | zero => rfl
      | succ n ih =>
        funext i
        rw [CellAutomaton.nextt, apply_iterated, Nat.iterate_succ']
        dsimp
        rw [ih]
        rw [h_next]
        rfl
    unfold LCellAutomaton.comp
    rw [h_embed]
    rw [h_iter]
    rfl

lemma ParFSM_scanr_step_distrib (M1: FiniteStateMachine α) (M2: FiniteStateMachine β)
    (q1: M1.Q) (q2: M2.Q) (a: α) (b: β) (l1: List M1.Q) (l2: List M2.Q) (h: l1.length = l2.length):
    FiniteStateMachine.scanr_step (M := ParFSM M1 M2) (q1, q2) (a, b) (l1 ⊗ l2) =
    (FiniteStateMachine.scanr_step q1 a l1) ⊗ (FiniteStateMachine.scanr_step q2 b l2) := by
  cases l1 <;> cases l2
  · simp [FiniteStateMachine.scanr_step, tensor_product, ParFSM]
  · simp at h
  · simp at h
  · simp [FiniteStateMachine.scanr_step, tensor_product, ParFSM]

lemma ParFSM_scanr (M1: FiniteStateMachine α) (M2: FiniteStateMachine β) (w: Word (α × β)):
    (ParFSM M1 M2).scanr w = (M1.scanr (w.map Prod.fst)) ⊗ (M2.scanr (w.map Prod.snd)) := by
  unfold FiniteStateMachine.scanr
  unfold FiniteStateMachine.scanr_q
  induction w with
  | nil => simp [ParFSM, tensor_product]
  | cons head tail ih =>
    simp only [List.foldr]
    rw [ih]
    dsimp [ParFSM]
    rw [ParFSM_scanr_step_distrib]
    · rw [FiniteStateMachine.scanr_q_len, FiniteStateMachine.scanr_q_len]
      rw [List.length_map, List.length_map]
    · rfl

lemma TwoStageAdvice.pair_spec [Alphabet Γ1] [Alphabet Γ2]
    (adv1: TwoStageAdvice α Γ1) (adv2: TwoStageAdvice α Γ2):
    (TwoStageAdvice.pair adv1 adv2).advice.f = fun w => (adv1.advice.f w) ⊗ (adv2.advice.f w) := by
  funext w
  simp [TwoStageAdvice.advice, TwoStageAdvice.pair]
  rw [ProdCA2_scan_temporal]
  rw [ParFSM_scanr]
  have h_map_zip : ∀ (l1 : List adv1.M.Q) (l2 : List adv2.M.Q),
    List.map (fun (q1, q2) => (adv1.t q1, adv2.t q2)) (l1 ⊗ l2) = (List.map adv1.t l1) ⊗ (List.map adv2.t l2) := by
    intro l1 l2
    induction l1 generalizing l2
    case nil => simp [tensor_product]
    case cons a l1 ih =>
      cases l2
      case nil => simp [tensor_product]
      case cons b l2 =>
        simp [tensor_product]
        exact ih l2
  erw [h_map_zip]
  simp
  rw [zip_advice_first]
  · rw [zip_advice_second]
    · rfl
    · simp [LCellAutomaton.scan_temporal]
  · simp [LCellAutomaton.scan_temporal]

def OptionAlphabetDef [Alphabet α] : Alphabet (Option α) where
  dec := inferInstance
  fin := inferInstance
  inh := inferInstance

def adv_shift α [Alphabet α]: TwoStageAdvice α α :=
  let M : FiniteStateMachine (Option α) := {
    Q := Option α
    decQ := inferInstance
    finQ := inferInstance
    δ := fun _ a => a
    q0 := default
  }
  {
    C := LcInRt.DiagonalShiftCA α
    M := M
    t := fun q => q.getD default
  }

lemma adv_shift_spec: (adv_shift α).advice.f = fun w => w := by
  funext w
  have h_scanr : (adv_shift α).M.scanr (w.map some) = w.map some := by
    simp [FiniteStateMachine.scanr, FiniteStateMachine.scanr_q]
    induction w with
    | nil => simp
    | cons a w ih =>
      simp [FiniteStateMachine.scanr_step]
      rw [ih]
      simp [adv_shift]
      split
      · simp_all
      · simp_all
  simp [TwoStageAdvice.advice]
  dsimp [adv_shift]
  rw [LcInRt.DiagonalShiftCA_scan_temporal]
  try rw [h_scanr]
  simp
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp
    rw [List.getElem_map]
    simp

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
    (M.scanr w).getLast? = some (M.δ M.q0 (w.getLast (List.ne_nil_of_length_pos h))) := by
  simp [FiniteStateMachine.scanr, FiniteStateMachine.scanr_q]
  induction w with
  | nil => contradiction
  | cons a w ih =>
    simp [FiniteStateMachine.scanr_step]
    cases h_w: w.length with
    | zero =>
      simp at h_w
      subst h_w
      simp
    | succ n =>
      have h_pos : w.length > 0 := by omega
      specialize ih h_pos
      simp
      rw [ih]
      simp

lemma TwoStageAdvice.CA_spec (adv: TwoStageAdvice α Bool):
    (TwoStageAdvice.CA adv).L = TwoStageAdvice.L adv := by
  ext w
  simp [tCellAutomaton.L, TwoStageAdvice.CA, TwoStageAdvice.L]
  cases h: w.length with
  | zero =>
    simp [LCellAutomaton.comp, LCellAutomaton.embed_word]
    simp [TwoStageAdvice.advice]
    unfold LCellAutomaton.scan_temporal
    simp
    unfold FiniteStateMachine.scanr
    unfold FiniteStateMachine.scanr_q
    simp
  | succ n =>
    have h_len : w.length > 0 := by rw [h]; simp
    rw [LcInRt.scan_temporal_get_last]
    simp [h_len]
    unfold TwoStageAdvice.advice
    dsimp
    rw [List.getLast?_map]
    rw [FiniteStateMachine.scanr_last]
    · simp
      congr 1
      congr 1
      rw [LcInRt.scan_temporal_get_last]
      simp [h_len]
    · simp [LCellAutomaton.scan_temporal]
      exact h_len

def CA_rt_to_TwoStage_poly {β: Type} [Alphabet β] (C: tCellAutomaton β) (hC: C ∈ CA_rt β): TwoStageAdvice β Bool := {
  C := C.toLCellAutomaton
  M := {
    Q := C.Q
    decQ := inferInstance
    finQ := inferInstance
    δ := fun _ a => a
    q0 := C.border
  }
  t := C.F_pos
}

theorem advice_two_stage_rt_closed (adv: TwoStageAdvice α Γ):
    adv.advice.rt_closed := by
  rw [rt_closed_iff]
  intro C hC
  let advC := CA_rt_to_TwoStage_poly C hC
  let adv_lifted := adv_lift adv
  obtain ⟨adv_final, h_final⟩ := advice_two_stage_closed_under_composition adv_lifted advC
  let C' := TwoStageAdvice.CA adv_final
  use C'
  constructor
  · simp [TwoStageAdvice.CA]
    simp [CA_rt, t_rt, CA, tCellAutomatons]
  · rw [TwoStageAdvice.CA_spec]
    unfold TwoStageAdvice.L
    rw [h_final]
    simp
    ext w
    simp
    rw [adv_lift_spec]
    simp [advC, CA_rt_to_TwoStage_poly, TwoStageAdvice.advice]
    cases h_w : w.length with
    | zero =>
      simp [LCellAutomaton.comp, LCellAutomaton.embed_word]
      unfold FiniteStateMachine.scanr
      unfold FiniteStateMachine.scanr_q
      simp
      simp [tCellAutomaton.L]
      simp [CA_rt, t_rt] at hC
      rw [hC.2]
      simp
      unfold LCellAutomaton.comp
      unfold LCellAutomaton.embed_word
      simp
    | succ n =>
      have h_len : (w ⊗ adv.advice.f w).length > 0 := by simp [adv.advice.len, h_w]; simp
      unfold TwoStageAdvice.advice
      dsimp
      rw [List.getLast?_map]
      let w' := adv.C.scan_temporal w
      let M := adv.M
      change (M.scanr w').getLast?.map adv.t = some true
      have h_last : (M.scanr w').getLast? = some (M.δ M.q0 (w'.getLast (List.ne_nil_of_length_pos (by simp [w', LCellAutomaton.scan_temporal]; exact h_len)))) := by
        rw [FiniteStateMachine.scanr_last]
        simp [w', LCellAutomaton.scan_temporal]
        exact h_len
      rw [h_last]
      simp
      simp [tCellAutomaton.L]
      simp [CA_rt, t_rt] at hC
      rw [hC.2]
      simp
      congr 1
      rw [LcInRt.scan_temporal_get_last]
      simp [h_len]
      simp [LCellAutomaton.scan_temporal]
      exact h_len
