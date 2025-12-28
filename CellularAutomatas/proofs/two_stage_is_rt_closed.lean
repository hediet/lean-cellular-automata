import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import CellularAutomatas.defs
import CellularAutomatas.proofs.composition
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.advice_two_stage_closed_under_composition

namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

open FiniteStateTransducer (M_map M_prod M_projQ M_id)
open CellAutomaton


def prefix_mem (L: Language α) [DecidablePred L] (w: Word α): Word Bool :=
  (List.range w.length).map (fun i => decide (L (w⟦0..i+1⟧)))

@[simp]
lemma prefix_mem_len {α} (L: Language α) [DecidablePred L] (w: Word α):
  (prefix_mem L w).length = w.length := by
  simp [prefix_mem]

def prefix_mem_adv (L: Language α) [DecidablePred L]: Advice α Bool := { f := prefix_mem L }

def lift {α β} [Alphabet α] [Alphabet β]
    (f: Word α → Word β) (L: Language α): Language β :=
  { w: Word β | ∃ v: Word α, f v = w ∧ L v }










variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]

def CA_rt_to_TwoStage (C: CA_rt α): TwoStageAdvice α Bool :=
  {
    β := Bool
    C := C.val.toCellAutomaton
    M := FiniteStateTransducer.M_id Bool
  }

lemma CA_rt_to_TwoStage_advice_eq (C: CA_rt α) :
  (CA_rt_to_TwoStage C).advice.f = C.val.trace_rt := by
  funext w
  simp [CA_rt_to_TwoStage, TwoStageAdvice.advice]

lemma CA_rt_to_TwoStage_eq (C: CA_rt α):
  (CA_rt_to_TwoStage C).advice.f = (Advice.prefixes_in_L C.val.L).f := by
  rw [CA_rt_to_TwoStage_advice_eq]
  funext w
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have (v: Bool) (p: Prop) [Decidable p]: (v = decide p ↔ (v = true ↔ p)) := by grind
    simp [Advice.prefixes_in_L, this, trace_rt_getElem_i_iff]
    rfl


theorem advice_prefixes_in_L_is_two_stage_advice (C: CA_rt α):
    (Advice.prefixes_in_L C.val.L).is_two_stage_advice := by
  use CA_rt_to_TwoStage C
  have h_eq := CA_rt_to_TwoStage_eq C
  match (CA_rt_to_TwoStage C).advice, (Advice.prefixes_in_L C.val.L), h_eq with
  | ⟨f1, l1⟩, ⟨f2, l2⟩, h =>
    simp at h
    subst h
    rfl



noncomputable def get_ca (L: ℒ (CA_rt α)): CA_rt α := by
  have := L.prop
  rw [ℒ_CA_rt_iff] at this
  exact ⟨ Classical.choose this, by simp [Classical.choose_spec this] ⟩


noncomputable def prefix_mem_two_stage (L: ℒ (CA_rt α)): TwoStageAdvice α Bool :=
  CA_rt_to_TwoStage (get_ca L)

def prefix_mem_two_stage_spec (L: ℒ (CA_rt α)) [DecidablePred L.val]:
    (prefix_mem_two_stage L).advice.f = prefix_mem L.val := by
  sorry

lemma advice_eq_iff {α β: Type} (adv1 adv2: Advice α β) (h: adv1.f = adv2.f): adv1 = adv2 := by
  cases adv1
  cases adv2
  simp at h
  subst h
  rfl


lemma L_rt_iff_prefix_mem_two_stage (L: Language α) [DecidablePred L]:
    L ∈ ℒ (CA_rt α) ↔ (prefix_mem_adv L).is_two_stage_advice := by
  constructor
  · intro h
    use prefix_mem_two_stage (⟨L, h⟩ : ℒ (CA_rt α))
    apply advice_eq_iff
    simp [prefix_mem_adv, prefix_mem_two_stage_spec]
  · intro h
    rw [ℒ_CA_rt_iff]
    sorry


-- classical

def ca_to_two_stage (C: CArtTransducer α Γ): TwoStageAdvice α Γ :=
  {
    β := Γ
    C := C
    M := FiniteStateTransducer.M_id Γ
  }


def zip_two_stage [Alphabet α] [Alphabet β] [Alphabet γ] (a1: TwoStageAdvice α β) (a2: TwoStageAdvice α γ):
    TwoStageAdvice α (β × γ) :=
  let ca_new := a1.C ⨂ a2.C
  let fst_new := a1.M ⨂ a2.M
  TwoStageAdvice.from_transducers fst_new ca_new

infixl:65 " ⨂ " => zip_two_stage

noncomputable def A (adv: TwoStageAdvice α Γ) (L: Language α): TwoStageAdvice α Bool :=
  (prefix_mem_two_stage ⟨(lift adv.advice.annotate L), sorry⟩) ⊚ ((ca_to_two_stage (ca_id_word α)) ⨂ adv)

lemma A_spec (adv: TwoStageAdvice α Γ) (L: Language α) [DecidablePred L]:
    (A adv L).advice = prefix_mem_adv L := by
  apply advice_eq_iff
  funext w
  simp [A, TwoStageAdvice.advice]
  sorry

lemma rt_closed_iff (adv: Advice α Γ):
    adv.rt_closed ↔ (∀ L, (lift adv.annotate L) ∈ ℒ (CA_rt (α × Γ)) → L ∈ ℒ (CA_rt α)) := by

  unfold Advice.rt_closed
  unfold adviceAdd
  conv in (ℒ (CA_rt (α ⨉ Γ) + adv) ) =>
    change L ∈ tCellAutomatonWithAdvice.with_advice (CA_rt (α × Γ)) adv

  sorry


theorem two_stage_rt_closed (adv: TwoStageAdvice α Γ):
    adv.advice.rt_closed := by
  open Classical in -- I'm quite sure this is not needed

  suffices ∀ (L : Language α) (h: lift adv.advice.annotate L ∈ ℒ (CA_rt (α ⨉ Γ))), L ∈ ℒ (CA_rt α) from by
    simp_all [rt_closed_iff]

  intro L h

  suffices ∃ ts_adv: TwoStageAdvice α Bool, ts_adv.advice = prefix_mem_adv L from by
    simp_all [L_rt_iff_prefix_mem_two_stage, Advice.is_two_stage_advice]

  use A adv L
  simp [A_spec adv]
