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
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.constructions.composition.compose_two_stage
import CellularAutomatas.proofs.constructions.basic_mark_border
import CellularAutomatas.proofs.constructions.cart_fix_empty_word

namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

open FiniteStateTransducer (M_map M_prod M_projQ M_id)
open CellAutomaton


variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]


@[simp]
lemma word_to_config_empty {α} [Alphabet α] :
    word_to_config (α := α) [] = fun _ => none := by
  funext i
  simp [word_to_config]

@[simp]
lemma embed_word_p_not_in_range {α} [Alphabet α] (w: Word α) {C: CellAutomaton α？ β} (p: ℤ) (h: p ∉ w.range):
    (embed_word (C := C) w) p = C.embed none := by
  unfold embed_word word_to_config embed_config
  have :  ¬ (0 ≤ p ∧ p < ↑(List.length w)) := by grind [Word.range]
  simp [this]


@[simp]
lemma embed_word_p_in_range {α} [Alphabet α] (w: Word α) {C: CellAutomaton α？ β} (p: ℤ) (h: p ∈ w.range):
    (embed_word (C := C) w) p = C.embed (w[p.toNat]'(by grind [Word.range])) := by
  unfold embed_word word_to_config embed_config
  have :  (0 ≤ p ∧ p < ↑(List.length w)) := by grind [Word.range]
  simp [this]





def ca_to_two_stage (C: CArtTransducer α Γ): TwoStageAdvice α Γ :=
  {
    β := Γ
    C := C
    M := FiniteStateTransducer.M_id Γ
  }

@[simp]
lemma ca_to_two_stage_spec (C: CArtTransducer α Γ):
    (ca_to_two_stage C).advice = C.trace_rt := by
  funext w
  simp [ca_to_two_stage, TwoStageAdvice.advice]

lemma ca_to_two_stage_advice_eq (C: CArtTransducer α Γ):
    (ca_to_two_stage C).advice = C.advice := by
  apply advice_eq_iff
  simp [CArtTransducer.advice]

lemma Advice.is_cart_advice.is_two_stage {adv: Advice α Γ} (h: adv.is_cart_advice): adv.is_two_stage_advice :=
  let ⟨C, hC⟩ := h
  ⟨ca_to_two_stage C, ca_to_two_stage_advice_eq C ▸ hC⟩




def zip_two_stage [Alphabet α] [Alphabet β] [Alphabet γ] (a1: TwoStageAdvice α β) (a2: TwoStageAdvice α γ):
    TwoStageAdvice α (β × γ) :=
  let ca_new := a1.C ⨂ a2.C
  let fst_new := a1.M ⨂ a2.M
  TwoStageAdvice.from_transducers fst_new ca_new

@[simp]
def zip_spec [Alphabet α] [Alphabet β] [Alphabet γ] (a1: TwoStageAdvice α β) (a2: TwoStageAdvice α γ):
    (zip_two_stage a1 a2).advice.f w = (a1.advice w ⨂ a2.advice w) := by
  simp [zip_two_stage, TwoStageAdvice.advice, TwoStageAdvice.from_transducers]

infixl:65 " ⨂ " => zip_two_stage








lemma advice_rt_closed_iff (adv: Advice α Γ):
    adv.rt_closed ↔ (∀ (C : CA_rt (α ⨉ Γ)), {w | w ⨂ adv w ∈ C.val.L} ∈ ℒ (CA_rt α)) := by
  unfold Advice.rt_closed
  rw [subset_antisymm_iff]
  simp only [CA_rt_subseteq_CA_rt_with_advice adv, and_true]
  rw [Set.subset_def]
  simp [ℒ_oca_def]
  grind

lemma tCellAutomatonWithAdvice.L_mem_ℒ (C: CA_rt (α × Γ)) (adv: Advice α Γ): (C.val + adv).L ∈ ℒ (CA_rt (α ⨉ Γ) + adv) := by
  unfold ℒ
  simp only [HAdd.hAdd, Set.mem_setOf_eq, DefinesLanguage.L, exists_exists_and_eq_and]
  use C
  simp

lemma tCellAutomatonWithAdvice.exists_CA_rt_of_rt_closed {adv: Advice α Γ} (h: adv.rt_closed) (C: CA_rt (α ⨉ Γ)):
    ∃ (C' : CA_rt α), C'.val.L = (C.val + adv).L := by
  have : (C.val + adv).L ∈ ℒ (CA_rt α) := by
    unfold Advice.rt_closed at h
    rw [←h]
    exact tCellAutomatonWithAdvice.L_mem_ℒ C adv

  rw [ℒ_CA_rt_iff] at this
  simp [this]



def TwoStageAdvice.L {α} [Alphabet α] (adv: TwoStageAdvice α Bool): Language α :=
  { w: Word α | (adv.advice w).getLast? = true }


def TwoStageAdvice.to_CA_rt {α} [Alphabet α] (adv: TwoStageAdvice α Bool): CA_rt α :=
  fix_empty false (toRtCa $ adv.C.map_project (fun q => adv.M.f (adv.M.δ adv.M.q0 q)))



@[simp]
lemma TwoStageAdvice.to_CA_rt_L {α} [Alphabet α] (adv: TwoStageAdvice α Bool):
    adv.to_CA_rt.val.L = adv.L := by
  ext w

  unfold TwoStageAdvice.to_CA_rt

  by_cases h: w = []
  · unfold TwoStageAdvice.L
    rw [Set.mem_setOf_eq]
    simp [h]

  unfold TwoStageAdvice.L
  rw [Set.mem_setOf_eq]

  simp [h]
  rw [←trace_rt_L h]
  unfold TwoStageAdvice.advice
  simp

  erw [←FiniteStateTransducer.getLast?_of_scanr]
  grind




def TwoStageAdvice.from_CA_rt {α} [Alphabet α] (C: CA_rt α): TwoStageAdvice α Bool :=
  {
    β := Bool
    C := C.val.toCellAutomaton
    M := FiniteStateTransducer.M_id Bool
  }

@[simp]
lemma TwoStageAdvice.from_CA_rt_spec {α} [Alphabet α] (C: CA_rt α):
    (TwoStageAdvice.from_CA_rt C).advice = C.val.trace_rt := by
  funext w
  simp [TwoStageAdvice.from_CA_rt, TwoStageAdvice.advice]


@[simp]
lemma zip_left_empty {α} {v: Word β}: ([]: Word α) ⨂ v = [] := by simp [List.zip]

@[simp]
lemma zip_right_empty {α} {v: Word β}: v ⨂ ([]: Word α) = [] := by simp [List.zip]

@[simp]
lemma zip_empty_iff {α β} {v1: Word α} {v2: Word β}:
    v1 ⨂ v2 = [] ↔ v1 = [] ∨ v2 = [] := by simp [List.zip]


end CellularAutomatas
