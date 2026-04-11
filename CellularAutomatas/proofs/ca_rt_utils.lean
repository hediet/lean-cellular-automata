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
    C.embed_config w p = C.embed none := by
  unfold CellAutomaton.embed_config word_to_config
  have :  ¬ (0 ≤ p ∧ p < ↑(List.length w)) := by grind [Word.range]
  simp [this]


@[simp]
lemma embed_word_p_in_range {α} [Alphabet α] (w: Word α) {C: CellAutomaton α？ β} (p: ℤ) (h: p ∈ w.range):
    C.embed_config w p = C.embed (w[p.toNat]'(by grind [Word.range])) := by
  unfold CellAutomaton.embed_config word_to_config
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

lemma tCellAutomatonWithAdvice.L_mem_ℒ (C: CA_rt (α × Γ)) (adv: Advice α Γ): (C.val + adv).L ∈ ℒ (CA_rt (α ⨉ Γ) + adv) := by
  unfold ℒ
  simp only [HAdd.hAdd, Set.mem_setOf_eq, DefinesLanguage.L, exists_exists_and_eq_and]
  use C
  simp

/-- Convert structure-based `weak_rt_closed` to the Prop-level language equality. -/
lemma Advice.WeakRtClosed.language_eq {adv: Advice α Γ} (h: adv.weak_rt_closed):
    ℒ (CA_rt (α × Γ) + adv) = ℒ (CA_rt α) := by
  ext L
  simp only [ℒ_oca_def]
  constructor
  · rintro ⟨C, hC, hL⟩
    exact ⟨(h.map ⟨C, hC⟩).val, (h.map ⟨C, hC⟩).prop, hL ▸ (h.spec ⟨C, hC⟩).symm⟩
  · intro hL
    rw [CA_rt_subseteq_CA_rt_with_advice adv] at hL
    exact hL

/-- Convert the Prop-level language equality to the structure-based `weak_rt_closed`.
    This direction requires `Classical.choice`. -/
noncomputable def Advice.WeakRtClosed.of_language_eq {adv: Advice α Γ}
    (h: ℒ (CA_rt (α × Γ) + adv) = ℒ (CA_rt α)): adv.weak_rt_closed where
  map C := by
    have : (C.val + adv).L ∈ ℒ (CA_rt α) := by
      rw [←h]; exact tCellAutomatonWithAdvice.L_mem_ℒ C adv
    rw [ℒ_CA_rt_iff] at this
    exact Classical.choice (by simpa using this)
  spec C := by
    have hL : (C.val + adv).L ∈ ℒ (CA_rt α) := by
      rw [←h]; exact tCellAutomatonWithAdvice.L_mem_ℒ C adv
    rw [ℒ_CA_rt_iff] at hL
    exact (Classical.choice (by simpa using hL)).prop

/-- The iff between the structure-based and Prop-level definitions. -/
lemma advice_weak_rt_closed_iff_language_eq (adv: Advice α Γ):
    Nonempty adv.weak_rt_closed ↔ ℒ (CA_rt (α × Γ) + adv) = ℒ (CA_rt α) :=
  ⟨fun ⟨h⟩ => h.language_eq, fun h => ⟨.of_language_eq h⟩⟩

/-- Backward-compatible: extract witness from `weak_rt_closed`. -/
lemma tCellAutomatonWithAdvice.exists_CA_rt_of_weak_rt_closed {adv: Advice α Γ} (h: adv.weak_rt_closed) (C: CA_rt (α ⨉ Γ)):
    ∃ (C' : CA_rt α), C'.val.L = (C.val + adv).L :=
  ⟨h.map C, h.spec C⟩



@[simp]
lemma zip_left_empty {α} {v: Word β}: ([]: Word α) ⨂ v = [] := by simp [List.zip]

@[simp]
lemma zip_right_empty {α} {v: Word β}: v ⨂ ([]: Word α) = [] := by simp [List.zip]

@[simp]
lemma zip_empty_iff {α β} {v1: Word α} {v2: Word β}:
    v1 ⨂ v2 = [] ↔ v1 = [] ∨ v2 = [] := by simp [List.zip]


end CellularAutomatas
