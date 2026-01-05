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


variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]


section CountUntil

def some_fin (k: ℕ) (i: ℕ): Option (Fin k) :=
  if h: i < k then
    some (Fin.mk i (by simp [h]))
  else
    none

lemma some_fin_succ: ((some_fin k v) >>= fun v => some_fin k (v + 1)) = some_fin k (v + 1) := by
  unfold some_fin
  grind

def c_count_until {α} [Alphabet α] (k: ℕ) [NeZero k]: CellAutomaton α (Fin k)？ :=
  {
    Q := (Fin k)？
    δ := fun _ q2 _ => q2 >>= fun v => some_fin k (v.val + 1)
    embed := fun _ => some 0
    project := id
  }

@[simp]
lemma c_count_until_spec_config {α} [Alphabet α] (k: ℕ) [h: NeZero k] (c: Config α):
    (c_count_until k).comp (embed_config c) t i = some_fin k t := by
  rw [comp_config_eq_project_nextt]
  change ((c_count_until k).nextt ⦋c⦌ t) i = some_fin k t

  induction t generalizing i with
  | zero =>
    simp [c_count_until, embed_config, some_fin, h.out]
  | succ t ih =>
    rw [nextt_succ]
    simp [CellAutomaton.next]
    simp [ih]
    simp [c_count_until]
    exact some_fin_succ

@[simp]
def c_count_until_spec_word {α} [Alphabet α] (k: Nat) [NeZero k] (w: Word α):
    (c_count_until k).comp (embed_word w) t i = some_fin k t := by
  rw [embed_word]
  rw [c_count_until_spec_config]

end CountUntil




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
    (ca_to_two_stage C).advice.f = C.trace_rt := by
  funext w
  simp [ca_to_two_stage, TwoStageAdvice.advice]





def zip_two_stage [Alphabet α] [Alphabet β] [Alphabet γ] (a1: TwoStageAdvice α β) (a2: TwoStageAdvice α γ):
    TwoStageAdvice α (β × γ) :=
  let ca_new := a1.C ⨂ a2.C
  let fst_new := a1.M ⨂ a2.M
  TwoStageAdvice.from_transducers fst_new ca_new

@[simp]
def zip_spec [Alphabet α] [Alphabet β] [Alphabet γ] (a1: TwoStageAdvice α β) (a2: TwoStageAdvice α γ):
    (zip_two_stage a1 a2).advice.f w = (a1.advice.f w ⨂ a2.advice.f w) := by
  simp [zip_two_stage, TwoStageAdvice.advice, TwoStageAdvice.from_transducers]
  rfl

infixl:65 " ⨂ " => zip_two_stage








lemma embed_word_p_eq {α} [Alphabet α] (w: Word α) {C: CellAutomaton α？ β} (p: ℤ):
    (embed_word (C := C) w) p = C.embed (if h: p ≥ 0 ∧ p < w.length then w[p.toNat] else none) := by
  unfold embed_word word_to_config embed_config
  grind


section CisBorder

def c_is_border (α) [Alphabet α]: CellAutomaton α？ Bool :=
  {
    Q := Bool
    δ := fun _ val _ => val
    embed
    | none => true
    | some _ => false
    project := id
  }

@[simp]
lemma c_is_border_spec {α} [Alphabet α] (w: Word α):
    (c_is_border α).comp w t 0 = (w == []) := by
  unfold comp
  erw [Function.id_comp]

  induction t with
  | zero =>
    rw [nextt_zero]
    rw [embed_word_p_eq]
    unfold c_is_border
    cases w
    · simp
    · simp
  | succ t ih =>
    rw [nextt_succ]
    unfold CellAutomaton.next
    rw [ih]
    simp [c_is_border]

end CisBorder



section fix_empty

variable {α: Type} [Alphabet α]


def fix_empty (contains_empty: Bool) (C: CA_rt α): CA_rt α :=
    toRtCa ((C.val.toCellAutomaton ⨂ c_is_border α).map_project (fun (a, b) => if b then contains_empty else a))

@[simp]
lemma fix_empty_spec (contains_empty: Bool) (C: CA_rt α)  (w: Word α):
    w ∈ (fix_empty contains_empty C).val.L ↔ if w == [] then contains_empty else w ∈ C.val.L := by
  rw [CA_rt_L_iff]
  unfold embed_word
  erw [map_project_comp]
  rw [ca_zip_comp]
  simp [CA_rt_L_iff]

end fix_empty








lemma subset_iff {α} {A B: Set α}: A ⊆ B ↔ (∀ L, L ∈ A → L ∈ B) := by rfl


lemma advice_rt_closed_iff (adv: Advice α Γ):
    adv.rt_closed ↔ (∀ (C : CA_rt (α ⨉ Γ)), {w | w ⨂ adv.f w ∈ C.val.L} ∈ ℒ (CA_rt α)) := by
  unfold Advice.rt_closed
  rw [subset_antisymm_iff]
  simp only [CA_rt_subseteq_CA_rt_with_advice adv, and_true]
  rw [subset_iff]
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



-- todo can be defined for any advice
def TwoStageAdvice.L {α} [Alphabet α] (adv: TwoStageAdvice α Bool): Language α :=
  { w: Word α | (adv.advice.f w).getLast? = true }


def TwoStageAdvice.to_CA_rt {α} [Alphabet α] (adv: TwoStageAdvice α Bool): CA_rt α :=
  fix_empty false (toRtCa $ adv.C.map_project (fun q => adv.M.f (adv.M.δ adv.M.q0 q)))



@[simp]
lemma TwoStageAdvice.to_CA_rt_L {α} [Alphabet α] (adv: TwoStageAdvice α Bool):
    adv.to_CA_rt.val.L = adv.L := by
  ext w

  unfold TwoStageAdvice.to_CA_rt

  by_cases h: w = []
  · unfold TwoStageAdvice.L
    rw [prop_of_elem_prop_set]
    simp [h]

  unfold TwoStageAdvice.L
  rw [prop_of_elem_prop_set]

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
    (TwoStageAdvice.from_CA_rt C).advice.f = C.val.trace_rt := by
  funext w
  simp [TwoStageAdvice.from_CA_rt, TwoStageAdvice.advice]


@[simp]
lemma zip_left_empty {α} {v: Word β}: ([]: Word α) ⨂ v = [] := by simp [zip_words]

@[simp]
lemma zip_right_empty {α} {v: Word β}: v ⨂ ([]: Word α) = [] := by simp [zip_words]

@[simp]
lemma zip_empty_iff {α β} {v1: Word α} {v2: Word β}:
    v1 ⨂ v2 = [] ↔ v1 = [] ∨ v2 = [] := by simp [zip_words]



theorem two_stage_rt_closed (adv: TwoStageAdvice α Γ):
    adv.advice.rt_closed := by
  open Classical in -- I'm quite sure this is not needed logically

  rw [advice_rt_closed_iff]
  intro C
  rw [ℒ_CA_rt_iff]

  let x := ((TwoStageAdvice.from_CA_rt C) ⊚ ((ca_to_two_stage (ca_id_word α)) ⨂ adv))
  let C' := fix_empty ([] ∈ C.val.L) x.to_CA_rt

  use C'

  constructor
  · simp [C']

  ext w


  simp [C']
  rw [prop_of_elem_prop_set]

  by_cases h_empty: w = []
  · simp [h_empty]

  simp [h_empty]
  simp [x]

  unfold TwoStageAdvice.L
  rw [prop_of_elem_prop_set]

  have : ↑C ∈ CA_rt (α ⨉ Γ) := by simp
  rw [elemL_iff_trace_rt this]

  simp [h_empty]
