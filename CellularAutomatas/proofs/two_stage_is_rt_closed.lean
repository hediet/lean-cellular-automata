import CellularAutomatas.proofs.ca_rt_utils
import CellularAutomatas.proofs.constructions.composition.compose_cart
import CellularAutomatas.proofs.constructions.composition.compose_two_stage
import CellularAutomatas.proofs.constructions.trace_id

namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

open CellAutomaton



def TwoStageAdvice.L {α} [Alphabet α] (adv: TwoStageAdvice α Bool): Language α :=
  { w: Word α | (adv.advice w).getLast? = true }


def TwoStageAdvice.to_CA_rt {α} [Alphabet α] (adv: TwoStageAdvice α Bool): CA_rt α :=
  fix_empty false (toRtCa $ adv.C.map_project (fun q => adv.M.f (adv.M.δ adv.M.q0 q)))



@[simp]
lemma TwoStageAdvice.to_CA_rt_L {α} [Alphabet α] (adv: TwoStageAdvice α Bool):
    adv.to_CA_rt.val.L = adv.L := by
  ext w

  unfold TwoStageAdvice.to_CA_rt
  unfold TwoStageAdvice.L
  rw [Set.mem_setOf_eq]

  by_cases h_empty: w = []
  · simp [h_empty]

  simp [h_empty]
  rw [←trace_rt_L h_empty]
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


theorem two_stage_is_weak_rt_closed (adv: TwoStageAdvice α Γ):
    adv.advice.weak_rt_closed := by
  rw [advice_weak_rt_closed_iff]

  intro C
  rw [ℒ_CA_rt_iff]

  let combined := (TwoStageAdvice.from_CA_rt C) ⊚ ((ca_to_two_stage (ca_trace_id_word α)) ⨂ adv)
  let C' := fix_empty ([] ∈ C.val.L) combined.to_CA_rt

  use C'
  constructor

  · show C'.val ∈ CA_rt α
    simp [C']

  · show C'.val.L = {w | w ⨂ adv.advice.f w ∈ C.val.L}
    ext w
    show w ∈ C'.val.L ↔ w ⨂ adv.advice.f w ∈ C.val.L

    by_cases h_empty: w = []
    · unfold C'
      simp [h_empty]

    calc
      w ∈ C'.val.L
      _ ↔ w ∈ (fix_empty (decide ([] ∈ C.val.L)) combined.to_CA_rt).val.L := by simp [C']
      _ ↔ w ∈ combined.L := by simp [h_empty]
      _ ↔ List.getLast? (combined.advice w) = some true := by
        unfold TwoStageAdvice.L
        rw [Set.mem_setOf_eq]
      _ ↔ w ⨂ adv.advice w ∈ C.val.L := by
        rw [elemL_iff_trace_rt (by simp)]
        simp [combined, h_empty]

def TwoStageAdvice.liftAdvice (adv: TwoStageAdvice α Γ) {S: Type} [Alphabet S] (π: S → α): TwoStageAdvice S Γ where
  β := adv.β
  C := adv.C.map_embed (Option.map π)
  M := adv.M

lemma TwoStageAdvice.liftAdvice_advice (adv: TwoStageAdvice α Γ) {S: Type} [Alphabet S] (π: S → α):
    (adv.liftAdvice π).advice = adv.advice.lift π := by
  apply advice_eq_iff
  funext w
  simp only [TwoStageAdvice.liftAdvice, TwoStageAdvice.advice, Function.comp, Advice.lift]
  congr 1
  exact map_embed_trace_rt adv.C π w

theorem two_stage_is_rt_closed (adv: TwoStageAdvice α Γ):
    adv.advice.rt_closed := by
  intro S _inst π
  rw [← adv.liftAdvice_advice π]
  exact two_stage_is_weak_rt_closed (adv.liftAdvice π)

theorem cart_is_rt_closed (C: CArtTransducer α Γ):
    C.advice.rt_closed :=
  ca_to_two_stage_advice_eq C ▸ two_stage_is_rt_closed (ca_to_two_stage C)
