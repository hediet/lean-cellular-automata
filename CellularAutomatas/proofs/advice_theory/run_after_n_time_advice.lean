import CellularAutomatas.proofs.advice_theory.time_advice_combinators
import CellularAutomatas.proofs.advice_theory.sync_time_constructible
import CellularAutomatas.proofs.constructions.basic_ca_id
import CellularAutomatas.proofs.constructions.basic_compose_k_steps
import CellularAutomatas.proofs.constructions.basic_mark_border
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.border_quiescent
import CellularAutomatas.proofs.rt_eq_2n_iff_rt_eq_rt_rev.rt_eq_2n_iff_rt_eq_rt_rev

namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

namespace RunAfterNTimeAdvice

/-- Delay an RT recognizer by one tick. At local time `n`, this exposes its
    ordinary RT answer from time `n - 1`. -/
def delayedRuntime (C : CA_rt Γ) : LCellAutomaton Γ :=
  (CellAutomaton.idCA (Option Γ)).composeKSteps C.toCellAutomaton 1

lemma delayedRuntime_spec (C : CA_rt Γ) (v : Word Γ) (hv : 0 < v.length) :
    (delayedRuntime C).comp ⦋⟬v⟭⦌ v.length 0 =
      C.toCellAutomaton.comp ⦋⟬v⟭⦌ (v.length - 1) 0 := by
  unfold delayedRuntime
  rw [CellAutomaton.composeKSteps_comp
    (CellAutomaton.idCA (Option Γ)) C.toCellAutomaton 1 ⟬v⟭ v.length 0]
  simp only [show v.length ≥ 1 by omega, ↓reduceIte]
  rw [CellAutomaton.idCA.comp_spec]
  change C.toCellAutomaton.comp
      (fun p => C.toCellAutomaton.embed
        ((CellAutomaton.idCA (Option Γ)).embed (word_to_config v p)))
      (v.length - 1) 0 =
    C.toCellAutomaton.comp
      (fun p => C.toCellAutomaton.embed (word_to_config v p))
      (v.length - 1) 0
  simp only [CellAutomaton.idCA, id_eq]

/-- Quiescent-border wrapper required by the generic phase composition. -/
def borderedRuntime (C : CA_rt Γ) : QuiescentBorder where
  C_orig := delayedRuntime C

def runtime (C : CA_rt Γ) : LCellAutomaton Γ :=
  (borderedRuntime C).C

lemma runtime_spec (C : CA_rt Γ) (v : Word Γ) (hv : 0 < v.length) :
    (runtime C).comp ⦋⟬v⟭⦌ v.length 0 =
      C.toCellAutomaton.comp ⦋⟬v⟭⦌ (v.length - 1) 0 := by
  have h_cone : (0 : ℤ) ∈ WordCone v v.length := by
    rw [WordCone_mem]
    simpa using hv
  change (borderedRuntime C).C.comp ⦋⟬v⟭⦌ v.length 0 = _
  rw [(borderedRuntime C).spec v hv v.length 0]
  rw [if_pos h_cone]
  exact delayedRuntime_spec C v hv

/-- Compute an `n`-time advice, then run an RT recognizer on its output. -/
def chain (adv : Advice α Γ) (hAdv : adv.IsNTimeAdvice) (C : CA_rt Γ) :
    FireThenRunInput α Γ Bool :=
  { a := hAdv
    sc := IdSync.toInner
    runtime := runtime C
    h_quiescent := (borderedRuntime C).C_border_quiescent }

lemma chain_spec (adv : Advice α Γ) (hAdv : adv.IsNTimeAdvice)
    (C : CA_rt Γ) (w : Word α) (hw : 0 < w.length) :
    (chain adv hAdv C).C.comp ⦋⟬w⟭⦌ (2 * w.length) 0 =
      C.toCellAutomaton.comp ⦋⟬adv w⟭⦌ (w.length - 1) 0 := by
  calc
    (chain adv hAdv C).C.comp ⦋⟬w⟭⦌ (2 * w.length) 0
        = (runtime C).comp ⦋⟬adv w⟭⦌ w.length 0 := by
          have h_post := (chain adv hAdv C).spec_post w w.length 0
          have h_time : (chain adv hAdv C).t1 w.length + w.length =
              2 * w.length := by
            change w.length + w.length = 2 * w.length
            omega
          rw [h_time] at h_post
          exact h_post
    _ = C.toCellAutomaton.comp ⦋⟬adv w⟭⦌ (w.length - 1) 0 := by
      have h_runtime := runtime_spec C (adv w) (by simpa [adv.len] using hw)
      rw [adv.len] at h_runtime
      exact h_runtime

/-- The generic two-stage construction, read at proper time `2n`. -/
def proper (adv : Advice α Γ) (hAdv : adv.IsNTimeAdvice) (C : CA_rt Γ) :
    CA_2n_proper α :=
  let chained : LCellAutomaton α := (chain adv hAdv C).C
  let containsEmpty : Bool := C.accepts (adv [])
  { toCellAutomaton :=
      (chained ⨂ c_is_border α).map_project
        (fun (answer, isEmpty) => if isEmpty then containsEmpty else answer) }

lemma proper_spec (adv : Advice α Γ) (hAdv : adv.IsNTimeAdvice)
    (C : CA_rt Γ) (w : Word α) :
    (proper adv hAdv C).accepts w = C.accepts (adv w) := by
  change (proper adv hAdv C).toCellAutomaton.comp
      ⦋⟬w⟭⦌ (2 * w.length) 0 = _
  unfold proper
  erw [comp_of_map_project]
  rw [ca_zip_comp, c_is_border_spec]
  by_cases hw : w = []
  · subst w
    rfl
  · have hw_pos : 0 < w.length := by
      cases w with
      | nil => exact absurd rfl hw
      | cons _ _ => simp
    have h_not_empty : (w == []) = false := by simp [hw]
    rw [h_not_empty]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [chain_spec adv hAdv C w hw_pos]
    simp [tCellAutomaton.accepts, AcceptanceSchema.rt_center, adv.len]

/-- Every RT language using `n`-time advice is recognizable at proper time
    `2n`: compute the annotated input, then run its RT recognizer. -/
theorem advised_ca_rt_subset_ca_2n_proper
    (adv : Advice α Γ) (hAdv : adv.IsNTimeAdvice) :
    ℒ (CA_rt (α × Γ) + adv) ⊆ ℒ (CA_2n_proper α) := by
  intro L ⟨advisedC, hL⟩
  let annotatedAdvice : Advice α (α × Γ) :=
    Advice.zip (Advice.identity α) adv
  let hAnnotated : annotatedAdvice.IsNTimeAdvice :=
    (Advice.identity_isTimeAdvice (α := α) (fun n => n)).zip hAdv
  refine ⟨proper annotatedAdvice hAnnotated advisedC.C, ?_⟩
  rw [hL]
  ext w
  change advisedC.C.accepts (adv.annotate w) = true ↔
    (proper annotatedAdvice hAnnotated advisedC.C).accepts w = true
  rw [proper_spec]
  change advisedC.C.accepts (adv.annotate w) = true ↔
    advisedC.C.accepts (Advice.zip (Advice.identity α) adv w) = true
  rw [Advice.zip_identity_eq_annotate]

end RunAfterNTimeAdvice

end CellularAutomatas
