import CellularAutomatas.proofs.advice_theory.marked_prefix.lt
import CellularAutomatas.proofs.advice_theory.rt_closed.of_compose

namespace CellularAutomatas.MarkedPrefix

/-- A bounded normal-form candidate: two-stage preprocessing, one spatial LT
prefix transformation, and two-stage postprocessing. -/
structure TwoStagePrefixSandwich (α Γ : Type) [Alphabet α] [Alphabet Γ] where
  input : Type
  output : Type
  [inputAlphabet : Alphabet input]
  [outputAlphabet : Alphabet output]
  before : TwoStageAdvice α input
  transform : Advice input output
  linear : transform.IsLtAdvice
  blank : output
  after : TwoStageAdvice output Γ

attribute [instance] TwoStagePrefixSandwich.inputAlphabet
attribute [instance] TwoStagePrefixSandwich.outputAlphabet

namespace TwoStagePrefixSandwich

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

def advice (e : TwoStagePrefixSandwich α Γ) : Advice α Γ :=
  (e.before.advice.compose (prefixTransform dyadicSelector e.transform e.blank)).compose
    e.after.advice

/-- Strong RT closure follows from the three concrete factors. -/
noncomputable def rt_closed (e : TwoStagePrefixSandwich α Γ) :
    e.advice.rt_closed :=
  Advice.rt_closed_compose_rt_closed _ _
    (Advice.rt_closed_compose_rt_closed _ _
      (two_stage_is_rt_closed e.before)
      (dyadicPrefixTransform_rt_closed e.transform e.linear e.blank))
    (two_stage_is_rt_closed e.after)

def precompose {σ : Type} [Alphabet σ]
    (e : TwoStagePrefixSandwich α Γ) (before : TwoStageAdvice σ α) :
    TwoStagePrefixSandwich σ Γ where
  input := e.input
  output := e.output
  before := compose_two_stage e.before before
  transform := e.transform
  linear := e.linear
  blank := e.blank
  after := e.after

def postcompose {Δ : Type} [Alphabet Δ]
    (e : TwoStagePrefixSandwich α Γ) (after : TwoStageAdvice Γ Δ) :
    TwoStagePrefixSandwich α Δ where
  input := e.input
  output := e.output
  before := e.before
  transform := e.transform
  linear := e.linear
  blank := e.blank
  after := compose_two_stage after e.after

theorem precompose_spec {σ : Type} [Alphabet σ]
    (e : TwoStagePrefixSandwich α Γ) (before : TwoStageAdvice σ α) :
    (e.precompose before).advice = before.advice.compose e.advice := by
  apply advice_eq_iff
  funext w
  change
    e.after.advice
        (prefixTransform dyadicSelector e.transform e.blank
          ((compose_two_stage e.before before).advice w)) =
      e.after.advice
        (prefixTransform dyadicSelector e.transform e.blank
          (e.before.advice (before.advice w)))
  rw [compose_two_stage_spec]
  rfl

theorem postcompose_spec {Δ : Type} [Alphabet Δ]
    (e : TwoStagePrefixSandwich α Γ) (after : TwoStageAdvice Γ Δ) :
    (e.postcompose after).advice = e.advice.compose after.advice := by
  apply advice_eq_iff
  funext w
  change
    (compose_two_stage after e.after).advice
        (prefixTransform dyadicSelector e.transform e.blank (e.before.advice w)) =
      after.advice
        (e.after.advice
          (prefixTransform dyadicSelector e.transform e.blank (e.before.advice w)))
  rw [compose_two_stage_spec]
  rfl

end TwoStagePrefixSandwich

/-- A concrete class containing two-stage advice and the three-factor
sandwiches. This definition does not assume membership in `rt_closed` or
close under an arbitrary number of compositions. -/
inductive IsTwoStagePrefixAdvice
    {α Γ : Type} [Alphabet α] [Alphabet Γ] (adv : Advice α Γ) : Type 1
  | twoStage (witness : adv.IsTwoStageAdvice)
  | sandwich (witness : TwoStagePrefixSandwich α Γ) (spec : witness.advice = adv)

namespace IsTwoStagePrefixAdvice

variable {α Γ : Type} [Alphabet α] [Alphabet Γ] {adv : Advice α Γ}

def of_two_stage (witness : TwoStageAdvice α Γ) :
    IsTwoStagePrefixAdvice witness.advice :=
  .twoStage ⟨witness, rfl⟩

/-- Both generating families belong to the concrete class. -/
def of_prefix (F : Advice α Γ) (hF : F.IsLtAdvice) (blank : Γ) :
    IsTwoStagePrefixAdvice (prefixTransform dyadicSelector F blank) := by
  refine .sandwich {
    input := α
    output := Γ
    before := ca_to_two_stage (ca_trace_id_word α)
    transform := F
    linear := hF
    blank := blank
    after := ca_to_two_stage (ca_trace_id_word Γ)
  } ?_
  apply advice_eq_iff
  funext w
  change
    (ca_to_two_stage (ca_trace_id_word Γ)).advice
        (prefixTransform dyadicSelector F blank
          ((ca_to_two_stage (ca_trace_id_word α)).advice w)) =
      prefixTransform dyadicSelector F blank w
  simp only [ca_to_two_stage_spec, ca_trace_id_scan_temporal, id_eq]

noncomputable def rt_closed (h : IsTwoStagePrefixAdvice adv) : adv.rt_closed := by
  cases h with
  | twoStage witness =>
    rw [← witness.spec]
    exact two_stage_is_rt_closed witness.witness
  | sandwich witness hspec =>
    rw [← hspec]
    exact witness.rt_closed

/-- Precomposing with two-stage advice stays within the same bounded form. -/
def precompose {σ : Type} [Alphabet σ]
    (h : IsTwoStagePrefixAdvice adv) (before : TwoStageAdvice σ α) :
    IsTwoStagePrefixAdvice (before.advice.compose adv) := by
  cases h with
  | twoStage witness =>
    obtain ⟨witness, rfl⟩ := witness
    apply twoStage
    refine ⟨compose_two_stage witness before, ?_⟩
    apply advice_eq_iff
    exact compose_two_stage_spec before witness
  | sandwich witness hspec =>
    apply sandwich (witness.precompose before)
    rw [TwoStagePrefixSandwich.precompose_spec, hspec]

/-- Postcomposing with two-stage advice stays within the same bounded form. -/
def postcompose {Δ : Type} [Alphabet Δ]
    (h : IsTwoStagePrefixAdvice adv) (after : TwoStageAdvice Γ Δ) :
    IsTwoStagePrefixAdvice (adv.compose after.advice) := by
  cases h with
  | twoStage witness =>
    obtain ⟨witness, rfl⟩ := witness
    apply twoStage
    refine ⟨compose_two_stage after witness, ?_⟩
    apply advice_eq_iff
    exact compose_two_stage_spec witness after
  | sandwich witness hspec =>
    apply sandwich (witness.postcompose after)
    rw [TwoStagePrefixSandwich.postcompose_spec, hspec]

end IsTwoStagePrefixAdvice
end CellularAutomatas.MarkedPrefix
