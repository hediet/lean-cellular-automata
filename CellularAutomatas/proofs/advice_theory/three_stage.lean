import CellularAutomatas.proofs.advice_theory.local_horizon.machine
import CellularAutomatas.proofs.advice_theory.local_horizon.cart
import CellularAutomatas.proofs.constructions.trace_id

namespace CellularAutomatas

/-- Two-stage preparation, one locally clocked packet readout on its image,
and two-stage postprocessing. These are compositional layers, not runtime phases. -/
structure ThreeStageAdvice (α Γ : Type) [Alphabet α] [Alphabet Γ] where
  input : Type
  output : Type
  [inputAlphabet : Alphabet input]
  [outputAlphabet : Alphabet output]
  before : TwoStageAdvice α input
  machine : PacketReadoutMachine input output
  contract : machine.RTContractOn (Set.range before.advice)
  after : TwoStageAdvice output Γ

attribute [instance] ThreeStageAdvice.inputAlphabet ThreeStageAdvice.outputAlphabet

namespace ThreeStageAdvice

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- In mathematical order: `after ∘ readout ∘ before`. -/
def advice (presentation : ThreeStageAdvice α Γ) : Advice α Γ :=
  (presentation.before.advice.compose presentation.contract.readout).compose
    presentation.after.advice

theorem prepared_valid (presentation : ThreeStageAdvice α Γ) (w : Word α) :
    Set.range presentation.before.advice (presentation.before.advice w) :=
  ⟨w, rfl⟩

end ThreeStageAdvice

namespace Advice

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

def IsThreeStage (A : Advice α Γ) : Prop :=
  ∃ presentation : ThreeStageAdvice α Γ, presentation.advice = A

/-- A presentation with `k` locally clocked packet layers. Every layer's
promise is the image of the entire preceding pipeline. Depth is fixed for
the advice, not chosen separately for each input. No layer-collapse is assumed. -/
inductive HasPacketStages :
    {α Γ : Type} → [Alphabet α] → [Alphabet Γ] → ℕ → Advice α Γ → Prop
  | twoStage {α Γ : Type} [Alphabet α] [Alphabet Γ]
      {A : Advice α Γ} (presentation : A.IsTwoStageAdvice) :
      HasPacketStages 0 A
  | packet {α β δ Γ : Type}
      [Alphabet α] [Alphabet β] [Alphabet δ] [Alphabet Γ]
      {k : ℕ} {preceding : Advice α β}
      (previous : HasPacketStages k preceding)
      (machine : PacketReadoutMachine β δ)
      (contract : machine.RTContractOn (Set.range preceding))
      (after : TwoStageAdvice δ Γ) :
      HasPacketStages (k + 1)
        ((preceding.compose contract.readout).compose after.advice)

def IsFiniteStage (A : Advice α Γ) : Prop :=
  ∃ k, HasPacketStages k A

/-- The bounded hierarchy counts packet layers, not the two-stage factors. -/
def packetStageAdvices (α Γ : Type) [Alphabet α] [Alphabet Γ]
    (bound : ℕ) : Set (Advice α Γ) :=
  { A | ∃ k ≤ bound, HasPacketStages k A }

def threeStageAdvices (α Γ : Type) [Alphabet α] [Alphabet Γ] :
    Set (Advice α Γ) :=
  { A | A.IsThreeStage }

def finiteStageAdvices (α Γ : Type) [Alphabet α] [Alphabet Γ] :
    Set (Advice α Γ) :=
  { A | A.IsFiniteStage }

theorem hasPacketStages_zero_iff (A : Advice α Γ) :
    HasPacketStages 0 A ↔ Nonempty A.IsTwoStageAdvice := by
  constructor
  · intro h
    show Nonempty A.IsTwoStageAdvice
    cases h with
    | twoStage presentation => exact ⟨presentation⟩
  · rintro ⟨presentation⟩
    show HasPacketStages 0 A
    exact .twoStage presentation

theorem isThreeStage_iff_hasPacketStages_one (A : Advice α Γ) :
    A.IsThreeStage ↔ HasPacketStages 1 A := by
  constructor
  · rintro ⟨presentation, rfl⟩
    show HasPacketStages 1 presentation.advice
    exact .packet (.twoStage ⟨presentation.before, rfl⟩)
      presentation.machine presentation.contract presentation.after
  · intro h
    show A.IsThreeStage
    cases h with
    | packet previous machine contract after =>
      cases previous with
      | twoStage presentation =>
        obtain ⟨before, rfl⟩ := presentation
        exact ⟨{
          input := _
          output := _
          before := before
          machine := machine
          contract := contract
          after := after
        }, rfl⟩

theorem IsThreeStage.isFiniteStage {A : Advice α Γ} (h : A.IsThreeStage) :
    A.IsFiniteStage :=
  ⟨1, (isThreeStage_iff_hasPacketStages_one A).mp h⟩

/-- Insert the global identity readout, restricting its contract to the
preparation's image. This does not assume any three-stage closure conjecture. -/
theorem IsTwoStageAdvice.isThreeStage {A : Advice α Γ}
    (h : A.IsTwoStageAdvice) : A.IsThreeStage := by
  let identity := ca_trace_id_word Γ
  obtain ⟨machine, contract, hreadout⟩ :=
    LocalHorizon.cart_isGlobalPacketReadout identity
  let presentation : ThreeStageAdvice α Γ := {
    input := Γ
    output := Γ
    before := h.witness
    machine := machine
    contract := contract.restrict (Set.range h.witness.advice) (fun _ _ => trivial)
    after := ca_to_two_stage identity
  }
  refine ⟨presentation, ?_⟩
  apply advice_eq_iff
  funext w
  show (ca_to_two_stage identity).advice
    (contract.readout (h.witness.advice w)) = A w
  rw [ca_to_two_stage_spec, hreadout _ trivial]
  change identity.trace_rt (identity.trace_rt (h.witness.advice w)) = A w
  simp only [identity, ca_trace_id_scan_temporal, id_eq, h.spec]

theorem packetStageAdvices_one :
    packetStageAdvices α Γ 1 = threeStageAdvices α Γ := by
  ext A
  constructor
  · rintro ⟨k, hk, presentation⟩
    show A.IsThreeStage
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl
    · obtain ⟨h⟩ := (hasPacketStages_zero_iff A).mp presentation
      exact h.isThreeStage
    · exact (isThreeStage_iff_hasPacketStages_one A).mpr presentation
  · intro h
    show ∃ k ≤ 1, HasPacketStages k A
    exact ⟨1, le_rfl, (isThreeStage_iff_hasPacketStages_one A).mp h⟩

theorem packetStageAdvices_mono {k l : ℕ} (hkl : k ≤ l) :
    packetStageAdvices α Γ k ⊆ packetStageAdvices α Γ l := by
  rintro A ⟨depth, hdepth, presentation⟩
  show ∃ depth ≤ l, HasPacketStages depth A
  exact ⟨depth, le_trans hdepth hkl, presentation⟩

theorem mem_finiteStageAdvices_iff (A : Advice α Γ) :
    A ∈ finiteStageAdvices α Γ ↔ ∃ k, A ∈ packetStageAdvices α Γ k := by
  constructor
  · rintro ⟨k, presentation⟩
    show ∃ k, A ∈ packetStageAdvices α Γ k
    exact ⟨k, k, le_rfl, presentation⟩
  · rintro ⟨_, k, _, presentation⟩
    show A.IsFiniteStage
    exact ⟨k, presentation⟩

end Advice
end CellularAutomatas
