import CellularAutomatas.proofs.uniform_local.program
import CellularAutomatas.proofs.uniform_local.relabel
import CellularAutomatas.proofs.advice_theory.marked_prefix.retain_input

namespace CellularAutomatas

namespace CellAutomaton

/-- Endpoint correctness is separate from the local-program restriction.
The target runs on the transformed word; no state decoder or time-zero
correspondence is required. Empty input has no RT endpoint obligation. -/
def PreservesRtEndpointOn {α β output : Type}
    (A : Advice α β) (domain : Word α → Prop)
    (f : CellAutomaton (Option β) output → CellAutomaton (Option α) output) : Prop :=
  ∀ target w, domain w → w ≠ [] →
    (f target).trace w (w.length - 1) =
      target.trace (A w) (w.length - 1)

def IsUniformRtSimulationOn {α β output : Type}
    (A : Advice α β) (domain : Word α → Prop)
    (f : CellAutomaton (Option β) output → CellAutomaton (Option α) output) : Prop :=
  IsUniformlyLocal f ∧ PreservesRtEndpointOn A domain f

/-- Compiler order is contravariant: `f ∘ g` eliminates `B ∘ A`
(written `A.compose B` in Lean). -/
theorem PreservesRtEndpointOn.comp {α β γ output : Type}
    {A : Advice α β} {B : Advice β γ}
    {domain : Word α → Prop} {middle : Word β → Prop}
    {f : CellAutomaton (Option β) output → CellAutomaton (Option α) output}
    {g : CellAutomaton (Option γ) output → CellAutomaton (Option β) output}
    (hf : PreservesRtEndpointOn A domain f)
    (hg : PreservesRtEndpointOn B middle g)
    (hcompatible : ∀ w, domain w → middle (A w)) :
    PreservesRtEndpointOn (A.compose B) domain (f ∘ g) := by
  intro target w hw hne
  have htransformed : A w ≠ [] := by
    apply List.ne_nil_of_length_pos
    simpa only [advice_len] using List.length_pos_of_ne_nil hne
  calc
    (f (g target)).trace w (w.length - 1) =
        (g target).trace (A w) (w.length - 1) := hf (g target) w hw hne
    _ = target.trace (B (A w)) (w.length - 1) := by
      simpa only [advice_len] using hg target (A w) (hcompatible w hw) htransformed

theorem IsUniformRtSimulationOn.comp {α β γ output : Type}
    {A : Advice α β} {B : Advice β γ}
    {domain : Word α → Prop} {middle : Word β → Prop}
    {f : CellAutomaton (Option β) output → CellAutomaton (Option α) output}
    {g : CellAutomaton (Option γ) output → CellAutomaton (Option β) output}
    (hf : IsUniformRtSimulationOn A domain f)
    (hg : IsUniformRtSimulationOn B middle g)
    (hcompatible : ∀ w, domain w → middle (A w)) :
    IsUniformRtSimulationOn (A.compose B) domain (f ∘ g) :=
  ⟨hf.1.comp hg.1, hf.2.comp hg.2 hcompatible⟩

end CellAutomaton

/-- One fixed opaque-state local program per alphabet lift and output alphabet,
working for every target CA. Retaining the input matches advised recognition:
consumers see both their original symbols and the advice symbols.

This is a candidate formal meaning of uniform local simulation, not an
asserted characterization of three-stage advice or of all RT-closed advice. -/
def Advice.IsUniformlyLocallySimulatable {α Γ : Type}
    [Alphabet α] [Alphabet Γ] (A : Advice α Γ) : Prop :=
  ∀ (σ : Type) [Alphabet σ] (π : σ → α) (output : Type) [Alphabet output],
    ∃ program : UniformLocal.Program (Option σ) (Option (σ × Γ)) output,
      CellAutomaton.PreservesRtEndpointOn (A.lift π).retainInput
        (fun _ => True) program.compile

def Advice.uniformlyLocallySimulatableAdvices (α Γ : Type)
    [Alphabet α] [Alphabet Γ] : Set (Advice α Γ) :=
  { A | A.IsUniformlyLocallySimulatable }

end CellularAutomatas
