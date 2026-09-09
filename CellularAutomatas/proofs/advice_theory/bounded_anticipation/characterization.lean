import CellularAutomatas.proofs.advice_theory.bounded_anticipation.global_readout
import CellularAutomatas.proofs.advice_theory.bounded_anticipation.diary_decode
import CellularAutomatas.proofs.advice_theory.bounded_anticipation.diagonal_readout

namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ] {advice : Advice α Γ}

/-- Weak closure is enough: a finite suffix diary gives a fixed-delay trace,
which geometric compression turns into globally valid readout packets. -/
theorem Advice.isGlobalPacketReadout_of_boundedAnticipation
    (hanticipation : advice.BoundedAnticipation) (hclosed : advice.weak_rt_closed) :
    advice.IsGlobalPacketReadout := by
  obtain ⟨a, ha⟩ := hanticipation
  have hdelay : advice.HasAnticipation (3 * (a + 1)) := ha.mono (by omega)
  let delayed := advice.delayedTrace_of_weak_rt_closed
    (3 * (a + 1)) (by omega) hdelay hclosed
  exact delayed.isGlobalPacketReadout

/-- This characterization is for the all-input subclass, not for contracts
restricted to an image of a preparation map. -/
theorem Advice.isGlobalPacketReadout_iff_boundedAnticipation_and_weak_rt_closed :
    advice.IsGlobalPacketReadout ↔
      advice.BoundedAnticipation ∧ Nonempty advice.weak_rt_closed := by
  constructor
  · intro hreadout
    show advice.BoundedAnticipation ∧ Nonempty advice.weak_rt_closed
    obtain ⟨hclosed⟩ := hreadout.rt_closed
    exact ⟨hreadout.boundedAnticipation,
      ⟨Advice.rt_closed_implies_weak_rt_closed hclosed⟩⟩
  · rintro ⟨hanticipation, ⟨hclosed⟩⟩
    show advice.IsGlobalPacketReadout
    exact Advice.isGlobalPacketReadout_of_boundedAnticipation hanticipation hclosed

theorem Advice.isGlobalPacketReadout_iff_boundedAnticipation_and_rt_closed :
    advice.IsGlobalPacketReadout ↔
      advice.BoundedAnticipation ∧ Nonempty advice.rt_closed := by
  constructor
  · intro hreadout
    show advice.BoundedAnticipation ∧ Nonempty advice.rt_closed
    exact ⟨hreadout.boundedAnticipation, hreadout.rt_closed⟩
  · rintro ⟨hanticipation, ⟨hclosed⟩⟩
    show advice.IsGlobalPacketReadout
    exact Advice.isGlobalPacketReadout_of_boundedAnticipation hanticipation
      (Advice.rt_closed_implies_weak_rt_closed hclosed)

/-- On bounded-anticipation advice, weak closure upgrades to closure under
every alphabet lift. No such upgrade is asserted for arbitrary advice. -/
theorem Advice.BoundedAnticipation.weak_rt_closed_iff_rt_closed
    (hanticipation : advice.BoundedAnticipation) :
    Nonempty advice.weak_rt_closed ↔ Nonempty advice.rt_closed := by
  constructor
  · rintro ⟨hclosed⟩
    show Nonempty advice.rt_closed
    exact (Advice.isGlobalPacketReadout_of_boundedAnticipation hanticipation hclosed).rt_closed
  · rintro ⟨hclosed⟩
    show Nonempty advice.weak_rt_closed
    exact ⟨Advice.rt_closed_implies_weak_rt_closed hclosed⟩

end CellularAutomatas
