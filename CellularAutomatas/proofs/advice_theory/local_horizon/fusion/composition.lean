import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.assembly

namespace CellularAutomatas

open LocalHorizon

namespace Advice

variable {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]
  {A : Advice α β} {B : Advice β γ}
  {domain : Word α → Prop} {middle : Word β → Prop}

/-- Packet readouts fuse on compatible promises. The intermediate word is
generated internally; it is not a new advice track supplied to the machine. -/
theorem IsPacketReadoutOn.compose
    (hA : A.IsPacketReadoutOn domain) (hB : B.IsPacketReadoutOn middle)
    (hcompatible : ∀ w, domain w → middle (A w)) :
    (A.compose B).IsPacketReadoutOn domain := by
  obtain ⟨q₁, κ₁, ⟨first⟩⟩ := Fusion.exists_normalized hA
  obtain ⟨q₂, κ₂, ⟨second⟩⟩ := Fusion.exists_normalized hB
  letI : NeZero q₁ := ⟨by have := first.width_ge_two; omega⟩
  letI : NeZero q₂ := ⟨by have := second.width_ge_two; omega⟩
  exact Fusion.normalized_comp first second hcompatible

/-- All-input fusion is the special case with both promises equal to `True`. -/
theorem IsGlobalPacketReadout.compose
    (hA : A.IsGlobalPacketReadout) (hB : B.IsGlobalPacketReadout) :
    (A.compose B).IsGlobalPacketReadout :=
  IsPacketReadoutOn.compose hA hB (fun _ _ => True.intro)

end Advice

namespace LocalHorizon.PacketProducer

variable {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]
  {A : Advice α β} {B : Advice β γ}
  {domain : Word α → Prop} {middle : Word β → Prop}
  {q₁ κ₁ q₂ κ₂ : ℕ}

/-- Bare producers also fuse: first normalize their exterior releases.
No additional bound on either original exterior schedule is assumed. -/
theorem compose_isPacketReadoutOn
    (first : PacketProducer q₁ κ₁ domain A)
    (second : PacketProducer q₂ κ₂ middle B)
    (hcompatible : ∀ w, domain w → middle (A w)) :
    (A.compose B).IsPacketReadoutOn domain :=
  (Fusion.producer_isPacketReadoutOn first).compose
    (Fusion.producer_isPacketReadoutOn second) hcompatible

/-- Re-normalizing the fused readout gives a single paced, padded producer. -/
theorem exists_composition
    (first : PacketProducer q₁ κ₁ domain A)
    (second : PacketProducer q₂ κ₂ middle B)
    (hcompatible : ∀ w, domain w → middle (A w)) :
    ∃ q κ, Nonempty (PacketProducer q κ domain (A.compose B)) := by
  obtain ⟨q, κ, ⟨producer⟩⟩ := Fusion.exists_normalized
    (first.compose_isPacketReadoutOn second hcompatible)
  exact ⟨q, κ, ⟨producer.toPacketProducer⟩⟩

end LocalHorizon.PacketProducer
end CellularAutomatas
