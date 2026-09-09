import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.initialization
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.ready_packets

namespace CellularAutomatas.LocalHorizon.Fusion

open CellAutomaton

variable {α β γ : Type} {q₁ q₂ : ℕ} [NeZero q₂]

/-- Consecutive second-stage packets are already in the right spatial order;
fusion only concatenates the lanes inside one finite state. -/
def flatten (packets : Fin q₁ → Fin q₂ → γ) : Fin (q₁ * q₂) → γ :=
  fun i => packets
    ⟨i.val / q₂, (Nat.div_lt_iff_lt_mul (NeZero.pos q₂)).mpr i.isLt⟩
    ⟨i.val % q₂, Nat.mod_lt _ (NeZero.pos q₂)⟩

theorem flatten_compress (input : Config γ) (p : ℤ) :
    flatten (SpeedupKx.compress q₁ (SpeedupKx.compress q₂ input) p) =
      SpeedupKx.compress (q₁ * q₂) input p := by
  funext i
  show input ((p * q₁ + ↑(i.val / q₂)) * q₂ + ↑(i.val % q₂)) =
    input (p * ↑(q₁ * q₂) + ↑i.val)
  congr 1
  have hdiv : (↑(i.val / q₂) : ℤ) * q₂ + ↑(i.val % q₂) = i.val := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.div_add_mod i.val q₂)
  rw [Nat.cast_mul]
  nlinarith

namespace NormalizedProducer

variable [Alphabet α] [Alphabet β]
  {q κ : ℕ} {domain : Word α → Prop} {A B : Advice α β}

/-- Replace only the denotation on the promised domain, not the machine. -/
def congrOutput (producer : NormalizedProducer q κ domain A)
    (heq : ∀ w, domain w → A w = B w) :
    NormalizedProducer q κ domain B where
  source := producer.source
  release := producer.release
  width_ge_two := producer.width_ge_two
  startup_pos := producer.startup_pos
  emits w hw hne t p := by
    show producer.source.comp w t p = _
    rw [producer.emits w hw hne, heq w hw]
  lower := producer.lower
  deadline := producer.deadline
  exterior := producer.exterior

end NormalizedProducer

theorem exists_normalized [Alphabet α] [Alphabet β]
    {A : Advice α β} {domain : Word α → Prop}
    (hA : A.IsPacketReadoutOn domain) :
    ∃ q κ, Nonempty (NormalizedProducer q κ domain A) := by
  obtain ⟨machine, contract, hspec⟩ := hA
  exact ⟨machine.width, contract.startup,
    ⟨(ofContract contract).congrOutput hspec⟩⟩

end CellularAutomatas.LocalHorizon.Fusion
