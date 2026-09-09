import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.packets
import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.retained_events
import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.readiness

namespace CellularAutomatas.LocalHorizon.Fusion

open CellAutomaton

namespace PackedTarget

variable {β γ : Type} [Alphabet β] [Alphabet γ]
  {q₁ q₂ κ₂ : ℕ} [NeZero q₁] [NeZero q₂]
  {middle : Word β → Prop} {B : Advice β γ}

/-- Retain each second-stage event before speeding up, then concatenate
completed lanes. A pulse between packed generations cannot be skipped. -/
def C (q₁ : ℕ) [NeZero q₁] (second : PacketProducer q₂ κ₂ middle B) :
    CellAutomaton (Fin q₁ → Option β) (Option (Fin (q₁ * q₂) → Option γ)) :=
  (RetainedEvents.packedJoined second.source q₁).map_project (Option.map flatten)

def times (q₁ : ℕ) (second : PacketProducer q₂ κ₂ middle B)
    (input : Word β) (p : ℕ) : Fin q₁ → ℕ :=
  fun s => second.release input (p * q₁ + s.val)

theorem comp_spec (second : PacketProducer q₂ κ₂ middle B)
    (input : Word β) (hw : middle input) (hne : input ≠ []) (d p : ℕ) :
    (C q₁ second).comp ⦋SpeedupKx.compress q₁ (word_to_config input)⦌ d p =
      if ∀ s, times q₁ second input p s ≤ q₁ * d then
        some (SpeedupKx.compress (q₁ * q₂) (word_to_config (B input)) p)
      else none := by
  let payload := SpeedupKx.compress q₁
    (SpeedupKx.compress q₂ (word_to_config (B input))) (p : ℤ)
  have hevent (s : Fin q₁) (t : ℕ) :
      second.source.comp input t ((p : ℤ) * q₁ + s) =
        if t = times q₁ second input p s then some (payload s) else none := by
    have hspec := second.emits input hw hne t (p * q₁ + s.val)
    simpa only [times, payload, SpeedupKx.compress, Nat.cast_add, Nat.cast_mul]
      using hspec
  rw [C, comp_of_map_project,
    RetainedEvents.packedJoined_one_shot second.source (word_to_config input)
      q₁ d p (times q₁ second input p) payload hevent]
  split
  · show some (flatten payload) = _
    rw [flatten_compress]
  · rfl

theorem atHeight_spec (second : PacketProducer q₂ κ₂ middle B)
    (input : Word β) (hw : middle input) (hne : input ≠ []) (h p : ℕ) :
    (if h = 0 then none else
      (C q₁ second).comp ⦋SpeedupKx.compress q₁ (word_to_config input)⦌ (h - 1) p) =
      if lanesReady (times q₁ second input p) h then
        some (SpeedupKx.compress (q₁ * q₂) (word_to_config (B input)) p)
      else none := by
  by_cases hh : h = 0
  · show _ = _
    simp [hh, lanesReady]
  · show _ = _
    rw [if_neg hh, comp_spec second input hw hne]
    simp only [lanesReady, show 0 < h by omega, true_and]

end PackedTarget
end CellularAutomatas.LocalHorizon.Fusion
