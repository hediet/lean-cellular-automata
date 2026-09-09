import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.async_full_line
import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.packed_target
import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.deadline

namespace CellularAutomatas.LocalHorizon.Fusion

variable {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]
  {q₁ q₂ κ₁ κ₂ : ℕ} [NeZero q₁] [NeZero q₂]
  {domain : Word α → Prop} {middle : Word β → Prop}
  {A : Advice α β} {B : Advice β γ}

def simulationHeight (first : PacketProducer q₁ κ₁ domain A)
    (w : Word α) (t : ℕ) (p : ℤ) : ℕ :=
  AsyncFullLine.height (Initialization.release first w) t p

def ready (first : PacketProducer q₁ κ₁ domain A)
    (second : PacketProducer q₂ κ₂ middle B) (w : Word α) (p t : ℕ) : Prop :=
  lanesReady (PackedTarget.times q₁ second (A w) p) (simulationHeight first w t p)

instance (first : PacketProducer q₁ κ₁ domain A)
    (second : PacketProducer q₂ κ₂ middle B) (w : Word α) (p t : ℕ) :
    Decidable (ready first second w p t) :=
  inferInstanceAs (Decidable (lanesReady _ _))

omit [Alphabet α] [Alphabet β] [Alphabet γ] [NeZero q₁] [NeZero q₂] in
theorem ready_mono (first : PacketProducer q₁ κ₁ domain A)
    (second : PacketProducer q₂ κ₂ middle B) (w : Word α) (p t u : ℕ)
    (htu : t ≤ u) (hready : ready first second w p t) :
    ready first second w p u :=
  lanesReady_mono _ (AsyncFullLine.height_mono _ _ htu) hready

omit [Alphabet α] [Alphabet β] [Alphabet γ] [NeZero q₁] [NeZero q₂] in
theorem ready_eventually (first : PacketProducer q₁ κ₁ domain A)
    (second : PacketProducer q₂ κ₂ middle B) (w : Word α) (p : ℕ) :
    ∃ t, ready first second w p t := by
  apply lanesReady_eventually (by have := first.width_ge_two; omega)
  intro d
  exact AsyncFullLine.height_eventually (Initialization.release first w) p d

omit [Alphabet γ] [NeZero q₁] [NeZero q₂] in
/-- The second producer's virtual depth fits in the first producer's local
release cone. The resulting coefficient is the product width minus one. -/
theorem ready_deadline (first : NormalizedProducer q₁ κ₁ domain A)
    (second : NormalizedProducer q₂ κ₂ middle B)
    (w : Word α) (hw : domain w) (hmiddle : middle (A w)) (hne : w ≠ [])
    (p : ℕ) (hp : p < packetCount (q₁ * q₂) w.length) :
    ready first.toPacketProducer second.toPacketProducer w p
      (startup q₁ q₂ κ₁ κ₂ + (q₁ * q₂ - 1) * packetCount (q₁ * q₂) w.length) := by
  let K := packetCount (q₁ * q₂) w.length
  let d := (q₂ - 1) * K + κ₂
  let T := κ₁ + (q₁ - 1) * (q₂ * K + κ₂)
  have hcone : ∀ z, |z - (p : ℤ)| ≤ (d : ℤ) →
      Initialization.release first.toPacketProducer w z ≤ T :=
    release_cone_bound q₁ q₂ κ₁ κ₂ w.length p
      first.width_ge_two second.width_ge_two hp
      (Initialization.release first.toPacketProducer w)
      (fun z _ => Initialization.release_upper first w hw hne z)
      (Initialization.release_negative first.toPacketProducer w)
  have hheight : d + 1 ≤ simulationHeight first.toPacketProducer w (T + d) p :=
    AsyncFullLine.height_cone _ T d p hcone
  have hinput : A w ≠ [] := by
    have := List.length_pos_of_ne_nil hne
    apply List.ne_nil_of_length_pos
    simpa only [advice_len] using this
  have hlanes : ∀ s, PackedTarget.times q₁ second.toPacketProducer (A w) p s ≤ q₁ * d := by
    intro s
    calc
      second.release (A w) (p * q₁ + s.val) ≤
          κ₂ + (q₂ - 1) * max (packetCount q₂ w.length) (q₁ * p + s.val) := by
        simpa only [advice_len, Nat.mul_comm p q₁] using
          second.upper (A w) hmiddle hinput (p * q₁ + s.val)
      _ ≤ q₁ * d := second_stage_release_bound q₁ q₂ κ₂ w.length p
        first.width_ge_two second.width_ge_two hp s
  have hready : ready first.toPacketProducer second.toPacketProducer w p (T + d) :=
    lanesReady_of_generation _ d _ hheight hlanes
  exact ready_mono _ _ w p _ _
    (deadline_le q₁ q₂ κ₁ κ₂ K first.width_ge_two second.width_ge_two) hready

end CellularAutomatas.LocalHorizon.Fusion
