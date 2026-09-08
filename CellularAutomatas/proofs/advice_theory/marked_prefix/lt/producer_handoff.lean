import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_config
import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_join
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.packed_exterior

namespace CellularAutomatas.MarkedPrefix.LT.ProducerHandoff

variable {ι σ Γ : Type} [Alphabet ι] [Alphabet σ] [Alphabet Γ] {q : ℕ}

def raw (classified : CellAutomaton ι (Option (Bool × (Fin q → Option σ)))) :
    CellAutomaton ι (Option (Fin q → Option σ)) :=
  classified.map_project (Option.map Prod.snd)

/-- Outside-prefix cells certify padding when their ordinary input packet
arrives. They do not wait for the finite-strip computation to finish. -/
def padding (classified : CellAutomaton ι (Option (Bool × (Fin q → Option σ))))
    (blank : Γ) : CellAutomaton ι (Option (Fin q → Γ)) :=
  classified.map_project fun event =>
    event.bind fun packet => if packet.1 then none else some (fun _ => blank)

def advice (classified : CellAutomaton ι (Option (Bool × (Fin q → Option σ))))
    (producer : CellAutomaton ι (Option (Fin q → Γ))) (blank : Γ) :
    CellAutomaton ι (Option (Fin q → Γ)) :=
  (producer ⨂ padding classified blank).map_project
    (fun outputs => PacketJoin.retain outputs.1 outputs.2)

def pairBlock (input : Fin q → Option σ) (output : Fin q → Γ) :
    Fin q → Option (σ × Γ) :=
  fun i => (input i).map (fun symbol => (symbol, output i))

/-- This is the actual handoff CA: merge computed prefix output with immediate
suffix padding, latch it with the raw input, and preserve absent input cells. -/
def C (classified : CellAutomaton ι (Option (Bool × (Fin q → Option σ))))
    (producer : CellAutomaton ι (Option (Fin q → Γ))) (blank : Γ) :
    CellAutomaton ι (Option (Fin q → Option (σ × Γ))) :=
  (PacketJoin.C (raw classified) (advice classified producer blank)).map_project
    (Option.map fun packets => pairBlock packets.1 packets.2)

omit [Alphabet σ] in
theorem advice_spec_at
    (classified : CellAutomaton ι (Option (Bool × (Fin q → Option σ))))
    (producer : CellAutomaton ι (Option (Fin q → Γ))) (blank : Γ)
    (input : Config ι) (p : ℤ) (inside : Prop) [Decidable inside]
    (rawTime producerTime : ℕ) (inputBlock : Fin q → Option σ)
    (outputBlock : Fin q → Γ)
    (hclassified : ∀ t, classified.comp ⦋input⦌ t p =
      if t = rawTime then some (decide inside, inputBlock) else none)
    (hproducer : ∀ t, producer.comp ⦋input⦌ t p =
      if inside ∧ t = producerTime then some outputBlock else none)
    (hpadding : ¬inside → outputBlock = fun _ => blank) (t : ℕ) :
    (advice classified producer blank).comp ⦋input⦌ t p =
      if t = (if inside then producerTime else rawTime)
        then some outputBlock else none := by
  simp only [advice, padding, comp_of_map_project, ca_zip_comp]
  rw [hclassified, hproducer]
  by_cases hin : inside
  · by_cases ht : t = producerTime <;>
      simp [hin, ht, PacketJoin.retain]
  · rw [hpadding hin]
    by_cases ht : t = rawTime <;>
      simp [hin, ht, PacketJoin.retain]

theorem comp_spec_at
    (classified : CellAutomaton ι (Option (Bool × (Fin q → Option σ))))
    (producer : CellAutomaton ι (Option (Fin q → Γ))) (blank : Γ)
    (input : Config ι) (p : ℤ) (inside : Prop) [Decidable inside]
    (rawTime producerTime : ℕ) (inputBlock : Fin q → Option σ)
    (outputBlock : Fin q → Γ)
    (hclassified : ∀ t, classified.comp ⦋input⦌ t p =
      if t = rawTime then some (decide inside, inputBlock) else none)
    (hproducer : ∀ t, producer.comp ⦋input⦌ t p =
      if inside ∧ t = producerTime then some outputBlock else none)
    (hpadding : ¬inside → outputBlock = fun _ => blank) (t : ℕ) :
    (C classified producer blank).comp ⦋input⦌ t p =
      if t = max rawTime (if inside then producerTime else rawTime)
        then some (pairBlock inputBlock outputBlock) else none := by
  have hraw : ∀ s, (raw classified).comp ⦋input⦌ s p =
      if s = rawTime then some inputBlock else none := by
    intro s
    simp only [raw, comp_of_map_project, hclassified]
    split <;> rfl
  have hjoin := PacketJoin.comp_spec_at
    (raw classified) (advice classified producer blank) input p
    rawTime (if inside then producerTime else rawTime) inputBlock outputBlock
    hraw (advice_spec_at classified producer blank input p inside
      rawTime producerTime inputBlock outputBlock hclassified hproducer hpadding) t
  simp only [C, comp_of_map_project, hjoin]
  by_cases ht : t = max rawTime (if inside then producerTime else rawTime)
  · simp [ht]
  · simp [ht]

def release (κ q M : ℕ) (producerTime : ℕ → ℕ) (p : ℕ) : ℕ :=
  max (κ + (q - 1) * p)
    (if p < M then producerTime p else κ + (q - 1) * p)

/-- Joining introduces no extra synchronization cost. The only producer
timing assumption concerns cells of the finite prefix. -/
theorem release_bounds (κ q M D : ℕ) (producerTime : ℕ → ℕ)
    (hproducer : ∀ p, p < M → producerTime p ≤ κ + D) (p : ℕ) :
    κ + (q - 1) * p ≤ release κ q M producerTime p ∧
      release κ q M producerTime p ≤ κ + max ((q - 1) * p) D := by
  refine ⟨Nat.le_max_left _ _, ?_⟩
  unfold release
  apply max_le
  · exact Nat.add_le_add_left (le_max_left _ _) κ
  · split
    · calc
        producerTime p ≤ κ + D := hproducer p ‹p < M›
        _ ≤ κ + max ((q - 1) * p) D :=
          Nat.add_le_add_left (le_max_right _ _) κ
    · exact Nat.add_le_add_left (le_max_left _ _) κ

variable [NeZero q]

def prefixBlock (selector : BoundedSelector) (F : Advice σ Γ)
    (blank : Γ) (w : Word σ) (p : ℤ) : Fin q → Γ :=
  fun i => (word_to_config (F (w.take (selector w.length)))
    (p * q + (i : ℤ))).getD blank

omit [Alphabet σ] [Alphabet Γ] [NeZero q] in
theorem pairBlock_prefix_eq (selector : BoundedSelector) (F : Advice σ Γ)
    (blank : Γ) (w : Word σ) (p : ℤ) :
    pairBlock (SpeedupKx.compress q (word_to_config w) p)
        (prefixBlock selector F blank w p) =
      SpeedupKx.compress q
        (word_to_config ((prefixTransform selector F blank).annotate w)) p := by
  funext i
  simp only [pairBlock, prefixBlock, SpeedupKx.compress]
  rw [← prefixTransform_config_getD selector F blank w]
  exact (annotated_config_eq (prefixTransform selector F blank) blank w _).symm

omit [Alphabet σ] [Alphabet Γ] in
theorem prefixBlock_eq_padding (selector : BoundedSelector) (F : Advice σ Γ)
    (blank : Γ) (w : Word σ) (M p : ℕ)
    (hlength : selector w.length = q * M) (hp : M ≤ p) :
    prefixBlock (q := q) selector F blank w p = fun _ => blank := by
  have hsize : (F (w.take (selector w.length))).length = q * M := by
    rw [advice_len, selectedPrefix_length, hlength]
  have hout := compress_word_exterior q (F (w.take (selector w.length)))
    M hsize p (Or.inr (by exact_mod_cast hp))
  funext i
  have hslot := congrFun hout i
  change (SpeedupKx.compress q
    (word_to_config (F (w.take (selector w.length)))) p i).getD blank = blank
  rw [hslot]
  rfl

/-- The producer's real prefix events and the raw controller's classifications
fit the consumer's exact compressed annotated-input interface. -/
theorem comp_prefix_spec
    (classified : CellAutomaton ι (Option (Bool × (Fin q → Option σ))))
    (producer : CellAutomaton ι (Option (Fin q → Γ))) (blank : Γ)
    (input : Config ι) (selector : BoundedSelector) (F : Advice σ Γ)
    (w : Word σ) (κ M : ℕ) (producerTime : ℕ → ℕ)
    (hlength : selector w.length = q * M)
    (hclassified : ∀ t p : ℕ, classified.comp ⦋input⦌ t p =
      if t = κ + (q - 1) * p then
        some (decide (p < M), SpeedupKx.compress q (word_to_config w) p)
      else none)
    (hproducer : ∀ t p : ℕ, producer.comp ⦋input⦌ t p =
      if p < M ∧ t = producerTime p then
        some (prefixBlock selector F blank w p) else none)
    (t p : ℕ) :
    (C classified producer blank).comp ⦋input⦌ t p =
      if t = release κ q M producerTime p then
        some (SpeedupKx.compress q
          (word_to_config ((prefixTransform selector F blank).annotate w)) p)
      else none := by
  rw [comp_spec_at classified producer blank input p (p < M)
    (κ + (q - 1) * p) (producerTime p)
    (SpeedupKx.compress q (word_to_config w) p)
    (prefixBlock selector F blank w p)
    (fun s => hclassified s p) (fun s => hproducer s p)
    (fun hp => prefixBlock_eq_padding selector F blank w M p hlength (by omega))]
  rw [pairBlock_prefix_eq]
  rfl

end CellularAutomatas.MarkedPrefix.LT.ProducerHandoff
