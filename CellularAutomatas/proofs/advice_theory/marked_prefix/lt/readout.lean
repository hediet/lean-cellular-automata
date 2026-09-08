import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.consumer
import CellularAutomatas.proofs.advice_theory.marked_prefix.clock_arithmetic
import CellularAutomatas.proofs.constructions.speedup_k_step

namespace CellularAutomatas.MarkedPrefix.LT

open CellAutomaton

namespace PeriodicPacketReadout

variable (q : ℕ) [NeZero q]

/-- Attach a wall-clock counter and expose the packet source exactly on the
chosen phase modulo `q`. -/
def sampler {α β : Type}
    (source : CellAutomaton α (Fin q → β)) (offset : ℕ) :
    CellAutomaton α (Option (Fin q → β)) where
  Q := source.Q × Fin q
  δ := fun left center right =>
    (source.δ left.1 center.1 right.1, center.2 + 1)
  embed := fun input => (source.embed input, 0)
  project := fun state =>
    if state.2.val = offset % q then some (source.project state.1) else none

theorem sampler_state_spec {α β : Type}
    (source : CellAutomaton α (Fin q → β)) (offset : ℕ)
    (input : Config α) (t : ℕ) (p : ℤ) :
    (sampler q source offset).nextt ⦋input⦌ t p =
      (source.nextt ⦋input⦌ t p,
        ⟨t % q, Nat.mod_lt _ (NeZero.pos q)⟩) := by
  induction t generalizing p with
  | zero =>
      show (sampler q source offset).embed (input p) =
        (source.embed (input p), (0 : Fin q))
      rfl
  | succ t ih =>
      simp only [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      rw [ih (p - 1), ih p, ih (p + 1)]
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change (t % q + 1 % q) % q = (t + 1) % q
        exact (Nat.add_mod t 1 q).symm

theorem sampler_comp_spec {α β : Type}
    (source : CellAutomaton α (Fin q → β)) (offset : ℕ)
    (input : Config α) (t : ℕ) (p : ℤ) :
    (sampler q source offset).comp ⦋input⦌ t p =
      if t % q = offset % q then
        some (source.comp ⦋input⦌ t p)
      else none := by
  change (sampler q source offset).project
    ((sampler q source offset).nextt ⦋input⦌ t p) = _
  rw [sampler_state_spec]
  simp only [sampler, CellAutomaton.comp_apply]

theorem sampler_trace_at {α β : Type}
    (source : CellAutomaton α (Fin q → β)) (offset j : ℕ)
    (input : Config α) :
    (sampler q source offset).trace input (q * j + offset) =
      some (source.trace input (q * j + offset)) := by
  unfold CellAutomaton.trace
  rw [sampler_comp_spec]
  have hphase : (q * j + offset) % q = offset % q := by
    exact Nat.mul_add_mod_self_left q j offset
  rw [if_pos hphase]

/-- Serialize packet events with a local modulo-`q` counter and packet memory.
The wrapper's output is total, and only the wrapped source track communicates
with neighboring cells. -/
def serializer {α β : Type} [Alphabet β]
    (packetSource : CellAutomaton α (Option (Fin q → β))) :
    CellAutomaton α β where
  Q := packetSource.Q × Fin q × (Fin q → β)
  δ := fun left center right =>
    let nextSource := packetSource.δ left.1 center.1 right.1
    match packetSource.project nextSource with
    | some packet => (nextSource, 0, packet)
    | none => (nextSource, center.2.1 + 1, center.2.2)
  embed := fun input => (packetSource.embed input, 0, fun _ => default)
  project := fun state => state.2.2 state.2.1

theorem serializer_source_track {α β : Type} [Alphabet β]
    (packetSource : CellAutomaton α (Option (Fin q → β)))
    (input : Config α) (t : ℕ) (p : ℤ) :
    ((serializer q packetSource).nextt ⦋input⦌ t p).1 =
      packetSource.nextt ⦋input⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ,
        CellAutomaton.next_apply, CellAutomaton.next_apply]
      change
        (match packetSource.project
          (packetSource.δ
            ((serializer q packetSource).nextt ⦋input⦌ t (p - 1)).1
            ((serializer q packetSource).nextt ⦋input⦌ t p).1
            ((serializer q packetSource).nextt ⦋input⦌ t (p + 1)).1) with
        | some packet => (_, (0 : Fin q), packet)
        | none => (_, _, _)).1 =
          packetSource.δ
            (packetSource.nextt ⦋input⦌ t (p - 1))
            (packetSource.nextt ⦋input⦌ t p)
            (packetSource.nextt ⦋input⦌ t (p + 1))
      rw [ih (p - 1), ih p, ih (p + 1)]
      split <;> rfl

theorem serializer_data_step {α β : Type} [Alphabet β]
    (packetSource : CellAutomaton α (Option (Fin q → β)))
    (input : Config α) (t : ℕ) (p : ℤ) :
    ((serializer q packetSource).nextt ⦋input⦌ (t + 1) p).2 =
      match packetSource.comp ⦋input⦌ (t + 1) p with
      | some packet => (0, packet)
      | none =>
          (((serializer q packetSource).nextt ⦋input⦌ t p).2.1 + 1,
            ((serializer q packetSource).nextt ⦋input⦌ t p).2.2) := by
  rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
  change
    (match packetSource.project
      (packetSource.δ
        ((serializer q packetSource).nextt ⦋input⦌ t (p - 1)).1
        ((serializer q packetSource).nextt ⦋input⦌ t p).1
        ((serializer q packetSource).nextt ⦋input⦌ t (p + 1)).1) with
    | some packet => (_, (0 : Fin q), packet)
    | none => (_, _, _)).2 = _
  rw [serializer_source_track q packetSource input t (p - 1),
    serializer_source_track q packetSource input t p,
    serializer_source_track q packetSource input t (p + 1)]
  rw [show
    packetSource.δ
        (packetSource.nextt ⦋input⦌ t (p - 1))
        (packetSource.nextt ⦋input⦌ t p)
        (packetSource.nextt ⦋input⦌ t (p + 1)) =
      packetSource.nextt ⦋input⦌ (t + 1) p by
        rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]]
  simp only [CellAutomaton.comp_apply]
  split <;> rfl

/-- Following a packet event, a silent interval walks through its components
without changing the stored packet. -/
theorem serializer_state_after_packet {α β : Type} [Alphabet β]
    (packetSource : CellAutomaton α (Option (Fin q → β)))
    (input : Config α) (p : ℤ) (sample : ℕ) (packet : Fin q → β)
    (hsample_pos : 0 < sample)
    (hsample :
      packetSource.comp ⦋input⦌ sample p = some packet)
    (hsilent : ∀ m, 0 < m → m < q →
      packetSource.comp ⦋input⦌ (sample + m) p = none) :
    ∀ m (hm : m < q),
      ((serializer q packetSource).nextt
        ⦋input⦌ (sample + m) p).2 =
        (⟨m, hm⟩, packet) := by
  have hat_sample :
      ((serializer q packetSource).nextt ⦋input⦌ sample p).2 =
        ((0 : Fin q), packet) := by
    obtain ⟨sample', rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsample_pos)
    have hstep := serializer_data_step q packetSource input sample' p
    rw [hsample] at hstep
    exact hstep
  intro m
  induction m with
  | zero =>
      intro hm
      simpa only [Nat.add_zero] using hat_sample
  | succ m ih =>
      intro hm
      have hm_lt : m < q := by omega
      have hprev := ih hm_lt
      have hnone :
          packetSource.comp ⦋input⦌ (sample + m + 1) p = none := by
        simpa only [Nat.add_assoc] using
          hsilent (m + 1) (by omega) (by omega)
      have hstep :=
        serializer_data_step q packetSource input (sample + m) p
      rw [hnone, hprev] at hstep
      rw [show sample + (m + 1) = sample + m + 1 by omega]
      rw [hstep]
      apply Prod.ext
      · apply Fin.ext
        change (m + 1 % q) % q = m + 1
        have hone : 1 < q := by omega
        rw [Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt (by omega)]
      · rfl

theorem serializer_comp_after_packet {α β : Type} [Alphabet β]
    (packetSource : CellAutomaton α (Option (Fin q → β)))
    (input : Config α) (p : ℤ) (sample : ℕ) (packet : Fin q → β)
    (hsample_pos : 0 < sample)
    (hsample :
      packetSource.comp ⦋input⦌ sample p = some packet)
    (hsilent : ∀ m, 0 < m → m < q →
      packetSource.comp ⦋input⦌ (sample + m) p = none)
    (r : Fin q) :
    (serializer q packetSource).comp ⦋input⦌ (sample + r) p =
      packet r := by
  have hstate := serializer_state_after_packet q packetSource input p sample
    packet hsample_pos hsample hsilent r r.isLt
  change
    ((serializer q packetSource).nextt
      ⦋input⦌ (sample + r) p).2.2
      ((serializer q packetSource).nextt
        ⦋input⦌ (sample + r) p).2.1 = packet r
  rw [hstate]

/-- Periodically sample and serialize a packet-valued source. -/
def C {α β : Type} [Alphabet β]
    (source : CellAutomaton α (Fin q → β)) (offset : ℕ) :
    CellAutomaton α β :=
  serializer q (sampler q source offset)

theorem unpack_spec {α β : Type} [Alphabet β]
    (source : CellAutomaton α (Fin q → β)) (offset : ℕ)
    (hoffset : 0 < offset) (input : Config α) (j : ℕ) (r : Fin q) :
    (C q source offset).trace input (q * j + r + offset) =
      source.trace input (q * j + offset) r := by
  let sample := q * j + offset
  let packet := source.trace input sample
  have hsample :
      (sampler q source offset).comp ⦋input⦌ sample 0 =
        some packet := by
    change (sampler q source offset).trace input sample = some packet
    dsimp only [sample, packet]
    exact sampler_trace_at q source offset j input
  have hsilent : ∀ m, 0 < m → m < q →
      (sampler q source offset).comp
        ⦋input⦌ (sample + m) 0 = none := by
    intro m hm hmq
    rw [sampler_comp_spec]
    have hphase : (sample + m) % q ≠ offset % q := by
      intro heq
      have hmod :
          sample + m ≡ sample + 0 [MOD q] := by
        change (sample + m) % q = (sample + 0) % q
        simpa only [Nat.add_zero, sample,
          Nat.mul_add_mod_self_left] using heq
      have hmzero : m ≡ 0 [MOD q] :=
        Nat.ModEq.add_left_cancel (Nat.ModEq.refl sample) hmod
      have := hmzero.eq_of_lt_of_lt hmq (NeZero.pos q)
      omega
    rw [if_neg hphase]
  have hserialized := serializer_comp_after_packet q
    (sampler q source offset) input 0 sample packet
    (by dsimp only [sample]; omega) hsample hsilent r
  change (serializer q (sampler q source offset)).comp
    ⦋input⦌ (q * j + r + offset) 0 =
      source.trace input (q * j + offset) r
  simpa only [sample, packet, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hserialized

/-- A correct sample for generation `a+1` is emitted component-by-component
at the exact delayed time `N + offset + q`, where `N = q*a+r`. -/
theorem decode_packet {α β : Type} [Alphabet β]
    (source : CellAutomaton α (Fin q → β)) (offset : ℕ)
    (hoffset : 0 < offset) (input : Config α)
    (a : ℕ) (r : Fin q) (packet : Fin q → β)
    (hpacket :
      source.trace input (offset + q * (a + 1)) = packet) :
    (C q source offset).trace input (q * a + r + offset + q) =
      packet r := by
  calc
    (C q source offset).trace input (q * a + r + offset + q) =
        (C q source offset).trace input (q * (a + 1) + r + offset) := by
          congr 1
          ring
    _ = source.trace input (q * (a + 1) + offset) r :=
      unpack_spec q source offset hoffset input (a + 1) r
    _ = packet r := by
      apply congrFun
      simpa only [Nat.add_comm] using hpacket

end PeriodicPacketReadout

/-- Remove the fixed `offset+q` serialization delay. -/
def exactReadout
    (q : ℕ) [NeZero q]
    {ρ β : Type} [Alphabet ρ] [Alphabet β]
    (source : CellAutomaton (Option ρ) (Fin q → β))
    (offset : ℕ) : SpeedupKSteps where
  α := ρ
  β := β
  C_orig := PeriodicPacketReadout.C q source offset
  k := offset + q
  c := offset + q + 1

theorem exactReadout_spec
    (q : ℕ) [NeZero q]
    {ρ β : Type} [Alphabet ρ] [Alphabet β]
    (source : CellAutomaton (Option ρ) (Fin q → β))
    (offset : ℕ) (hoffset : 0 < offset)
    (controllerWord : Word ρ) (hcontroller : 0 < controllerWord.length)
    (a : ℕ) (r : Fin q)
    (hindex : controllerWord.length - 1 = q * a + r)
    (packet : Fin q → β)
    (hpacket :
      source.trace (word_to_config controllerWord)
        (offset + q * (a + 1)) = packet) :
    (exactReadout q source offset).C.trace
        (word_to_config controllerWord) (controllerWord.length - 1) =
      packet r := by
  have hbound :
      controllerWord.length - 1 + (offset + q) <
        (offset + q + 1) * controllerWord.length :=
    MarkedPrefixClock.constant_speedup_side_condition
      controllerWord.length (offset + q) hcontroller
  calc
    (exactReadout q source offset).C.trace
          (word_to_config controllerWord) (controllerWord.length - 1) =
        (PeriodicPacketReadout.C q source offset).trace
          (word_to_config controllerWord)
          (controllerWord.length - 1 + (offset + q)) := by
            exact (exactReadout q source offset).spec
              controllerWord (controllerWord.length - 1) (by omega) hbound
    _ = (PeriodicPacketReadout.C q source offset).trace
          (word_to_config controllerWord) (q * a + r + offset + q) := by
            congr 1
            omega
    _ = packet r :=
      PeriodicPacketReadout.decode_packet q source offset hoffset
        (word_to_config controllerWord) a r packet hpacket

/-- The complete conditional consumer CA built from an abstract one-shot
`q`-packet producer. -/
def consumerCA
    (q : ℕ) [NeZero q]
    {ρ δ β : Type} [Alphabet ρ] [Alphabet δ] [Alphabet β]
    (producer :
      CellAutomaton (Option ρ) (Option (Fin q → Option δ)))
    (consumer : CellAutomaton (Option δ) β)
    (κ : ℕ) :
    CellAutomaton (Option ρ) β :=
  (exactReadout q (source q producer consumer) κ).C

/-- End-to-end q-general consumer endpoint. A producer satisfying the
one-shot packet contract and affine release envelope yields the original
consumer's final real-time trace, after dead-border normalization,
asynchronous catch-up, periodic serialization, and fixed-delay removal. -/
theorem consumerCA_trace_final
    (q : ℕ) [NeZero q]
    {ρ δ β : Type} [Alphabet ρ] [Alphabet δ] [Alphabet β]
    (producer :
      CellAutomaton (Option ρ) (Option (Fin q → Option δ)))
    (consumer : CellAutomaton (Option δ) β)
    (controllerWord : Word ρ) (v : Word δ)
    (R : ℕ → ℕ) (κ D : ℕ)
    (hq : 2 ≤ q) (hκ : 0 < κ)
    (hlength : controllerWord.length = v.length)
    (hnonempty : 0 < v.length)
    (hproducer : ∀ t p : ℕ,
      producer.comp ⦋word_to_config controllerWord⦌ t (p : ℤ) =
        if t = R p then
          some (SpeedupKx.compress q (word_to_config v) (p : ℤ))
        else none)
    (henvelope : ∀ p,
      κ + (q - 1) * p ≤ R p ∧
        R p ≤ κ + max ((q - 1) * p) D)
    (hcatch :
      D ≤ (q - 1) * ((controllerWord.length - 1) / q + 1)) :
    (consumerCA q producer consumer κ).trace
        (word_to_config controllerWord) (controllerWord.length - 1) =
      consumer.trace (word_to_config v) (controllerWord.length - 1) := by
  let a := (controllerWord.length - 1) / q
  let r : Fin q :=
    ⟨(controllerWord.length - 1) % q,
      Nat.mod_lt _ (by omega)⟩
  let packet : Fin q → β :=
    (normalizedSpeedupAndTrace q consumer).C.trace
      (SpeedupKx.compress q (word_to_config v)) (a + 1)

  have hcontroller : 0 < controllerWord.length := by omega
  have hindex : controllerWord.length - 1 = q * a + r := by
    simpa only [a, r] using
      (Nat.div_add_mod (controllerWord.length - 1) q).symm
  have hagrees :
      (source q producer consumer).trace
          (word_to_config controllerWord) (κ + q * (a + 1)) =
        packet := by
    dsimp only [packet]
    apply source_trace_eq_normalized
      producer consumer controllerWord hcontroller v R κ D (a + 1)
      hq hproducer henvelope
    simpa only [a] using hcatch
  have hreadout :
      (consumerCA q producer consumer κ).trace
          (word_to_config controllerWord) (controllerWord.length - 1) =
        packet r := by
    apply exactReadout_spec q (source q producer consumer)
      κ hκ controllerWord hcontroller a r hindex packet
    exact hagrees
  calc
    (consumerCA q producer consumer κ).trace
          (word_to_config controllerWord) (controllerWord.length - 1) =
        packet r := hreadout
    _ = (normalizedConsumer consumer).C.trace
          (word_to_config v) (q * a + r) := by
        exact (normalizedSpeedupAndTrace q consumer).spec1
    _ = (normalizedConsumer consumer).C.trace
          (word_to_config v) (controllerWord.length - 1) := by
        congr 1
        exact hindex.symm
    _ = consumer.trace
          (word_to_config v) (controllerWord.length - 1) := by
        simpa only [hlength] using
          normalizedConsumer_trace_final consumer v hnonempty

end CellularAutomatas.MarkedPrefix.LT
