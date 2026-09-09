import CellularAutomatas.proofs.advice_theory.local_horizon.producer
import CellularAutomatas.proofs.advice_theory.local_horizon.machine
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.producer
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.packing_budget
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.prefix_packets
import CellularAutomatas.proofs.advice_theory.marked_prefix.lifted_packets

namespace CellularAutomatas.LocalHorizon

open MarkedPrefix MarkedPrefix.LT

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- Preparation retains the ordinary symbols and adds the dyadic endpoint.
The finite cutoff is the existing exact-packing cutoff, not a machine oracle. -/
def dyadicValid (q : ℕ) (v : Word (α × Bool)) : Prop :=
  v = (Advice.middle_exp α).annotate (v.map Prod.fst) ∧
    2 * q ≤ v.length

def dyadicOutput (F : Advice α Γ) (blank : Γ) :
    Advice (α × Bool) (α × Γ) where
  f v := (prefixTransform dyadicSelector F blank).annotate (v.map Prod.fst)
  len v := by
    simp only [Advice.annotate, List.length_zip, advice_len, min_self, List.length_map]

/-- The previous LT construction is an instance of the local producer
contract. Prefix computation and suffix padding may fire at different times;
only their common deadline is passed to the consumer. -/
noncomputable def dyadicProducer {F : Advice α Γ} (hF : F.IsLtAdvice)
    (blank : Γ) (controller : PrefixController (packingFactor hF.c) α) :
    PacketProducer (packingFactor hF.c) controller.offset
      (dyadicValid (packingFactor hF.c)) (dyadicOutput F blank) := by
  let q := packingFactor hF.c
  have hq : 2 ≤ q := by
    have hlarge := packingFactor_large hF.c
    omega
  letI : NeZero q := ⟨by omega⟩
  apply PacketProducer.of_exists (Producer.C q hF blank controller) hq
    controller.offset_pos
  intro v hv _
  let w := v.map Prod.fst
  have hwlength : w.length = v.length := List.length_map _
  have hn : 2 * q ≤ w.length := by
    simpa only [hwlength] using hv.2
  have hn_two : 2 ≤ w.length := by omega
  let M := dyadicSelector w.length / q
  have hL : 0 < dyadicSelector w.length := dyadicSelector_pos hn_two
  have hdiv : q ∣ dyadicSelector w.length := packingFactor_dvd hn
  have hlength : dyadicSelector w.length = q * M :=
    (Nat.mul_div_cancel' hdiv).symm
  have hM : 0 < M :=
    Nat.div_pos (Nat.le_of_dvd hL hdiv) (by omega)
  have hmarked : v = ReversalPackets.markedWord w (q * M - 1) := by
    calc
      v = (Advice.middle_exp α).annotate w := hv.1
      _ = ReversalPackets.markedWord w (dyadicSelector w.length - 1) :=
        middle_exp_annotate_eq_mapIdx w hn_two
      _ = ReversalPackets.markedWord w (q * M - 1) := by rw [hlength]
  obtain ⟨release, henvelope, hpackets⟩ :=
    Producer.exists_packets q hF blank controller dyadicSelector w M hM hlength
  have hbudget : (q - 1 + hF.c) * M ≤
      (q - 1) * packetCount q v.length := by
    simpa only [packetCount_of_pos q v.length (by omega), M, q, hwlength] using
      packed_cost_le_catchup hF.c w.length hn
  refine ⟨release, fun p => (henvelope p).1, ?_, ?_⟩
  · intro p hp
    show release p ≤ controller.offset + (q - 1) * packetCount q v.length
    calc
      release p ≤ controller.offset +
          max ((q - 1) * p) ((q - 1 + hF.c) * M) := (henvelope p).2
      _ ≤ controller.offset + (q - 1) * packetCount q v.length :=
        Nat.add_le_add_left
          (max_le (Nat.mul_le_mul_left _ hp) hbudget) _
  · intro t p
    show (Producer.C q hF blank controller).comp v t p =
      if t = release p then
        some (SpeedupKx.compress q
          (word_to_config ((prefixTransform dyadicSelector F blank).annotate w)) p)
      else none
    rw [hmarked]
    exact hpackets t p

/-- Concrete instance: both the horizon and all LT-controller machinery are
finite CAs, with no controller assumptions remaining. -/
noncomputable def dyadicPrefixProducer {F : Advice α Γ} (hF : F.IsLtAdvice)
    (blank : Γ) :
    PacketProducer (packingFactor hF.c) (packingFactor hF.c)
      (dyadicValid (packingFactor hF.c)) (dyadicOutput F blank) :=
  dyadicProducer hF blank
    (PrefixPackets.prefixController (packingFactor hF.c)
      (by have hlarge := packingFactor_large hF.c; omega) α)

theorem dyadic_horizon_admissible {F : Advice α Γ} (hF : F.IsLtAdvice)
    (blank : Γ) :
    RTAdmissibleHorizon (packingFactor hF.c) (packingFactor hF.c)
      (dyadicPrefixProducer hF blank).horizon :=
  (dyadicPrefixProducer hF blank).admissible le_rfl

theorem dyadic_readout_eq {F : Advice α Γ} (hF : F.IsLtAdvice)
    (blank : Γ) (v : Word (α × Bool))
    (hv : dyadicValid (packingFactor hF.c) v) :
    letI : NeZero (packingFactor hF.c) :=
      ⟨by have hlarge := packingFactor_large hF.c; omega⟩
    readout (packingFactor hF.c) (dyadicPrefixProducer hF blank).horizon
        (dyadicPrefixProducer hF blank).data v =
      (prefixTransform dyadicSelector F blank).annotate (v.map Prod.fst) := by
  letI : NeZero (packingFactor hF.c) :=
    ⟨by have hlarge := packingFactor_large hF.c; omega⟩
  exact (dyadicPrefixProducer hF blank).readout_eq v hv

/-- The marked LT machine realizes the desired advice only on correctly
prepared inputs above the packing cutoff, not on all marked words. -/
theorem dyadic_isPacketReadoutOn {F : Advice α Γ} (hF : F.IsLtAdvice)
    (blank : Γ) :
    (dyadicOutput F blank).IsPacketReadoutOn (dyadicValid (packingFactor hF.c)) := by
  refine ⟨PacketReadoutMachine.ofProducer (dyadicPrefixProducer hF blank),
    PacketReadoutMachine.contractOfProducer (dyadicPrefixProducer hF blank) le_rfl, ?_⟩
  intro w hw
  exact PacketReadoutMachine.producer_readout_eq (dyadicPrefixProducer hF blank) le_rfl w hw

end CellularAutomatas.LocalHorizon
