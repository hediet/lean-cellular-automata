import CellularAutomatas.proofs.advice_theory.local_horizon.producer
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.raw_pack
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.producer_handoff

namespace CellularAutomatas.LocalHorizon

open CellAutomaton MarkedPrefix

namespace Normalize

variable {α Γ : Type} [Alphabet α] [Alphabet Γ] {q : ℕ} [NeZero q]

/-- A fixed startup delay preserves the raw input while moving the raw
packet diagonal from `q` to `κ`. -/
def raw (q κ : ℕ) [NeZero q] (hq : 2 ≤ q) (α : Type) [Alphabet α] :
    CellAutomaton (Option α) (Option (Fin q → Option α)) :=
  (idCA (Option α)).composeKSteps (LT.RawPack.C q hq α) (κ - q)

theorem raw_spec (κ : ℕ) (hq : 2 ≤ q) (hκ : q ≤ κ)
    (w : Word α) (hne : w ≠ []) (t p : ℕ) :
    (raw q κ hq α).comp w t p =
      if t = κ + (q - 1) * p then
        some (SpeedupKx.compress q (word_to_config w) p) else none := by
  simp only [raw, composeKSteps_comp, idCA.comp_spec]
  by_cases ht : κ - q ≤ t
  · show (if t ≥ κ - q then _ else _) = _
    rw [if_pos ht]
    change (LT.RawPack.C q hq α).comp w (t - (κ - q)) p = _
    rw [LT.RawPack.comp_spec q hq w hne]
    simp only [Int.natCast_nonneg, Int.natAbs_natCast, true_and, LT.RawPack.offset]
    have htime : t - (κ - q) = q + (q - 1) * p ↔
        t = κ + (q - 1) * p := by omega
    simp only [htime]
  · show (if t ≥ κ - q then _ else _) = _
    rw [if_neg ht, if_neg (by omega : t ≠ κ + (q - 1) * p)]
    rfl

def exterior (input : Option (Fin q → Option α)) :
    Option (Fin q → Option (α × Γ)) :=
  input.bind fun packet => if (packet 0).isNone then some (fun _ => none) else none

def interior (joined : Option ((Fin q → Option α) × (Fin q → Γ))) :
    Option (Fin q → Option (α × Γ)) :=
  joined.bind fun (input, advice) =>
    if (input 0).isNone then none else some (LT.ProducerHandoff.pairBlock input advice)

/-- All-border packets bypass the horizon. The raw first slot certifies
the right exterior, so no global length or deadline signal is needed. -/
def handoff {ι : Type} [Alphabet ι]
    (rawSource : CellAutomaton ι (Option (Fin q → Option α)))
    (adviceSource : CellAutomaton ι (Option (Fin q → Γ))) :
    CellAutomaton ι (Option (Fin q → Option (α × Γ))) :=
  (rawSource ⨂ PacketJoin.C rawSource adviceSource).map_project
    fun (rawPacket, joined) => PacketJoin.retain (exterior rawPacket) (interior joined)

theorem handoff_spec_at {ι : Type} [Alphabet ι]
    (rawSource : CellAutomaton ι (Option (Fin q → Option α)))
    (adviceSource : CellAutomaton ι (Option (Fin q → Γ)))
    (input : Config ι) (p : ℤ) (rawTime adviceTime : ℕ)
    (inputBlock : Fin q → Option α) (adviceBlock : Fin q → Γ)
    (hraw : ∀ t, rawSource.comp ⦋input⦌ t p =
      if t = rawTime then some inputBlock else none)
    (hadvice : ∀ t, adviceSource.comp ⦋input⦌ t p =
      if t = adviceTime then some adviceBlock else none)
    (t : ℕ) :
    (handoff rawSource adviceSource).comp ⦋input⦌ t p =
      if t = (if (inputBlock 0).isNone then rawTime else max rawTime adviceTime) then
        some (if (inputBlock 0).isNone then fun _ => none
          else LT.ProducerHandoff.pairBlock inputBlock adviceBlock)
      else none := by
  simp only [handoff, comp_of_map_project, ca_zip_comp]
  rw [PacketJoin.comp_spec_at rawSource adviceSource input p rawTime adviceTime
    inputBlock adviceBlock hraw hadvice t, hraw t]
  simp only [exterior, interior]
  cases hfirst : inputBlock 0 <;>
    simp only [Option.isNone_none, Option.isNone_some,
      Bool.false_eq_true, if_true, if_false] <;>
    split_ifs <;> simp [hfirst, PacketJoin.retain]

omit [Alphabet α] in
theorem first_none_iff (w : Word α) (p : ℕ) :
    (SpeedupKx.compress q (word_to_config w) p 0).isNone = true ↔
      w.length ≤ q * p := by
  have hnonneg : (0 : ℤ) ≤ (p : ℤ) * q := mul_nonneg (by omega) (by omega)
  simp only [SpeedupKx.compress, Fin.val_zero, Nat.cast_zero, add_zero,
    word_to_config, hnonneg, true_and]
  by_cases hp : q * p < w.length
  · have hlt : (p : ℤ) * q < w.length := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using hp : p * q < w.length)
    simp [hlt, Nat.not_le_of_gt hp]
  · have hge : (w.length : ℤ) ≤ (p : ℤ) * q := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.le_of_not_gt hp :
        w.length ≤ p * q)
    simp [not_lt_of_ge hge, Nat.le_of_not_gt hp]

omit [Alphabet α] [NeZero q] in
theorem exterior_packet (w : Word α) (p : ℕ) (hp : w.length ≤ q * p) :
    SpeedupKx.compress q (word_to_config w) p = fun _ => none := by
  funext i
  show word_to_config w ((p : ℤ) * q + (i : ℤ)) = none
  have hbound : (w.length : ℤ) ≤ (p : ℤ) * q + (i : ℤ) := by
    have hbase : (w.length : ℤ) ≤ (q : ℤ) * p := by exact_mod_cast hp
    have hi : (0 : ℤ) ≤ i := Int.natCast_nonneg _
    nlinarith
  simp only [word_to_config, not_lt_of_ge hbound, and_false, dite_false]

omit [Alphabet α] in
theorem position_lt_count (w : Word α) (hne : w ≠ []) (p : ℕ) :
    p < packetCount q w.length ↔ q * p < w.length := by
  have hn := List.length_pos_of_ne_nil hne
  rw [packetCount_of_pos q w.length hn]
  have hq : 0 < q := NeZero.pos q
  constructor
  · intro hp
    show q * p < w.length
    have hle : p ≤ (w.length - 1) / q := by omega
    have hmul := (Nat.le_div_iff_mul_le hq).mp hle
    rw [Nat.mul_comm p q] at hmul
    omega
  · intro hp
    show p < (w.length - 1) / q + 1
    have hle : p * q ≤ w.length - 1 := by
      rw [Nat.mul_comm]
      omega
    have hdiv := (Nat.le_div_iff_mul_le hq).mpr hle
    omega

def annotated {valid : Word α → Prop} (horizon : RealizableHorizon α valid)
    (data : CellAutomaton (Option α) (Fin q → Γ)) : Advice α (α × Γ) where
  f w := (readout q horizon data).annotate w
  len _ := by
    simp only [Advice.annotate, List.length_zip, advice_len, min_self]

omit [Alphabet α] in
theorem pairBlock_sample {valid : Word α → Prop}
    (horizon : RealizableHorizon α valid)
    (data : CellAutomaton (Option α) (Fin q → Γ)) (w : Word α) (p : ℕ) :
    LT.ProducerHandoff.pairBlock (SpeedupKx.compress q (word_to_config w) p)
        (data.comp w (horizon.time w p) p) =
      SpeedupKx.compress q (word_to_config (annotated horizon data w)) p := by
  funext i
  show (word_to_config w ((p : ℤ) * q + (i : ℤ))).map
      (fun a => (a, data.comp w (horizon.time w p) p i)) =
    word_to_config ((readout q horizon data).annotate w) ((p : ℤ) * q + (i : ℤ))
  rw [annotated_config_eq (readout q horizon data) default w]
  have hindex : (p : ℤ) * q + (i : ℤ) = ((q * p + i.val : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hindex]
  by_cases hi : q * p + i.val < w.length
  · have hcast : (↑(q * p + i.val) : ℤ) < w.length := by exact_mod_cast hi
    simp only [word_to_config, Int.natCast_nonneg, hcast, advice_len,
      true_and, dite_true, Option.map_some, Option.getD_some, Int.toNat_natCast]
    congr 2
    rw [readout_getElem q horizon data w (q * p + i.val) hi]
    simp only [Nat.mul_add_div (NeZero.pos q), Nat.div_eq_of_lt i.isLt,
      Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  · have hcast : ¬(↑(q * p + i.val) : ℤ) < w.length := by exact_mod_cast hi
    simp only [word_to_config, hcast, and_false, dite_false, Option.map_none]

def release {valid : Word α → Prop} (κ : ℕ)
    (horizon : RealizableHorizon α valid) (w : Word α) (p : ℕ) : ℕ :=
  if q * p < w.length then max (κ + (q - 1) * p) (horizon.time w p)
  else κ + (q - 1) * p

/-- Normalize arbitrary realizable readout events by locally joining them
with raw packets. Padding bypasses the join, even if an exterior horizon is late. -/
def producer {valid : Word α → Prop} (κ : ℕ)
    (horizon : RealizableHorizon α valid)
    (data : CellAutomaton (Option α) (Fin q → Γ))
    (hadmissible : RTAdmissibleHorizon q κ horizon) :
    PacketProducer q κ valid (annotated horizon data) where
  source := handoff (raw q κ hadmissible.1 α) (events q horizon data)
  release := release (q := q) κ horizon
  width_ge_two := hadmissible.1
  startup_pos := by
    have hwidth := hadmissible.1
    have hstartup := hadmissible.2.1
    omega
  emits := by
    intro w hw hne t p
    have hspec := handoff_spec_at (raw q κ hadmissible.1 α)
      (events q horizon data) (word_to_config w) p
      (κ + (q - 1) * p) (horizon.time w p)
      (SpeedupKx.compress q (word_to_config w) p)
      (data.comp w (horizon.time w p) p)
      (fun s => raw_spec κ hadmissible.1 hadmissible.2.1 w hne s p)
      (fun s => events_spec q horizon data w hw hne s p) t
    show (handoff (raw q κ hadmissible.1 α) (events q horizon data)).comp w t p = _
    rw [hspec]
    by_cases hp : q * p < w.length
    · have hfirst :
          ¬(SpeedupKx.compress q (word_to_config w) p 0).isNone = true := by
        rw [first_none_iff]
        omega
      simp only [hfirst, Bool.false_eq_true, if_false, release, hp, if_true,
        pairBlock_sample horizon data w p]
    · have hfirst := (first_none_iff (q := q) w p).mpr (Nat.le_of_not_gt hp)
      have hpadding := exterior_packet (q := q) (annotated horizon data w) p
        (by simpa only [advice_len] using Nat.le_of_not_gt hp)
      simp only [hfirst, if_true, release, hp, if_false, hpadding]
  lower := by
    intro w _ _ p
    show κ + (q - 1) * p ≤ release κ horizon w p
    unfold release
    split
    · show κ + (q - 1) * p ≤ max (κ + (q - 1) * p) (horizon.time w p)
      exact le_max_left _ _
    · show κ + (q - 1) * p ≤ κ + (q - 1) * p
      exact le_rfl
  deadline := by
    intro w hw hne p hp
    show release κ horizon w p ≤ κ + (q - 1) * packetCount q w.length
    have hraw := Nat.add_le_add_left (Nat.mul_le_mul_left (q - 1) hp) κ
    unfold release
    split_ifs with hinside
    · show max (κ + (q - 1) * p) (horizon.time w p) ≤ _
      exact max_le hraw
        (hadmissible.2.2 w hw hne p ((position_lt_count w hne p).mpr hinside))
    · show κ + (q - 1) * p ≤ _
      exact hraw

end Normalize
end CellularAutomatas.LocalHorizon
