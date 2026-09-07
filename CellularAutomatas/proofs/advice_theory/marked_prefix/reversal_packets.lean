import CellularAutomatas.proofs.advice_theory.marked_prefix.delayed_reflection
import CellularAutomatas.proofs.constructions.basic_ca_id
import CellularAutomatas.proofs.constructions.basic_compose_k_steps
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.speedup_compressed
import CellularAutomatas.proofs.constructions.trace_kx

namespace CellularAutomatas.MarkedPrefix.ReversalPackets

open CellAutomaton

variable {α : Type} [Alphabet α]

/-!
# One-shot packets for a reversed prefix

The unique mark at input position `b` launches unit-speed signals in both
directions.  After a fixed three-step startup, the left-going signal samples
three suitable history entries from `DelayedReflection`; the right-going
signal emits an explicitly empty packet.  Thus every nonnegative packet cell
fires exactly once, at distance from the mark.
-/

/-- Mark exactly input position `b`, while retaining the underlying input
letter for the delayed-reflection data path. -/
def markedWord (w : Word α) (b : ℕ) : Word (α × Bool) :=
  w.mapIdx fun i a => (a, decide (i = b))

omit [Alphabet α] in
@[simp]
theorem markedWord_length (w : Word α) (b : ℕ) :
    (markedWord w b).length = w.length := by
  simp [markedWord]

omit [Alphabet α] in
@[simp]
theorem markedWord_getElem (w : Word α) (b i : ℕ)
    (hi : i < (markedWord w b).length) :
    (markedWord w b)[i] =
      (w[i]'(by simpa using hi), decide (i = b)) := by
  simp [markedWord]

omit [Alphabet α] in
@[simp]
theorem markedWord_map_fst (w : Word α) (b : ℕ) :
    (markedWord w b).map Prod.fst = w := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [markedWord]

omit [Alphabet α] in
theorem markedWord_ne_nil (w : Word α) (b : ℕ) (hb : b < w.length) :
    markedWord w b ≠ [] := by
  intro hempty
  have := congrArg List.length hempty
  simp only [markedWord_length, List.length_nil] at this
  omega

/-! ## Unit-speed marker signals with a three-step startup -/

/-- Read the marker bit, treating cells outside the finite word as unmarked. -/
def markerBit : Option (α × Bool) → Bool
  | none => false
  | some (_, marked) => marked

omit [Alphabet α] in
private theorem markerBit_config (w : Word α) (b : ℕ) (hb : b < w.length)
    (p : ℤ) :
    markerBit (word_to_config (markedWord w b) p) =
      decide (p = (b : ℤ)) := by
  unfold word_to_config
  by_cases hp : 0 ≤ p ∧ p < ((markedWord w b).length : ℤ)
  · rw [dif_pos hp]
    unfold markerBit
    rw [markedWord_getElem]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hpcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp.1
    omega
  · rw [dif_neg hp]
    unfold markerBit
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.false_eq_true, decide_eq_true_eq, false_iff]
    intro heq
    subst p
    apply hp
    rw [markedWord_length]
    constructor <;> omega

/-- The first component moves left and the second moves right, both at unit
speed and without leaving a trail. -/
def markerSignals (α : Type) [Alphabet α] :
    CellAutomaton (Option (α × Bool)) (Bool × Bool) where
  Q := Bool × Bool
  δ := fun left _ right => (right.1, left.2)
  embed := fun input =>
    let marked := markerBit input
    (marked, marked)
  project := id

private theorem markerSignals_state (w : Word α) (b : ℕ) (hb : b < w.length)
    (t : ℕ) (p : ℤ) :
    (markerSignals α).nextt (⦋word_to_config (markedWord w b)⦌) t p =
      (decide (p + (t : ℤ) = (b : ℤ)),
        decide (p - (t : ℤ) = (b : ℤ))) := by
  induction t generalizing p with
  | zero =>
      simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply]
      change
        (markerBit (word_to_config (markedWord w b) p),
          markerBit (word_to_config (markedWord w b) p)) = _
      rw [markerBit_config w b hb]
      apply Prod.ext
      · apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        push_cast
        omega
      · apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        push_cast
        omega
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      change
        (((markerSignals α).nextt
            (⦋word_to_config (markedWord w b)⦌) t (p + 1)).1,
          ((markerSignals α).nextt
            (⦋word_to_config (markedWord w b)⦌) t (p - 1)).2) = _
      rw [ih (p + 1), ih (p - 1)]
      apply Prod.ext
      · apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        push_cast
        omega
      · apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        push_cast
        omega

theorem markerSignals_comp (w : Word α) (b : ℕ) (hb : b < w.length)
    (t : ℕ) (p : ℤ) :
    (markerSignals α).comp (markedWord w b) t p =
      (decide (p + (t : ℤ) = (b : ℤ)),
        decide (p - (t : ℤ) = (b : ℤ))) := by
  change (markerSignals α).nextt
    (⦋word_to_config (markedWord w b)⦌) t p = _
  exact markerSignals_state w b hb t p

/-- Preserve the marked input for three steps, then launch both marker
signals.  Consequently no signal is visible before time three. -/
def delayedSignals (α : Type) [Alphabet α] :
    CellAutomaton (Option (α × Bool)) (Bool × Bool) :=
  (CellAutomaton.idCA (Option (α × Bool))).composeKSteps (markerSignals α) 3

/-- Exact delayed signal positions for natural physical positions. -/
theorem delayedSignals_comp (w : Word α) (b : ℕ) (hb : b < w.length)
    (t p : ℕ) :
    (delayedSignals α).comp (markedWord w b) t (p : ℤ) =
      (decide (p ≤ b ∧ t = 3 + (b - p)),
        decide (b ≤ p ∧ t = 3 + (p - b))) := by
  unfold delayedSignals
  rw [CellAutomaton.composeKSteps_comp]
  simp only [CellAutomaton.idCA.comp_spec]
  by_cases ht : 3 ≤ t
  · rw [if_pos ht]
    change (markerSignals α).comp (markedWord w b) (t - 3) (p : ℤ) = _
    rw [markerSignals_comp w b hb]
    apply Prod.ext
    · apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    · apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
  · rw [if_neg ht]
    have ht' : t < 3 := Nat.lt_of_not_ge ht
    have hleft : decide (p ≤ b ∧ t = 3 + (b - p)) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    have hright : decide (b ≤ p ∧ t = 3 + (p - b)) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [hleft, hright]
    rfl

/-! ## Delayed-reflection history -/

/-- Forget the marker and feed the ordinary letters to the delayed reflector. -/
def stream (α : Type) [Alphabet α] :
    CellAutomaton (Option (α × Bool)) (Option α) :=
  (DelayedReflection.ca α).map_embed (Option.map Prod.fst)

theorem stream_comp (w : Word α) (b : ℕ) (t : ℕ) (p : ℤ) :
    (stream α).comp (markedWord w b) t p =
      (DelayedReflection.ca α).comp w t p := by
  change (DelayedReflection.ca α).project
      ((stream α).nextt
        (⦋word_to_config (markedWord w b)⦌) t p) =
    (DelayedReflection.ca α).project
      ((DelayedReflection.ca α).nextt (⦋word_to_config w⦌) t p)
  unfold stream
  rw [map_embed_nextt_word]
  rw [markedWord_map_fst]

/-- Five snapshots are enough for lags `2`, `3`, and `4`. -/
def history (α : Type) [Alphabet α] : TraceKx where
  k := 4
  α := Option (α × Bool)
  β := Option α
  C_orig := stream α

/-- Logical packet residue `r` reads history lag `2+r`. -/
def historySlot (r : Fin 3) : Fin 5 :=
  ⟨2 - r.val, by omega⟩

omit [Alphabet α] in
private theorem historySlot_val (r : Fin 3) :
    (historySlot r).val = 2 - r.val := rfl

/-- Extract the three relevant delayed-stream values from the five-snapshot
history. -/
def readHistoryPacket (values : Fin 5 → Option (Option α)) :
    Fin 3 → Option α :=
  fun r => (values (historySlot r)).getD none

/-- The history CA with its output restricted to the three packet slots. -/
def packetHistory (α : Type) [Alphabet α] :
    CellAutomaton (Option (α × Bool)) (Fin 3 → Option α) :=
  (history α).C.map_project readHistoryPacket

section TraceKxAccess

set_option allowUnsafeReducibility true in
attribute [local reducible] TraceKx.C

private theorem packetHistory_slot (w : Word α) (b : ℕ) (t : ℕ)
    (p : ℤ) (r : Fin 3) :
    (packetHistory α).comp (markedWord w b) t p r =
      (stream α).comp (markedWord w b)
        (t + (historySlot r).val - 4) p := by
  have hstate := TraceKx.state_eq (history α)
    (word_to_config (markedWord w b)) t p (historySlot r)
  have hproject := congrArg (fun q => (history α).C_orig.project q) hstate
  simpa only [packetHistory, readHistoryPacket, comp_of_map_project,
    CellAutomaton.comp_apply, TraceKx.C, Option.getD_some, history] using hproject

end TraceKxAccess

/-! ## Reversed-prefix indexing -/

omit [Alphabet α] in
/-- For a nonnegative logical index, reversing `take (b+1)` is exactly
integer reflection around `b`.  Both sides are `none` beyond the prefix. -/
theorem reversedPrefix_config (w : Word α) (b : ℕ) (hb : b < w.length)
    (i : ℤ) (hi : 0 ≤ i) :
    word_to_config ((w.take (b + 1)).reverse) i =
      word_to_config w ((b : ℤ) - i) := by
  have htake : (w.take (b + 1)).length = b + 1 := by
    simp only [List.length_take]
    omega
  simp only [word_to_config, List.length_reverse, htake]
  split_ifs with hleft hright
  · congr 1
    have hindex :
        (w.take (b + 1)).length - 1 - i.toNat =
          ((b : ℤ) - i).toNat := by
      rw [htake]
      have hicast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi
      omega
    simp only [List.getElem_reverse, hindex, List.getElem_take]
  · omega
  · omega
  · rfl

omit [Alphabet α] in
private theorem reversedPrefix_compress_right (w : Word α) (b p : ℕ)
    (hp : b < p) :
    SpeedupKx.compress 3
        (word_to_config ((w.take (b + 1)).reverse)) (p : ℤ) =
      fun _ => none := by
  funext r
  unfold SpeedupKx.compress word_to_config
  rw [dif_neg]
  simp only [List.length_reverse, List.length_take]
  omega

/-- When the left-going marker signal reaches `p`, the selected history
entries form exactly compressed cells `3*p`, `3*p+1`, and `3*p+2` of the
reversed prefix. -/
theorem packetHistory_at_left_signal (w : Word α) (b p : ℕ)
    (hb : b < w.length) (hp : p ≤ b) :
    (packetHistory α).comp (markedWord w b) (3 + (b - p)) (p : ℤ) =
      SpeedupKx.compress 3
        (word_to_config ((w.take (b + 1)).reverse)) (p : ℤ) := by
  funext r
  rw [packetHistory_slot]
  rw [stream_comp w b]
  rw [DelayedReflection.comp_spec w (by
    exact List.ne_nil_of_length_pos (by omega))]
  unfold SpeedupKx.compress
  norm_num only [Nat.cast_ofNat]
  conv_rhs =>
    rw [show (p : ℤ) * (3 : ℤ) + (r.val : ℤ) =
      3 * (p : ℤ) + (r.val : ℤ) by ring]
  rw [reversedPrefix_config w b hb
    (3 * (p : ℤ) + (r.val : ℤ)) (by positivity)]
  split_ifs with harrival
  · congr 1
    simp only [historySlot_val] at harrival ⊢
    omega
  · have hnegative :
        (b : ℤ) - (3 * (p : ℤ) + (r.val : ℤ)) < 0 := by
      simp only [historySlot_val] at harrival
      omega
    rw [word_to_config_apply, dif_neg]
    omega

/-! ## Packet producer -/

/-- One-shot reversed-prefix packet producer. -/
def P (α : Type) [Alphabet α] :
    CellAutomaton (Option (α × Bool)) (Option (Fin 3 → Option α)) :=
  ((packetHistory α) ⨂ (delayedSignals α)).map_project
    (fun (packet, signals) =>
      if signals.1 then
        some packet
      else if signals.2 then
        some (fun _ => none)
      else
        none)

/-- Exact one-shot specification at every natural physical position and
time.  In particular, positions strictly to the right of the mark still fire
and carry an all-`none` packet. -/
theorem comp_spec (w : Word α) (b : ℕ) (hb : b < w.length) (t p : ℕ) :
    (P α).comp (markedWord w b) t (p : ℤ) =
      if t = 3 + Int.natAbs ((p : ℤ) - (b : ℤ)) then
        some (SpeedupKx.compress 3
          (word_to_config ((w.take (b + 1)).reverse)) (p : ℤ))
      else
        none := by
  unfold P
  simp only [comp_of_map_project, ca_zip_comp]
  rw [delayedSignals_comp w b hb]
  by_cases hp : p ≤ b
  · have habs : Int.natAbs ((p : ℤ) - (b : ℤ)) = b - p := by
      omega
    rw [habs]
    by_cases ht : t = 3 + (b - p)
    · subst t
      simpa [hp] using
        congrArg some (packetHistory_at_left_signal w b p hb hp)
    · have hright :
          ¬(b ≤ p ∧ t = 3 + (p - b)) := by
        rintro ⟨hbp, htime⟩
        apply ht
        omega
      rw [if_neg ht]
      have hleftBool :
          decide (p ≤ b ∧ t = 3 + (b - p)) = false := by
        simp [ht]
      have hrightBool :
          decide (b ≤ p ∧ t = 3 + (p - b)) = false :=
        decide_eq_false hright
      rw [hleftBool, hrightBool]
      rfl
  · have hbp : b < p := Nat.lt_of_not_ge hp
    have habs : Int.natAbs ((p : ℤ) - (b : ℤ)) = p - b := by
      omega
    rw [habs]
    by_cases ht : t = 3 + (p - b)
    · subst t
      simpa [hp, hbp.le] using
        congrArg some (reversedPrefix_compress_right w b p hbp).symm
    · rw [if_neg ht]
      have hleftBool :
          decide (p ≤ b ∧ t = 3 + (b - p)) = false := by
        simp [hp]
      have hrightBool :
          decide (b ≤ p ∧ t = 3 + (p - b)) = false := by
        simp [ht]
      rw [hleftBool, hrightBool]
      rfl

end CellularAutomatas.MarkedPrefix.ReversalPackets
