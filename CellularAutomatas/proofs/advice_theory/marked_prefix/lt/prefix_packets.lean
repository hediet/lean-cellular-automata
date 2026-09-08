import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.raw_pack
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.prefix_controller
import CellularAutomatas.proofs.advice_theory.marked_prefix.reversal_packets

namespace CellularAutomatas.MarkedPrefix.LT.PrefixPackets

open CellAutomaton

variable {α : Type} [Alphabet α]

/-- Boundary information retained permanently after a block is classified. -/
structure BoundaryFlags where
  atLeft : Bool
  atRight : Bool
deriving DecidableEq, Inhabited, Fintype

instance : Alphabet BoundaryFlags where

/-- A block is either in the selected prefix or certified as padding. -/
inductive BlockClass
  | inside (boundary : BoundaryFlags)
  | padding
deriving DecidableEq, Inhabited, Fintype

instance : Alphabet BlockClass where

/-- One-shot initialization payload for a cell of the finite producer. -/
structure Initialization (q : ℕ) (α : Type) where
  packet : Fin q → Option α
  boundary : BoundaryFlags
deriving DecidableEq, Inhabited, Fintype

instance (q : ℕ) (α : Type) [Alphabet α] :
    Alphabet (Initialization q α) where

/-- Observable prefix-packet interface. `initialization` is a one-shot event;
the boundary and padding fields are permanent after classification. -/
@[ext] structure Output (q : ℕ) (α : Type) where
  initialization : Option (Initialization q α)
  boundary : Option BoundaryFlags
  paddingReady : Bool
deriving DecidableEq, Inhabited, Fintype

instance (q : ℕ) (α : Type) [Alphabet α] :
    Alphabet (Output q α) where

/-- Discard the marker bits while preserving genuine absent input cells. -/
def stripPacket {q : ℕ} {α : Type}
    (packet : Fin q → Option (α × Bool)) : Fin q → Option α :=
  fun r => (packet r).map Prod.fst

/-- Read the marker from the final slot of a packet. Under exact `q`-packing
of the marked prefix, this is exactly the endpoint test. -/
def endMarker (q : ℕ) (hq : 2 ≤ q)
    (packet : Fin q → Option (α × Bool)) : Bool :=
  match packet ⟨q - 1, by omega⟩ with
  | some (_, marked) => marked
  | none => false

/-- Expected permanent classification of physical block `p`. -/
def expectedClass (M p : ℕ) : BlockClass :=
  if p < M then
    .inside ⟨decide (p = 0), decide (p + 1 = M)⟩
  else
    .padding

/-- Classification uses only the previous physical cell and the marker in
the packet arriving now. -/
def classify (left : Option BlockClass) (marked : Bool) : BlockClass :=
  match left with
  | none => .inside ⟨true, marked⟩
  | some (.inside boundary) =>
      if boundary.atRight then
        .padding
      else
        .inside ⟨false, marked⟩
  | some .padding => .padding

private theorem classify_expected (M p : ℕ)
    (marked : Bool) (hmarked : marked = decide (p + 2 = M)) :
    classify (some (expectedClass M p)) marked =
      expectedClass M (p + 1) := by
  subst marked
  unfold expectedClass classify
  split_ifs <;> simp_all <;> omega

private theorem classify_first (M : ℕ) (hM : 0 < M) (marked : Bool)
    (hmarked : marked = decide (1 = M)) :
    classify none marked = expectedClass M 0 := by
  subst marked
  simp [classify, expectedClass, hM]

/-- Read a marker bit from a marked input configuration. -/
def markerBit : Option (α × Bool) → Bool
  | some (_, marked) => marked
  | none => false

omit [Alphabet α] in
private theorem markerBit_config (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (i : ℤ) :
    markerBit
        (word_to_config
          (ReversalPackets.markedWord w (L - 1)) i) =
      decide (i = (L - 1 : ℕ)) := by
  unfold word_to_config
  by_cases hi :
      0 ≤ i ∧
        i < ((ReversalPackets.markedWord w (L - 1)).length : ℤ)
  · rw [dif_pos hi]
    unfold markerBit
    rw [ReversalPackets.markedWord_getElem]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hcast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi.1
    omega
  · rw [dif_neg hi]
    unfold markerBit
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.false_eq_true, decide_eq_true_eq, false_iff]
    intro heq
    apply hi
    rw [ReversalPackets.markedWord_length]
    constructor <;> omega

omit [Alphabet α] in
private theorem stripPacket_compress (q : ℕ) (w : Word α) (b p : ℕ) :
    stripPacket
        (SpeedupKx.compress q
          (word_to_config (ReversalPackets.markedWord w b)) (p : ℤ)) =
      SpeedupKx.compress q (word_to_config w) (p : ℤ) := by
  funext r
  unfold stripPacket SpeedupKx.compress word_to_config
  by_cases hi :
      0 ≤ (p : ℤ) * q + (r.val : ℤ) ∧
        (p : ℤ) * q + (r.val : ℤ) <
          ((ReversalPackets.markedWord w b).length : ℤ)
  · rw [dif_pos hi]
    have hi' :
        0 ≤ (p : ℤ) * q + (r.val : ℤ) ∧
          (p : ℤ) * q + (r.val : ℤ) < (w.length : ℤ) := by
      simpa only [ReversalPackets.markedWord_length] using hi
    rw [dif_pos hi', ReversalPackets.markedWord_getElem]
    rfl
  · rw [dif_neg hi]
    have hi' :
        ¬(0 ≤ (p : ℤ) * q + (r.val : ℤ) ∧
          (p : ℤ) * q + (r.val : ℤ) < (w.length : ℤ)) := by
      simpa only [ReversalPackets.markedWord_length] using hi
    rw [dif_neg hi']
    rfl

omit [Alphabet α] in
private theorem compress_take_eq (q L M p : ℕ) (w : Word α)
    (hLM : L = q * M) (hle : L ≤ w.length) (hp : p < M) :
    SpeedupKx.compress q (word_to_config w) (p : ℤ) =
      SpeedupKx.compress q (word_to_config (w.take L)) (p : ℤ) := by
  funext r
  unfold SpeedupKx.compress word_to_config
  have hindex :
      0 ≤ (p : ℤ) * q + (r.val : ℤ) ∧
        (p : ℤ) * q + (r.val : ℤ) < (L : ℤ) := by
    constructor
    · positivity
    · exact_mod_cast
        (calc
          p * q + r.val < p * q + q := Nat.add_lt_add_left r.isLt _
          _ = (p + 1) * q := by ring
          _ ≤ M * q := Nat.mul_le_mul_right q (by omega)
          _ = L := by rw [hLM, Nat.mul_comm])
  have hword :
      0 ≤ (p : ℤ) * q + (r.val : ℤ) ∧
        (p : ℤ) * q + (r.val : ℤ) < (w.length : ℤ) := by
    constructor
    · exact hindex.1
    · exact lt_of_lt_of_le hindex.2 (by exact_mod_cast hle)
  have htake : (w.take L).length = L := by
    simp [List.length_take, hle]
  rw [dif_pos hword, dif_pos (by simpa only [htake] using hindex)]
  congr 1
  exact List.getElem_take.symm

omit [Alphabet α] in
theorem endMarker_compress (q : ℕ) (hq : 2 ≤ q)
    (w : Word α) (L M p : ℕ) (hL : 0 < L) (hle : L ≤ w.length)
    (hLM : L = q * M) :
    endMarker q hq
        (SpeedupKx.compress q
          (word_to_config
            (ReversalPackets.markedWord w (L - 1))) (p : ℤ)) =
      decide (p + 1 = M) := by
  unfold endMarker SpeedupKx.compress
  change markerBit
      (word_to_config
        (ReversalPackets.markedWord w (L - 1))
        ((p : ℤ) * q + (q - 1 : ℕ))) =
    decide (p + 1 = M)
  rw [markerBit_config w L hL hle]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro heq
    have heqNat :
        p * q + (q - 1) = L - 1 := by
      exact_mod_cast heq
    have hsum : p * q + (q - 1) + 1 = L := by omega
    have heq' :
        q * (p + 1) = q * M := by
      calc
        q * (p + 1) = p * q + q := by ring
        _ = p * q + (q - 1) + 1 := by omega
        _ = L := hsum
        _ = q * M := hLM
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) heq'
  · intro heq
    subst M
    have hqcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
    rw [hqcast]
    rw [hLM]
    rw [Int.ofNat_sub]
    push_cast
    ring
    omega

/-- Retain an existing classification; otherwise classify a raw event. -/
def nextClass (q : ℕ) (hq : 2 ≤ q)
    (old left : Option BlockClass)
    (event : Option (Fin q → Option (α × Bool))) : Option BlockClass :=
  match old with
  | some cls => some cls
  | none =>
      event.map fun packet => classify left (endMarker q hq packet)

/-- Convert a newly classified interior packet to its initialization event. -/
def initializationFor {q : ℕ} {α : Type}
    (packet : Fin q → Option (α × Bool)) (cls : BlockClass) :
    Option (Initialization q α) :=
  match cls with
  | .inside boundary => some ⟨stripPacket packet, boundary⟩
  | .padding => none

/-- A fresh initialization is emitted only on the transition that first
classifies this cell. -/
def nextFresh (q : ℕ) (hq : 2 ≤ q)
    (old left : Option BlockClass)
    (event : Option (Fin q → Option (α × Bool))) :
    Option (Initialization q α) :=
  match old, event with
  | none, some packet =>
      initializationFor packet (classify left (endMarker q hq packet))
  | _, _ => none

structure State (Q : Type) (q : ℕ) (α : Type) where
  raw : Q
  classification : Option BlockClass
  fresh : Option (Initialization q α)
deriving DecidableEq, Inhabited, Fintype

instance (Q : Type) (q : ℕ) (α : Type)
    [Alphabet Q] [Alphabet α] : Alphabet (State Q q α) where

private abbrev rawCA (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] :=
  RawPack.C q hq (α × Bool)

/-- Online prefix isolation driven directly by raw packet arrivals. -/
def C (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] :
    CellAutomaton (Option (α × Bool)) (Output q α) where
  Q := State (rawCA q hq α).Q q α
  δ := fun left center right =>
    let nextRaw :=
      (rawCA q hq α).δ left.raw center.raw right.raw
    let event := (rawCA q hq α).project nextRaw
    ⟨nextRaw,
      nextClass q hq center.classification left.classification event,
      nextFresh q hq center.classification left.classification event⟩
  embed := fun input =>
    ⟨(rawCA q hq α).embed input, none, none⟩
  project := fun state =>
    ⟨state.fresh,
      match state.classification with
      | some (.inside boundary) => some boundary
      | _ => none,
      decide (state.classification = some .padding)⟩

private theorem raw_state (q : ℕ) (hq : 2 ≤ q)
    (c : Config (Option (α × Bool))) (t : ℕ) (p : ℤ) :
    ((C q hq α).nextt ⦋c⦌ t p).raw =
      (rawCA q hq α).nextt ⦋c⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ,
        CellAutomaton.next_apply, CellAutomaton.next_apply]
      change
        (rawCA q hq α).δ
            ((C q hq α).nextt ⦋c⦌ t (p - 1)).raw
            ((C q hq α).nextt ⦋c⦌ t p).raw
            ((C q hq α).nextt ⦋c⦌ t (p + 1)).raw =
          (rawCA q hq α).δ
            ((rawCA q hq α).nextt ⦋c⦌ t (p - 1))
            ((rawCA q hq α).nextt ⦋c⦌ t p)
            ((rawCA q hq α).nextt ⦋c⦌ t (p + 1))
      rw [ih, ih, ih]

private theorem classification_succ (q : ℕ) (hq : 2 ≤ q)
    (c : Config (Option (α × Bool))) (t : ℕ) (p : ℤ) :
    ((C q hq α).nextt ⦋c⦌ (t + 1) p).classification =
      nextClass q hq
        ((C q hq α).nextt ⦋c⦌ t p).classification
        ((C q hq α).nextt ⦋c⦌ t (p - 1)).classification
        ((rawCA q hq α).comp ⦋c⦌ (t + 1) p) := by
  rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
  change nextClass q hq _ _ ((rawCA q hq α).project
      ((rawCA q hq α).δ
        ((C q hq α).nextt ⦋c⦌ t (p - 1)).raw
        ((C q hq α).nextt ⦋c⦌ t p).raw
        ((C q hq α).nextt ⦋c⦌ t (p + 1)).raw)) = _
  rw [CellAutomaton.comp_apply, CellAutomaton.nextt_succ,
    CellAutomaton.next_apply]
  rw [raw_state q hq c t (p - 1), raw_state q hq c t p,
    raw_state q hq c t (p + 1)]

private theorem fresh_succ (q : ℕ) (hq : 2 ≤ q)
    (c : Config (Option (α × Bool))) (t : ℕ) (p : ℤ) :
    ((C q hq α).nextt ⦋c⦌ (t + 1) p).fresh =
      nextFresh q hq
        ((C q hq α).nextt ⦋c⦌ t p).classification
        ((C q hq α).nextt ⦋c⦌ t (p - 1)).classification
        ((rawCA q hq α).comp ⦋c⦌ (t + 1) p) := by
  rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
  change nextFresh q hq _ _ ((rawCA q hq α).project
      ((rawCA q hq α).δ
        ((C q hq α).nextt ⦋c⦌ t (p - 1)).raw
        ((C q hq α).nextt ⦋c⦌ t p).raw
        ((C q hq α).nextt ⦋c⦌ t (p + 1)).raw)) = _
  rw [CellAutomaton.comp_apply, CellAutomaton.nextt_succ,
    CellAutomaton.next_apply]
  rw [raw_state q hq c t (p - 1), raw_state q hq c t p,
    raw_state q hq c t (p + 1)]

private theorem classification_none_of_raw_none
    (q : ℕ) (hq : 2 ≤ q) (c : Config (Option (α × Bool)))
    (t : ℕ) (p : ℤ)
    (hraw : ∀ s, s ≤ t → (rawCA q hq α).comp ⦋c⦌ s p = none) :
    ((C q hq α).nextt ⦋c⦌ t p).classification = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [classification_succ]
      rw [ih (fun s hs => hraw s (by omega)), hraw (t + 1) (by omega)]
      rfl

private theorem classification_at_event
    (q : ℕ) (hq : 2 ≤ q) (c : Config (Option (α × Bool)))
    (τ : ℕ) (p : ℤ) (packet : Fin q → Option (α × Bool))
    (hτ : 0 < τ)
    (hbefore : ∀ s, s < τ →
      (rawCA q hq α).comp ⦋c⦌ s p = none)
    (hevent : (rawCA q hq α).comp ⦋c⦌ τ p = some packet)
    (left : Option BlockClass)
    (hleft :
      ((C q hq α).nextt ⦋c⦌ (τ - 1) (p - 1)).classification = left) :
    ((C q hq α).nextt ⦋c⦌ τ p).classification =
      some (classify left (endMarker q hq packet)) := by
  rw [show τ = (τ - 1) + 1 by omega, classification_succ]
  have hevent' :
      (rawCA q hq α).comp ⦋c⦌ (τ - 1 + 1) p = some packet := by
    simpa [Nat.sub_add_cancel hτ] using hevent
  rw [classification_none_of_raw_none q hq c (τ - 1) p
    (fun s hs => hbefore s (by omega)), hleft, hevent']
  rfl

private theorem fresh_at_event
    (q : ℕ) (hq : 2 ≤ q) (c : Config (Option (α × Bool)))
    (τ : ℕ) (p : ℤ) (packet : Fin q → Option (α × Bool))
    (hτ : 0 < τ)
    (hbefore : ∀ s, s < τ →
      (rawCA q hq α).comp ⦋c⦌ s p = none)
    (hevent : (rawCA q hq α).comp ⦋c⦌ τ p = some packet)
    (left : Option BlockClass)
    (hleft :
      ((C q hq α).nextt ⦋c⦌ (τ - 1) (p - 1)).classification = left) :
    ((C q hq α).nextt ⦋c⦌ τ p).fresh =
      initializationFor packet (classify left (endMarker q hq packet)) := by
  rw [show τ = (τ - 1) + 1 by omega, fresh_succ]
  have hevent' :
      (rawCA q hq α).comp ⦋c⦌ (τ - 1 + 1) p = some packet := by
    simpa [Nat.sub_add_cancel hτ] using hevent
  rw [classification_none_of_raw_none q hq c (τ - 1) p
    (fun s hs => hbefore s (by omega)), hleft, hevent']
  rfl

private theorem classification_persistent
    (q : ℕ) (hq : 2 ≤ q) (c : Config (Option (α × Bool)))
    (τ : ℕ) (p : ℤ) (cls : BlockClass)
    (hat :
      ((C q hq α).nextt ⦋c⦌ τ p).classification = some cls) :
    ∀ t, τ ≤ t →
      ((C q hq α).nextt ⦋c⦌ t p).classification = some cls := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hat
  | succ t _ ih =>
      rw [classification_succ, ih]
      rfl

/-- The prefix classifier uses the raw packet baseline without another
position-dependent delay. -/
def release (q p : ℕ) : ℕ :=
  RawPack.offset q + (q - 1) * p

private theorem exact_blocks (q L : ℕ) (hdiv : q ∣ L) :
    L = q * (L / q) := by
  calc
    L = L / q * q := (Nat.div_mul_cancel hdiv).symm
    _ = q * (L / q) := Nat.mul_comm _ _

private theorem block_count_pos (q L : ℕ)
    (hL : 0 < L) (hdiv : q ∣ L) :
    0 < L / q := by
  have hblocks := exact_blocks q L hdiv
  by_contra hzero
  simp only [Nat.not_lt, Nat.le_zero] at hzero
  rw [hzero, Nat.mul_zero] at hblocks
  omega

omit [Alphabet α] in
private theorem marked_ne_nil (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) :
    ReversalPackets.markedWord w (L - 1) ≠ [] :=
  ReversalPackets.markedWord_ne_nil w (L - 1) (by omega)

private theorem raw_at_release (q : ℕ) (hq : 2 ≤ q)
    (w : Word α) (L p : ℕ) (hL : 0 < L) (hle : L ≤ w.length) :
    (rawCA q hq α).comp
        (ReversalPackets.markedWord w (L - 1))
        (release q p) (p : ℤ) =
      some (SpeedupKx.compress q
        (word_to_config (ReversalPackets.markedWord w (L - 1)))
        (p : ℤ)) := by
  exact RawPack.positive_spec q hq _
    (marked_ne_nil w L hL hle) p

private theorem raw_before_release (q : ℕ) (hq : 2 ≤ q)
    (w : Word α) (L p s : ℕ) (hL : 0 < L) (hle : L ≤ w.length)
    (hs : s < release q p) :
    (rawCA q hq α).comp
        (ReversalPackets.markedWord w (L - 1)) s (p : ℤ) = none := by
  rw [RawPack.comp_spec q hq _ (marked_ne_nil w L hL hle)]
  rw [if_neg]
  intro hevent
  simp only [Int.natCast_nonneg, Int.natAbs_natCast, true_and] at hevent
  exact (Nat.ne_of_lt hs) (by simpa [release] using hevent)

private theorem raw_negative (q : ℕ) (hq : 2 ≤ q)
    (w : Word α) (L : ℕ) (hL : 0 < L) (hle : L ≤ w.length)
    (t : ℕ) (p : ℤ) (hp : p < 0) :
    (rawCA q hq α).comp
        (ReversalPackets.markedWord w (L - 1)) t p = none := by
  rw [RawPack.comp_spec q hq _ (marked_ne_nil w L hL hle)]
  simp [show ¬0 ≤ p by omega]

/-- At its raw packet time, every natural cell has already received the
classification of its left neighbor. Hence endpoint discovery adds no
linear delay. -/
theorem classification_at_release
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (p : ℕ) :
    ((C q hq α).nextt
        (ReversalPackets.markedWord w (L - 1))
        (release q p) (p : ℤ)).classification =
      some (expectedClass (L / q) p) := by
  let packet : Fin q → Option (α × Bool) :=
    SpeedupKx.compress q
      (word_to_config (ReversalPackets.markedWord w (L - 1))) (p : ℤ)
  have hM : 0 < L / q := block_count_pos q L hL hdiv
  induction p with
  | zero =>
      have hleft :
          ((C q hq α).nextt
              (ReversalPackets.markedWord w (L - 1))
              (release q 0 - 1) (-1)).classification = none := by
        apply classification_none_of_raw_none
        intro s _
        exact raw_negative q hq w L hL hle s (-1) (by omega)
      calc
        ((C q hq α).nextt
            (ReversalPackets.markedWord w (L - 1))
            (release q 0) (0 : ℤ)).classification =
            some (classify none (endMarker q hq packet)) := by
          apply classification_at_event q hq
            (word_to_config
              (ReversalPackets.markedWord w (L - 1)))
            (release q 0) 0 packet
          · unfold release RawPack.offset
            omega
          · intro s hs
            exact raw_before_release q hq w L 0 s hL hle hs
          · exact raw_at_release q hq w L 0 hL hle
          · exact hleft
        _ = some (expectedClass (L / q) 0) := by
          congr 1
          apply classify_first (L / q) hM
          exact endMarker_compress q hq w L (L / q) 0 hL hle
            (exact_blocks q L hdiv)
  | succ p ih =>
      let previousClass := expectedClass (L / q) p
      have hleft :
          ((C q hq α).nextt
              (ReversalPackets.markedWord w (L - 1))
              (release q (p + 1) - 1) (p : ℤ)).classification =
            some previousClass := by
        apply classification_persistent q hq
          (word_to_config
            (ReversalPackets.markedWord w (L - 1)))
          (release q p) (p : ℤ) previousClass ih
        unfold release
        have hgap : 0 < q - 1 := by omega
        rw [Nat.mul_add, Nat.mul_one]
        omega
      let currentPacket : Fin q → Option (α × Bool) :=
        SpeedupKx.compress q
          (word_to_config (ReversalPackets.markedWord w (L - 1)))
          ((p + 1 : ℕ) : ℤ)
      calc
        ((C q hq α).nextt
            (ReversalPackets.markedWord w (L - 1))
            (release q (p + 1)) ((p + 1 : ℕ) : ℤ)).classification =
            some (classify (some previousClass)
              (endMarker q hq currentPacket)) := by
          apply classification_at_event q hq
            (word_to_config
              (ReversalPackets.markedWord w (L - 1)))
            (release q (p + 1)) (p + 1) currentPacket
          · unfold release RawPack.offset
            omega
          · intro s hs
            exact raw_before_release q hq w L (p + 1) s hL hle hs
          · exact raw_at_release q hq w L (p + 1) hL hle
          · simpa only [Int.natCast_add, Int.natCast_one,
              add_sub_cancel_right] using hleft
        _ = some (expectedClass (L / q) (p + 1)) := by
          congr 1
          apply classify_expected (L / q) p
          exact endMarker_compress q hq w L (L / q) (p + 1)
            hL hle (exact_blocks q L hdiv)

/-- The classification and boundary bits remain fixed after release. -/
theorem classification_spec
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (p t : ℕ) (ht : release q p ≤ t) :
    ((C q hq α).nextt
        (ReversalPackets.markedWord w (L - 1))
        t (p : ℤ)).classification =
      some (expectedClass (L / q) p) :=
  classification_persistent q hq
    (word_to_config (ReversalPackets.markedWord w (L - 1)))
    (release q p) (p : ℤ) (expectedClass (L / q) p)
    (classification_at_release q hq w L hL hle hdiv p) t ht

private theorem fresh_at_event_of_class
    (q : ℕ) (hq : 2 ≤ q) (c : Config (Option (α × Bool)))
    (τ : ℕ) (p : ℤ) (packet : Fin q → Option (α × Bool))
    (cls : BlockClass) (hτ : 0 < τ)
    (hbefore : ∀ s, s < τ →
      (rawCA q hq α).comp ⦋c⦌ s p = none)
    (hevent : (rawCA q hq α).comp ⦋c⦌ τ p = some packet)
    (hclass :
      ((C q hq α).nextt ⦋c⦌ τ p).classification = some cls) :
    ((C q hq α).nextt ⦋c⦌ τ p).fresh =
      initializationFor packet cls := by
  let left :=
    ((C q hq α).nextt ⦋c⦌ (τ - 1) (p - 1)).classification
  have hcomputed := classification_at_event q hq c τ p packet hτ
    hbefore hevent left rfl
  have hcls :
      cls = classify left (endMarker q hq packet) := by
    exact Option.some.inj (hclass.symm.trans hcomputed)
  rw [hcls]
  exact fresh_at_event q hq c τ p packet hτ hbefore hevent left rfl

private theorem fresh_none_of_raw_none
    (q : ℕ) (hq : 2 ≤ q) (c : Config (Option (α × Bool)))
    (t : ℕ) (p : ℤ)
    (hraw : ∀ s, s ≤ t → (rawCA q hq α).comp ⦋c⦌ s p = none) :
    ((C q hq α).nextt ⦋c⦌ t p).fresh = none := by
  cases t with
  | zero => rfl
  | succ t =>
      rw [fresh_succ]
      rw [classification_none_of_raw_none q hq c t p
        (fun s hs => hraw s (by omega)), hraw (t + 1) (by omega)]
      rfl

private theorem fresh_none_after_classification
    (q : ℕ) (hq : 2 ≤ q) (c : Config (Option (α × Bool)))
    (τ t : ℕ) (p : ℤ) (cls : BlockClass)
    (hat :
      ((C q hq α).nextt ⦋c⦌ τ p).classification = some cls)
    (ht : τ < t) :
    ((C q hq α).nextt ⦋c⦌ t p).fresh = none := by
  rw [show t = (t - 1) + 1 by omega, fresh_succ]
  rw [classification_persistent q hq c τ p cls hat (t - 1) (by omega)]
  rfl

private theorem fresh_at_release_spec
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (p : ℕ) :
    ((C q hq α).nextt
        (ReversalPackets.markedWord w (L - 1))
        (release q p) (p : ℤ)).fresh =
      if p < L / q then
        some
          ⟨SpeedupKx.compress q
              (word_to_config (w.take L)) (p : ℤ),
            ⟨decide (p = 0), decide (p + 1 = L / q)⟩⟩
      else
        none := by
  let packet : Fin q → Option (α × Bool) :=
    SpeedupKx.compress q
      (word_to_config (ReversalPackets.markedWord w (L - 1))) (p : ℤ)
  calc
    ((C q hq α).nextt
        (ReversalPackets.markedWord w (L - 1))
        (release q p) (p : ℤ)).fresh =
        initializationFor packet (expectedClass (L / q) p) := by
      apply fresh_at_event_of_class q hq
        (word_to_config
          (ReversalPackets.markedWord w (L - 1)))
        (release q p) p packet (expectedClass (L / q) p)
      · unfold release RawPack.offset
        omega
      · intro s hs
        exact raw_before_release q hq w L p s hL hle hs
      · exact raw_at_release q hq w L p hL hle
      · exact classification_at_release q hq w L hL hle hdiv p
    _ = if p < L / q then
          some
            ⟨SpeedupKx.compress q
                (word_to_config (w.take L)) (p : ℤ),
              ⟨decide (p = 0), decide (p + 1 = L / q)⟩⟩
        else none := by
      by_cases hp : p < L / q
      · rw [if_pos hp]
        simp only [expectedClass, hp, if_true, initializationFor, packet]
        congr 2
        calc
          stripPacket
              (SpeedupKx.compress q
                (word_to_config
                  (ReversalPackets.markedWord w (L - 1))) (p : ℤ)) =
              SpeedupKx.compress q (word_to_config w) (p : ℤ) :=
            stripPacket_compress q w (L - 1) p
          _ = SpeedupKx.compress q
                (word_to_config (w.take L)) (p : ℤ) :=
            compress_take_eq q L (L / q) p w
              (exact_blocks q L hdiv) hle hp
      · rw [if_neg hp]
        simp [expectedClass, hp, initializationFor]

/-- Exact one-shot producer contract. No cell outside `p < L/q` emits an
initialization, at any time. -/
theorem initialization_spec
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (t p : ℕ) :
    ((C q hq α).comp
        (ReversalPackets.markedWord w (L - 1)) t (p : ℤ)).initialization =
      if t = release q p ∧ p < L / q then
        some
          ⟨SpeedupKx.compress q
              (word_to_config (w.take L)) (p : ℤ),
            ⟨decide (p = 0), decide (p + 1 = L / q)⟩⟩
      else
        none := by
  change
    ((C q hq α).nextt
        (ReversalPackets.markedWord w (L - 1)) t (p : ℤ)).fresh = _
  rcases lt_trichotomy t (release q p) with hbefore | hat | hafter
  · rw [if_neg (by omega)]
    apply fresh_none_of_raw_none
    intro s hs
    exact raw_before_release q hq w L p s hL hle (by omega)
  · subst t
    rw [fresh_at_release_spec q hq w L hL hle hdiv]
    by_cases hp : p < L / q <;> simp [hp]
  · rw [if_neg (by omega)]
    apply fresh_none_after_classification q hq
      (word_to_config
        (ReversalPackets.markedWord w (L - 1)))
      (release q p) t (p : ℤ) (expectedClass (L / q) p)
    · exact classification_at_release q hq w L hL hle hdiv p
    · exact hafter

/-- Boundary flags become permanent at the same raw baseline. -/
theorem boundary_spec
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (p t : ℕ) (ht : release q p ≤ t) :
    ((C q hq α).comp
        (ReversalPackets.markedWord w (L - 1)) t (p : ℤ)).boundary =
      if p < L / q then
        some ⟨decide (p = 0), decide (p + 1 = L / q)⟩
      else
        none := by
  change
    (match
      ((C q hq α).nextt
        (ReversalPackets.markedWord w (L - 1))
        t (p : ℤ)).classification with
    | some (.inside boundary) => some boundary
    | _ => none) = _
  rw [classification_spec q hq w L hL hle hdiv p t ht]
  by_cases hp : p < L / q <;> simp [expectedClass, hp]

/-- Every later block is explicitly and permanently certified padding from
its own raw packet baseline onward. -/
theorem paddingReady_spec
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (p t : ℕ) (ht : release q p ≤ t) :
    ((C q hq α).comp
        (ReversalPackets.markedWord w (L - 1)) t (p : ℤ)).paddingReady =
      decide (L / q ≤ p) := by
  change
    decide
      (((C q hq α).nextt
        (ReversalPackets.markedWord w (L - 1))
        t (p : ℤ)).classification = some .padding) =
      decide (L / q ≤ p)
  rw [classification_spec q hq w L hL hle hdiv p t ht]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Option.some.injEq]
  unfold expectedClass
  split_ifs <;> simp_all

/-- Combined release-time API: interior cells emit their exact finite-prefix
packet and expose permanent boundary flags; exterior cells expose the
padding-ready certificate at that same raw baseline. -/
theorem comp_at_release
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (p : ℕ) :
    (C q hq α).comp
        (ReversalPackets.markedWord w (L - 1))
        (release q p) (p : ℤ) =
      if p < L / q then
        ⟨some
            ⟨SpeedupKx.compress q
                (word_to_config (w.take L)) (p : ℤ),
              ⟨decide (p = 0), decide (p + 1 = L / q)⟩⟩,
          some ⟨decide (p = 0), decide (p + 1 = L / q)⟩,
          false⟩
      else
        ⟨none, none, true⟩ := by
  by_cases hp : p < L / q
  · rw [if_pos hp]
    apply Output.ext
    · simpa [hp] using
        initialization_spec q hq w L hL hle hdiv (release q p) p
    · simpa [hp] using
        boundary_spec q hq w L hL hle hdiv p (release q p) le_rfl
    · have hnot : ¬L / q ≤ p := by omega
      simpa [hnot] using
        paddingReady_spec q hq w L hL hle hdiv p (release q p) le_rfl
  · rw [if_neg hp]
    apply Output.ext
    · simpa [hp] using
        initialization_spec q hq w L hL hle hdiv (release q p) p
    · simpa [hp] using
        boundary_spec q hq w L hL hle hdiv p (release q p) le_rfl
    · have hleblock : L / q ≤ p := by omega
      simpa [hleblock] using
        paddingReady_spec q hq w L hL hle hdiv p (release q p) le_rfl

/-- Boolean view of the permanent prefix classification. -/
def isInside : BlockClass → Bool
  | .inside _ => true
  | .padding => false

@[simp]
theorem isInside_expected (M p : ℕ) :
    isInside (expectedClass M p) = decide (p < M) := by
  unfold expectedClass
  split_ifs <;> simp_all [isInside]

/-- One-shot raw packet stream decorated with its online prefix
classification. Unlike `Output.initialization`, this projection emits at
every natural position, so suffix packets remain available to a downstream
padding merge. -/
def classifiedRaw (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] :
    CellAutomaton (Option (α × Bool))
      (Option (Bool × (Fin q → Option α))) where
  Q := (C q hq α).Q
  δ := (C q hq α).δ
  embed := (C q hq α).embed
  project := fun state =>
    match
        (rawCA q hq α).project state.raw,
        state.classification with
    | some packet, some cls =>
        some (isInside cls, stripPacket packet)
    | _, _ => none

@[simp]
private theorem classifiedRaw_nextt
    (q : ℕ) (hq : 2 ≤ q) (c : Config (Option (α × Bool)))
    (t : ℕ) :
    (classifiedRaw q hq α).nextt ⦋c⦌ t =
      (C q hq α).nextt ⦋c⦌ t :=
  rfl

/-- Complete one-shot contract for the classified raw stream. The Boolean is
true exactly on the finite prefix, while the raw packet is preserved at all
natural positions, including the suffix. -/
theorem classifiedRaw_spec
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (t p : ℕ) :
    (classifiedRaw q hq α).comp
        (ReversalPackets.markedWord w (L - 1)) t (p : ℤ) =
      if t = release q p then
        some
          (decide (p < L / q),
            SpeedupKx.compress q (word_to_config w) (p : ℤ))
      else
        none := by
  rw [CellAutomaton.comp_apply, classifiedRaw_nextt]
  simp only [classifiedRaw]
  rw [raw_state q hq
    (word_to_config (ReversalPackets.markedWord w (L - 1))) t p]
  rw [← CellAutomaton.comp_apply]
  rw [RawPack.comp_spec q hq _
    (marked_ne_nil w L hL hle)]
  simp only [Int.natCast_nonneg, Int.natAbs_natCast, true_and]
  by_cases ht : t = release q p
  · subst t
    rw [if_pos (by simp [release]), if_pos rfl]
    rw [classification_at_release q hq w L hL hle hdiv p]
    simp only [isInside_expected]
    rw [stripPacket_compress q w (L - 1) p]
  · rw [if_neg (by simpa [release] using ht), if_neg ht]

@[simp]
theorem classifiedRaw_at_release
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (p : ℕ) :
    (classifiedRaw q hq α).comp
        (ReversalPackets.markedWord w (L - 1))
        (release q p) (p : ℤ) =
      some
        (decide (p < L / q),
          SpeedupKx.compress q (word_to_config w) (p : ℤ)) := by
  rw [classifiedRaw_spec q hq w L hL hle hdiv]
  simp

/-- Projection consumed directly by the finite-strip driver. Before
classification its boundary bits are harmlessly false; after release they
remain exact. -/
def finiteController (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] :
    CellAutomaton (Option (α × Bool))
      ((Bool × Bool) × Option (Fin q → Option α)) :=
  (C q hq α).map_project fun output =>
    (output.boundary.map
        (fun boundary => (boundary.atLeft, boundary.atRight))
        |>.getD (false, false),
      output.initialization.map Initialization.packet)

/-- The finite-strip input packet occurs exactly at the common raw release
time, and only for cells inside the selected prefix. -/
theorem finiteController_packets
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (t p : ℕ) (hp : p < L / q) :
    ((finiteController q hq α).comp
        (ReversalPackets.markedWord w (L - 1)) t (p : ℤ)).2 =
      if t = release q p then
        some
          (SpeedupKx.compress q
            (word_to_config (w.take L)) (p : ℤ))
      else
        none := by
  simp only [finiteController, comp_of_map_project]
  rw [initialization_spec q hq w L hL hle hdiv t p]
  by_cases ht : t = release q p <;> simp [ht, hp]

/-- Both finite-strip boundary bits are exact and permanent immediately
after the packet release. -/
theorem finiteController_boundaries
    (q : ℕ) (hq : 2 ≤ q) (w : Word α) (L : ℕ)
    (hL : 0 < L) (hle : L ≤ w.length) (hdiv : q ∣ L)
    (t p : ℕ) (hp : p < L / q) (ht : release q p < t) :
    ((finiteController q hq α).comp
        (ReversalPackets.markedWord w (L - 1)) t (p : ℤ)).1 =
      (decide (p = 0), decide (p + 1 = L / q)) := by
  simp only [finiteController, comp_of_map_project]
  rw [boundary_spec q hq w L hL hle hdiv p t (by omega)]
  simp [hp]

/-- Concrete implementation of the abstract LT prefix-controller contract.
Both projections use the same startup offset `q` and the same release
diagonal. -/
def prefixController (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] :
    PrefixController q α where
  offset := RawPack.offset q
  offset_pos := by
    simp [RawPack.offset]
    omega
  classified := classifiedRaw q hq α
  initializer := finiteController q hq α
  classified_spec := by
    intro w M hM hle t p
    have hL : 0 < q * M := Nat.mul_pos (by omega) hM
    have hdiv : q ∣ q * M := dvd_mul_right q M
    have hquot : q * M / q = M := by
      rw [Nat.mul_comm, Nat.mul_div_left _ (by omega : 0 < q)]
    simpa [release, hquot] using
      classifiedRaw_spec q hq w (q * M) hL hle hdiv t p
  packets_spec := by
    intro w M hM hle t p
    have hL : 0 < q * M := Nat.mul_pos (by omega) hM
    have hdiv : q ∣ q * M := dvd_mul_right q M
    have hquot : q * M / q = M := by
      rw [Nat.mul_comm, Nat.mul_div_left _ (by omega : 0 < q)]
    simp only [finiteController, comp_of_map_project]
    rw [initialization_spec q hq w (q * M) hL hle hdiv t p]
    simp [release, hquot, and_comm]
  boundaries_spec := by
    intro w M hM hle t p hp ht
    have hL : 0 < q * M := Nat.mul_pos (by omega) hM
    have hdiv : q ∣ q * M := dvd_mul_right q M
    have hquot : q * M / q = M := by
      rw [Nat.mul_comm, Nat.mul_div_left _ (by omega : 0 < q)]
    have hboundary := finiteController_boundaries q hq w (q * M)
      hL hle hdiv t p (by simpa [hquot] using hp)
        (by simpa [release] using ht)
    simpa [hquot] using hboundary

end CellularAutomatas.MarkedPrefix.LT.PrefixPackets
