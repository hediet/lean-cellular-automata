import CellularAutomatas.proofs.advice_theory.compress_n_is_rt_advice
import CellularAutomatas.proofs.advice_theory.sync_time_constructible
import CellularAutomatas.proofs.constructions.border_quiescent
import CellularAutomatas.proofs.constructions.basic_ca_id
import CellularAutomatas.proofs.constructions.basic_mark_border
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.trace_kx
import CellularAutomatas.proofs.rt_eq_2n_iff_rt_eq_rt_rev.rt_eq_2n_iff_rt_eq_rt_rev

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

namespace LinearTimeSpeedup

/-- Decode an optional compressed block. Outside the compressed word, every
    component represents an out-of-range source cell. -/
def decodeBlock (k : ℕ) : Option (Fin k → Option α) → (Fin k → Option α)
  | none => fun _ => none
  | some block => block

/-- Reading `compress_n k w` as a CA configuration, then decoding its optional
    cells, gives exactly the block configuration expected by `SpeedupKx`. -/
lemma decodeBlock_word_to_config_eq_compress (k : ℕ) [NeZero k]
    (w : Word α) (p : ℤ) :
    decodeBlock k (⟬Advice.compress_n k α w⟭ p) =
      SpeedupKx.compress k ⟬w⟭ p := by
  funext j
  by_cases hp : 0 ≤ p ∧ p < (w.length : ℤ)
  · have hp_nat : p.toNat < w.length := by omega
    have hp_cast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp.1
    have hp_compressed :
        0 ≤ p ∧ p < ((Advice.compress_n k α w).length : ℤ) := by
      simpa [Advice.compress_n] using hp
    have h_block :
        ⟬Advice.compress_n k α w⟭ p =
          some (fun j : Fin k => w[k * p.toNat + j.val]?) := by
      rw [word_to_config_apply, dif_pos hp_compressed]
      simp [Advice.compress_n]
    rw [h_block]
    simp only [decodeBlock, SpeedupKx.compress]
    have h_mul : p * (k : ℤ) = (p.toNat : ℤ) * (k : ℤ) :=
      congrArg (fun q : ℤ => q * (k : ℤ)) hp_cast.symm
    have h_index :
        p * (k : ℤ) + (j.val : ℤ) =
          ((k * p.toNat + j.val : ℕ) : ℤ) := by
      rw [h_mul]
      push_cast
      ring
    rw [h_index, word_to_config_apply]
    simp only [Int.toNat_natCast]
    by_cases h_source : k * p.toNat + j.val < w.length
    · rw [dif_pos]
      · exact List.getElem?_eq_getElem h_source
      · constructor
        · exact_mod_cast Nat.zero_le (k * p.toNat + j.val)
        · exact_mod_cast h_source
    · rw [dif_neg]
      · exact List.getElem?_eq_none (Nat.le_of_not_gt h_source)
      · intro h
        exact h_source (by exact_mod_cast h.2)
  · have hp_compressed :
        ¬ (0 ≤ p ∧ p < ((Advice.compress_n k α w).length : ℤ)) := by
      simpa [Advice.compress_n] using hp
    simp only [SpeedupKx.compress]
    rw [word_to_config_apply, dif_neg hp_compressed]
    simp only [decodeBlock]
    rw [word_to_config_apply, dif_neg]
    intro h_source
    have hk_pos : (0 : ℤ) < k := by
      exact_mod_cast NeZero.pos k
    have hj_nonneg : 0 ≤ (j.val : ℤ) := by omega
    have hj_lt : (j.val : ℤ) < k := by exact_mod_cast j.isLt
    rcases lt_or_ge p 0 with hp_neg | hp_nonneg
    · have hp_le : p ≤ -1 := by omega
      have h_mul : p * (k : ℤ) ≤ (-1 : ℤ) * k :=
        mul_le_mul_of_nonneg_right hp_le (le_of_lt hk_pos)
      omega
    · have hp_ge : (w.length : ℤ) ≤ p := by
        by_contra h
        exact hp ⟨hp_nonneg, lt_of_not_ge h⟩
      have hk_one : (1 : ℤ) ≤ k := by omega
      have h_mul : p * 1 ≤ p * (k : ℤ) :=
        mul_le_mul_of_nonneg_left hk_one hp_nonneg
      omega

/-! ## Accelerated runtime -/

/-- The trace-preserving `k`-fold speedup of the original recognizer. -/
def speedup (C : LCellAutomaton α) (k : ℕ) [NeZero k] : SpeedupAndTraceKx where
  k := k
  α := Option α
  β := Bool
  C_orig := C

/-- The accelerated CA after decoding optional cells of `compress_n k w`. -/
def decodedSpeedup (C : LCellAutomaton α) (k : ℕ) [NeZero k] :
    CellAutomaton (Option (Fin k → Option α)) (Fin k → Bool) :=
  (speedup C k).C.map_embed (decodeBlock k)

/-- Add a quiescent border so the accelerated CA can be launched as a second
    stage by `FireThenRun`. -/
def borderedSpeedup (C : LCellAutomaton α) (k : ℕ) [NeZero k] :
    QuiescentBorder where
  C_orig := decodedSpeedup C k

def runtime (C : LCellAutomaton α) (k : ℕ) [NeZero k] :
    CellAutomaton (Option (Fin k → Option α)) (Fin k → Bool) :=
  (borderedSpeedup C k).C

private lemma decodedSpeedup_spec (C : LCellAutomaton α) (k : ℕ) [NeZero k]
    (w : Word α) (hw : 0 < w.length) :
    (decodedSpeedup C k).comp ⦋⟬Advice.compress_n k α w⟭⦌ w.length 0 0 =
      C.comp ⦋⟬w⟭⦌ (k * (w.length - 1)) 0 := by
  have h_embedded :
      (CellAutomaton.embed_config (C := (speedup C k).C.map_embed (decodeBlock k))
          ⟬Advice.compress_n k α w⟭ : Config _) =
        CellAutomaton.embed_config (C := (speedup C k).C)
          (SpeedupKx.compress k ⟬w⟭) := by
    funext p
    show (speedup C k).C.embed (decodeBlock k _) = (speedup C k).C.embed _
    rw [decodeBlock_word_to_config_eq_compress]
  show ((speedup C k).C.map_embed (decodeBlock k)).comp
      ⟬Advice.compress_n k α w⟭ w.length 0 0 = _
  rw [show ((speedup C k).C.map_embed (decodeBlock k)).comp
      ⟬Advice.compress_n k α w⟭ w.length 0 0 =
        (speedup C k).C.comp
          (CellAutomaton.embed_config
            (C := (speedup C k).C.map_embed (decodeBlock k))
            ⟬Advice.compress_n k α w⟭) w.length 0 0 from rfl]
  rw [h_embedded]
  have h_time : w.length - 1 + 1 = w.length := by omega
  have h_spec := (speedup C k).spec1
    (c := ⟬w⟭) (t1 := w.length - 1) (t2 := (0 : Fin k))
  rw [h_time] at h_spec
  simpa [speedup, CellAutomaton.trace] using h_spec

/-- On the compressed word, `n` accelerated ticks recover the original
    recognizer's answer at time `k * (n - 1)`. -/
lemma runtime_spec (C : LCellAutomaton α) (k : ℕ) [NeZero k]
    (w : Word α) (hw : 0 < w.length) :
    (runtime C k).comp ⦋⟬Advice.compress_n k α w⟭⦌ w.length 0 0 =
      C.comp ⦋⟬w⟭⦌ (k * (w.length - 1)) 0 := by
  have h_compressed_pos : 0 < (Advice.compress_n k α w).length := by
    simpa using hw
  have h_cone :
      (0 : ℤ) ∈ WordCone (Advice.compress_n k α w) w.length := by
    rw [WordCone_mem]
    simpa using hw
  change (borderedSpeedup C k).C.comp
      ⦋⟬Advice.compress_n k α w⟭⦌ w.length 0 0 = _
  rw [(borderedSpeedup C k).spec
    (Advice.compress_n k α w) h_compressed_pos w.length 0]
  rw [if_pos h_cone]
  exact decodedSpeedup_spec C k w hw

/-! ## Sequential composition -/

/-- First compute `compress_n k`, then run the `k`-fold accelerated
    recognizer. The synchronous timer is encapsulated by `FireThenRunInput`. -/
def chain (C : LCellAutomaton α) (k : ℕ) (hk : 2 ≤ k) :
    FireThenRunInput α (Fin k → Option α) (Fin k → Bool) := by
  letI : NeZero k := ⟨by omega⟩
  exact
    { a := Advice.compress_n_is_n_time_advice k hk
      sc := IdSync.toInner
      runtime := runtime C k
      h_quiescent := (borderedSpeedup C k).C_border_quiescent }

/-- The complete two-stage construction spends `n` ticks on compression and
    `n` ticks on accelerated simulation. -/
lemma chain_spec (C : LCellAutomaton α) (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (w : Word α) (hw : 0 < w.length) :
    (chain C k hk).C.comp ⦋⟬w⟭⦌ (2 * w.length) 0 0 =
      C.comp ⦋⟬w⟭⦌ (k * (w.length - 1)) 0 := by
  calc
    (chain C k hk).C.comp ⦋⟬w⟭⦌ (2 * w.length) 0 0
        = (runtime C k).comp
            ⦋⟬Advice.compress_n k α w⟭⦌ w.length 0 0 := by
          have h_post := (chain C k hk).spec_post w w.length 0
          have h_time : (chain C k hk).t1 w.length + w.length =
              2 * w.length := by
            change w.length + w.length = 2 * w.length
            omega
          rw [h_time] at h_post
          exact congrFun h_post 0
    _ = C.comp ⦋⟬w⟭⦌ (k * (w.length - 1)) 0 :=
      runtime_spec C k w hw

/-! ## Proper-time recognizer -/

/-- Package the two-stage construction as a recognizer at time `2n`. The
    border detector preserves the original recognizer's empty-word answer. -/
def properSpeedup (C : LCellAutomaton α) (k : ℕ) (hk : 2 ≤ k) :
    CA_2n_proper α := by
  letI : NeZero k := ⟨by omega⟩
  let accelerated : LCellAutomaton α := (chain C k hk).C.map_project (· 0)
  let containsEmpty : Bool := C.comp ⦋⟬([] : Word α)⟭⦌ 0 0
  exact
    { toCellAutomaton :=
        (accelerated ⨂ c_is_border α).map_project
          (fun (answer, isEmpty) => if isEmpty then containsEmpty else answer) }

/-- The proper-time recognizer agrees with the original `k(n-1)`-time
    recognizer on every word. -/
lemma properSpeedup_spec (C : LCellAutomaton α) (k : ℕ) (hk : 2 ≤ k)
    (w : Word α) :
    (properSpeedup C k hk).accepts w =
      C.comp ⦋⟬w⟭⦌ (k * (w.length - 1)) 0 := by
  letI : NeZero k := ⟨by omega⟩
  change (properSpeedup C k hk).toCellAutomaton.comp
      ⦋⟬w⟭⦌ (2 * w.length) 0 = _
  unfold properSpeedup
  erw [comp_of_map_project]
  rw [ca_zip_comp, c_is_border_spec]
  by_cases hw : w = []
  · subst w
    rfl
  · have hw_pos : 0 < w.length := by
      cases w with
      | nil => exact absurd rfl hw
      | cons _ _ => simp
    have h_not_empty : (w == []) = false := by simp [hw]
    rw [h_not_empty]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact chain_spec C k hk w hw_pos

lemma properSpeedup_L (C : tCellAutomaton (.lt_center k) α) (hk : 2 ≤ k) :
    (properSpeedup C.toCellAutomaton k hk).L = C.L := by
  ext w
  show (properSpeedup C.toCellAutomaton k hk).accepts w = true ↔
    C.accepts w = true
  rw [properSpeedup_spec]
  rfl

/-! ## Small coefficients -/

/-- A CA that preserves the original embedded state forever. -/
def holdInitial (C : LCellAutomaton α) : LCellAutomaton α :=
  ((CellAutomaton.idCA C.Q).map_embed C.embed).map_project C.project

omit [Alphabet α] in
lemma holdInitial_spec (C : LCellAutomaton α) (w : Word α) (t : ℕ) :
    (holdInitial C).comp ⦋⟬w⟭⦌ t 0 = C.comp ⦋⟬w⟭⦌ 0 0 := by
  change C.project ((CellAutomaton.idCA C.Q).comp
      (CellAutomaton.embed_config
        (C := (CellAutomaton.idCA C.Q).map_embed C.embed) ⟬w⟭) t 0) = _
  rw [CellAutomaton.idCA.comp_spec]
  rfl

def zeroTimeToProper (C : tCellAutomaton (.lt_center 0) α) :
    CA_2n_proper α where
  toCellAutomaton := holdInitial C.toCellAutomaton

lemma zeroTimeToProper_L (C : tCellAutomaton (.lt_center 0) α) :
    (zeroTimeToProper C).L = C.L := by
  ext w
  show (zeroTimeToProper C).accepts w = true ↔ C.accepts w = true
  change (holdInitial C.toCellAutomaton).comp ⦋⟬w⟭⦌ (2 * w.length) 0 = true ↔
    C.toCellAutomaton.comp ⦋⟬w⟭⦌ (0 * (w.length - 1)) 0 = true
  rw [holdInitial_spec]
  simp

def oneTimeToRt (C : tCellAutomaton (.lt_center 1) α) : CA_rt α where
  toCellAutomaton := C.toCellAutomaton

omit [Alphabet α] in
lemma oneTimeToRt_L (C : tCellAutomaton (.lt_center 1) α) :
    (oneTimeToRt C).L = C.L := by
  ext w
  show (oneTimeToRt C).accepts w = true ↔ C.accepts w = true
  change C.toCellAutomaton.comp ⦋⟬w⟭⦌ (w.length - 1) 0 = true ↔
    C.toCellAutomaton.comp ⦋⟬w⟭⦌ (1 * (w.length - 1)) 0 = true
  simp

end LinearTimeSpeedup

/-! ## Language-class equality -/

/-- Every `2(n-1)`-time recognizer is already a linear-time recognizer with
    coefficient `2`. -/
lemma ca_2n_subset_ca_lt : ℒ (CA_2n α) ⊆ ℒ (CA_lt α) := by
  intro L ⟨C, hL⟩
  let C' : tCellAutomaton (.lt_center 2) α :=
    { toCellAutomaton := C.toCellAutomaton }
  refine ⟨⟨2, C'⟩, ?_⟩
  calc
    L = C.L := hL
    _ = C'.L := by rfl

/-- Every linear-time recognizer can be compressed and accelerated to a
    `2(n-1)`-time recognizer. -/
lemma ca_lt_subset_ca_2n : ℒ (CA_lt α) ⊆ ℒ (CA_2n α) := by
  intro L ⟨⟨k, C⟩, hL⟩
  rcases eq_or_ne k 0 with hk_zero | hk_nonzero
  · subst k
    apply ca_2n_proper_subset_ca_2n
    refine ⟨LinearTimeSpeedup.zeroTimeToProper C, ?_⟩
    exact hL.trans (LinearTimeSpeedup.zeroTimeToProper_L C).symm
  · rcases eq_or_ne k 1 with hk_one | hk_not_one
    · subst k
      apply ca_rt_subset_ca_2n
      refine ⟨LinearTimeSpeedup.oneTimeToRt C, ?_⟩
      exact hL.trans (LinearTimeSpeedup.oneTimeToRt_L C).symm
    · have hk : 2 ≤ k := by omega
      apply ca_2n_proper_subset_ca_2n
      refine ⟨LinearTimeSpeedup.properSpeedup C.toCellAutomaton k hk, ?_⟩
      exact hL.trans (LinearTimeSpeedup.properSpeedup_L C hk).symm

/-- Linear-time speedup for two-way cellular automata. -/
theorem ca_2n_eq_ca_lt : ℒ (CA_2n α) = ℒ (CA_lt α) :=
  Set.Subset.antisymm ca_2n_subset_ca_lt ca_lt_subset_ca_2n

end CellularAutomatas
