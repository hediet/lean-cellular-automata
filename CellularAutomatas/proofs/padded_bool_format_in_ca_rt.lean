/-
  # PaddedBoolFormat ∈ ℒ(CA_rt Bool)

  Proves that `PaddedBoolFormat = { true^i false^j | j ≥ i }` is in ℒ(CA_rt Bool).

  ## Strategy
  Build a CA directly for PaddedBoolFormat by combining:
  1. The monotone DFA (checks `true^* false^*` pattern) — 3 states
  2. A midpoint-checking CA using two meeting signals — checks `i ≤ ⌊n/2⌋`

  ### Midpoint CA
  For a word of length n, two signals:
  - **Right signal** from position 0, speed 1, carries "boundary crossed" flag
  - **Left signal** from the right border (position n-1), speed 1
  They meet around position ⌊(n-1)/2⌋. The meeting cell checks if its input is false.
  The result propagates back to cell 0, arriving by time n.

  Since the result arrives at time n (not n-1), we use the 1-step speedup theorem
  (SpBD) to get acceptance at time n-1 for real-time.
-/

import CellularAutomatas.proofs.monotone_format_in_ca_rt
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.speedup_k_step
import CellularAutomatas.proofs.constructions.cart_fix_empty_word
import CellularAutomatas.proofs.constructions.extract_mid_input

namespace CellularAutomatas

open CellAutomaton

/-! ## Definitions -/

/-- Padded bool format: true^i ++ false^j where j ≥ i. -/
def PaddedBoolFormat : Language Bool :=
  { u | ∃ i j : ℕ, j ≥ i ∧ u = List.replicate i true ++ List.replicate j false }

/-- MonotoneBool: the true^* false^* language. -/
def MonotoneBool : Language Bool :=
  { u | ∃ i j : ℕ, u = List.replicate i true ++ List.replicate j false }

/-! ## PaddedBoolFormat = MonotoneBool ∩ MidpointFalse

We decompose PaddedBoolFormat into:
- MonotoneBool: the word has form true^i false^j
- MidpointFalse: the element at position ⌊(n-1)/2⌋ is false (or n = 0)

For monotone words true^i false^j with n = i + j:
  MidpointFalse ↔ i ≤ ⌊(n-1)/2⌋ ↔ 2i ≤ n - 1 ↔ 2i < n + 1 ↔ 2i ≤ n ↔ i ≤ j
Wait, need to be careful:
  i ≤ ⌊(n-1)/2⌋ ↔ i ≤ (i+j-1)/2 ↔ 2i ≤ i+j-1 ↔ i ≤ j-1 ↔ i < j
That only gives j > i, not j ≥ i!

For j = i (n = 2i): ⌊(2i-1)/2⌋ = i-1. Position i-1 has value true (since first false is
at position i). So MidpointFalse is FALSE, but we want to ACCEPT (j = i ≥ i).

So checking position ⌊(n-1)/2⌋ is too restrictive for even-length words.

**Fix**: Check position ⌊n/2⌋ instead.
For n = 2i: ⌊2i/2⌋ = i. Position i is the first false. So check passes. ✓
For i=3, j=2, n=5: ⌊5/2⌋ = 2. Position 2 is true (i=3). Check fails. j < i, correct. ✓
For i=2, j=3, n=5: ⌊5/2⌋ = 2. Position 2 is false (i=2). Check passes. j ≥ i, correct. ✓
For i=2, j=2, n=4: ⌊4/2⌋ = 2. Position 2 is false (i=2). Check passes. j = i, correct. ✓
For i=3, j=2, n=5: ⌊5/2⌋ = 2. Position 2 is true (i=3 > 2). Check fails. j < i, correct. ✓
For i=3, j=3, n=6: ⌊6/2⌋ = 3. Position 3 is false (i=3). Check passes. j = i, correct. ✓

So MidpointFalse should check position ⌊n/2⌋.
But the CA reads at time n-1, not time n/2. We need a signal construction.

**Alternative**: Use a half-speed signal.
A signal starting at position 0 that moves right at speed 1/2 reaches position ⌊t/2⌋ at time t.
At time n-1, it's at position ⌊(n-1)/2⌋, which for even n = 2i gives i-1 (one too few),
and for odd n = 2i+1 gives i.

Hmm, this is still off. Let me use a different approach.

**Cleanest decomposition**: Instead of a midpoint check, use a direct characterization.
-/

/-- PaddedBoolFormat characterized via length and boundary. -/
lemma paddedBoolFormat_iff (w : Word Bool) :
    w ∈ PaddedBoolFormat ↔ ∃ i j, j ≥ i ∧ w = List.replicate i true ++ List.replicate j false := by
  rfl

/-! ## Helper lemmas -/

private lemma count_replicate_self (a : Bool) (n : ℕ) :
    (List.replicate n a).count a = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.count_cons, ih]

private lemma count_replicate_ne (a b : Bool) (n : ℕ) (h : a ≠ b) :
    (List.replicate n a).count b = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.count_cons, ih]
    simp [show (a == b) = false from by cases a <;> cases b <;> simp_all]

lemma monotoneBool_eq_dfa : MonotoneBool = monotoneDFA.accepts := by
  ext u; simp only [MonotoneBool, monotoneDFA_accepts_iff]; rfl

theorem monotoneBool_in_ca_rt : MonotoneBool ∈ ℒ (CA_rt Bool) := by
  rw [monotoneBool_eq_dfa]; exact truestar_falsestar_in_ca_rt

/-! ## MidpointFalse: w[⌊n/2⌋] = false -/

/-- The midpoint-false condition for PaddedBoolFormat.
    For a nonempty word, the element at position ⌊n/2⌋ is false. -/
def MidpointFalse : Language Bool :=
  { w | ∀ (h : w.length > 0), w[w.length / 2]'(by omega) = false }

instance : DecidablePred (· ∈ MidpointFalse) := fun w =>
  if hlen : w.length > 0 then
    if heq : w[w.length / 2]'(by omega) = false then
      isTrue (fun _ => heq)
    else
      isFalse (fun hw => heq (hw hlen))
  else
    isTrue (fun hp => by omega)

/-- For monotone true^i false^j, MidpointFalse ↔ j ≥ i -/
private lemma midpointFalse_monotone_iff (i j : ℕ) :
    (List.replicate i true ++ List.replicate j false) ∈ MidpointFalse ↔ j ≥ i := by
  simp only [MidpointFalse, Set.mem_setOf_eq, List.length_append, List.length_replicate]
  constructor
  · intro h
    by_cases hij : i + j = 0
    · omega
    · have h_pos : (List.replicate i true ++ List.replicate j false).length > 0 := by simp; omega
      specialize h h_pos
      by_contra h_lt
      push_neg at h_lt
      have h_pos_lt_i : (i + j) / 2 < i := Nat.div_lt_iff_lt_mul (by omega) |>.mpr (by omega)
      rw [List.getElem_append_left (by simp; exact h_pos_lt_i)] at h
      simp [List.getElem_replicate] at h
  · intro h _
    have h_pos_ge_i : (i + j) / 2 ≥ i := Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)
    rw [List.getElem_append_right (by simp; omega)]
    simp [List.getElem_replicate]

/-- PaddedBoolFormat = MonotoneBool ∩ MidpointFalse -/
lemma paddedBoolFormat_eq_inter :
    PaddedBoolFormat = (MonotoneBool ∩ MidpointFalse : Set (Word Bool)) := by
  ext w
  simp only [PaddedBoolFormat, MonotoneBool, MidpointFalse,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro ⟨i, j, hj, hw⟩
    refine ⟨⟨i, j, hw⟩, ?_⟩
    rw [hw]
    exact (midpointFalse_monotone_iff i j).mpr hj
  · intro ⟨⟨i, j, hw⟩, hmid⟩
    refine ⟨i, j, ?_, hw⟩
    rw [hw] at hmid
    exact (midpointFalse_monotone_iff i j).mp hmid

/-! ## MidpointFalse ∈ ℒ(CA_rt Bool)

We check w[⌊n/2⌋] = false using `extractMidCA`, which extracts the middle cell(s) of the
input at time n-1. We compose it with a projection that checks whether the middle value
is false.

For `extractMidCA_spec` (requires n ≥ 2):
- Even n: output = `.pair w[n/2-1] w[n/2]`
- Odd n:  output = `.single w[n/2]`

In both cases, the "rightmost" value is `w[n/2]`, which is exactly what MidpointFalse checks.
-/

/-- Extract the value to check from BetaUnionSq: always the rightmost. -/
private def betaUnionSqRight : BetaUnionSq Bool → Bool
  | .single b => b
  | .pair _ b => b

/-- The midpoint-false CA: extracts the middle value and checks if it's false. -/
def midpointFalseCA : CellAutomaton Bool？ Bool :=
  (extractMidCA Bool).map_project (fun x => decide (betaUnionSqRight x = false))

/-- For length-1 words, the rightmost extracted value is w[0]. -/
private lemma betaUnionSqRight_extractMid_len1 (w : Word Bool) (hw : w.length = 1) :
    betaUnionSqRight ((extractMidCA Bool).comp (↑w) 0 0) = w[0]'(by omega) := by
  rw [extractMidCA_spec_len1 w hw]
  simp [betaUnionSqRight]

/-- At time n-1, cell 0 outputs `!w[n/2]` for words of length ≥ 2. -/
private lemma betaUnionSqRight_extractMid (w : Word Bool) (hw : w.length ≥ 2) :
    betaUnionSqRight ((extractMidCA Bool).comp (↑w) (w.length - 1) 0) = w[w.length / 2]'(by omega) := by
  have h := extractMidCA_spec w hw
  unfold betaUnionSqRight
  rw [h]
  by_cases hp : w.length % 2 = 0 <;> simp [hp]

private lemma midpointFalseCA_spec' (w : Word Bool) (hw : w.length ≥ 2) :
    midpointFalseCA.comp w (w.length - 1) 0 = true ↔ w[w.length / 2]'(by omega) = false := by
  unfold midpointFalseCA
  simp only [map_project_comp, decide_eq_true_iff]
  have key := betaUnionSqRight_extractMid w hw
  exact key ▸ Iff.rfl

/-- MidpointFalse ∈ ℒ(CA_rt Bool). -/
theorem midpointFalse_in_ca_rt : MidpointFalse ∈ ℒ (CA_rt Bool) := by
  rw [ℒ_CA_rt_iff]
  let C_rt := fix_empty true (toRtCa midpointFalseCA)
  use C_rt.val
  refine ⟨C_rt.property, ?_⟩
  ext w
  rw [fix_empty_spec]
  by_cases hw : w = []
  · -- Empty word: vacuously in MidpointFalse
    simp only [hw, beq_self_eq_true, ↓reduceIte]
    exact ⟨fun _ h => by simp at h, fun _ => trivial⟩
  · simp only [beq_iff_eq, hw, ↓reduceIte, decide_eq_true_iff]
    have hw_pos : w.length ≥ 1 := by cases w with | nil => contradiction | cons _ _ => simp
    by_cases hw1 : w.length = 1
    · -- Length 1: w[n/2] = w[0], time n-1 = 0
      have hdiv : w.length / 2 = 0 := by omega
      -- key: betaUnionSqRight at time 0 gives w[0]
      have key : betaUnionSqRight ((extractMidCA Bool).comp (↑w) 0 0) = w[0]'(by omega) :=
        betaUnionSqRight_extractMid_len1 w hw1
      simp only [MidpointFalse, Set.mem_setOf_eq, hdiv]
      -- The CA_rt_L_iff gives us comp (n-1) 0 = true. Since n-1 = 0, this is comp 0 0.
      -- The comp goes through toRtCa which preserves the CA, just wrapping it.
      -- toRtCa.comp = midpointFalseCA.comp = decide(betaUnionSqRight(extractMidCA.comp w 0 0) = false)
      constructor
      · intro hmem _
        have hmem' := (CA_rt_L_iff (C := toRtCa midpointFalseCA)).mp hmem
        change midpointFalseCA.comp (↑w) (w.length - 1) 0 = true at hmem'
        rw [show w.length - 1 = 0 from by omega] at hmem'
        change decide (betaUnionSqRight ((extractMidCA Bool).comp (↑w) 0 0) = false) = true at hmem'
        rw [decide_eq_true_iff, key] at hmem'
        simpa [hdiv] using hmem'
      · intro hmem
        apply (CA_rt_L_iff (C := toRtCa midpointFalseCA)).mpr
        change midpointFalseCA.comp (↑w) (w.length - 1) 0 = true
        rw [show w.length - 1 = 0 from by omega]
        change decide (betaUnionSqRight ((extractMidCA Bool).comp (↑w) 0 0) = false) = true
        rw [decide_eq_true_iff, key]
        simpa [hdiv] using hmem hw_pos
    · -- Length ≥ 2: use midpointFalseCA_spec'
      have hw_ge2 : w.length ≥ 2 := by omega
      constructor
      · intro hmem
        simp only [MidpointFalse, Set.mem_setOf_eq]
        intro _
        exact (midpointFalseCA_spec' w hw_ge2).mp ((CA_rt_L_iff (C := toRtCa midpointFalseCA)).mp hmem)
      · intro hmem
        exact (CA_rt_L_iff (C := toRtCa midpointFalseCA)).mpr
          ((midpointFalseCA_spec' w hw_ge2).mpr (hmem hw_pos))

/-! ## Main result -/

/-- PaddedBoolFormat is in ℒ(CA_rt Bool). -/
theorem padded_bool_format_in_ca_rt : PaddedBoolFormat ∈ ℒ (CA_rt Bool) := by
  rw [paddedBoolFormat_eq_inter]
  have h₁ := monotoneBool_in_ca_rt
  have h₂ := midpointFalse_in_ca_rt
  rw [ℒ_CA_rt_iff] at h₁ h₂ ⊢
  obtain ⟨C₁, hC₁_rt, hC₁_L⟩ := h₁
  obtain ⟨C₂, hC₂_rt, hC₂_L⟩ := h₂
  let C' := toRtCa ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && b))
  refine ⟨C'.val, C'.property, ?_⟩
  ext w
  rw [Set.mem_inter_iff, ← hC₁_L, ← hC₂_L]
  rw [CA_rt_L_iff (C := C'), CA_rt_L_iff2 hC₁_rt, CA_rt_L_iff2 hC₂_rt]
  show ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && b)).comp
    ⦋w⦌ (w.length - 1) 0 = true ↔
    C₁.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true ∧
    C₂.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true
  simp only [comp_of_map_project, ca_zip_comp, Bool.and_eq_true]

end CellularAutomatas
