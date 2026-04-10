import CellularAutomatas.defs
import CellularAutomatas.internal_defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.rt_eq_2n_iff_rt_eq_rt_rev.broadcast_oca
import CellularAutomatas.proofs.constructions.left_indep_from_regular
import CellularAutomatas.proofs.constructions.left_indep_to_regular
import CellularAutomatas.proofs.constructions.speedup_left_independent_config
import CellularAutomatas.proofs.constructions.basic_fold
import CellularAutomatas.proofs.constructions.basic_border_normalization
import CellularAutomatas.proofs.two_stage_is_rt_closed
import CellularAutomatas.proofs.ca_rt_finite_closure
import CellularAutomatas.proofs.rt_eq_2n_iff_rt_eq_rt_rev.nextpow2
import CellularAutomatas.proofs.rt_eq_2n_iff_rt_eq_rt_rev.x_prefix_advice_two_stage
import CellularAutomatas.proofs.language.lift_language
import Mathlib.Data.Set.Finite.List

/-!
# $L_x(L) \in \mathrm{CA_{RT}} \implies L \in \mathrm{CA_{RT}}$

This file proves that if $L_x(L) := \{ x^m w \mid w \in L, m = 2^{\lceil \log_2 |w| \rceil} \}$
is accepted by a real-time CA, then $L$ itself is accepted by a real-time CA.

## Overview

The proof proceeds by constructing a pipeline of CA transformations:
1. **RegularToLeftIndep**: Convert to left-independent CA (time doubles)
2. **Broadcast**: Extend computation time while preserving result
3. **Shift**: Move observation point via translation invariance
4. **Speedup**: Compress k consecutive cells into tuples
5. **LeftIndepToRegular**: Convert back to regular CA (time halves)
6. **FoldCA**: Fold bi-infinite config to right-infinite
7. **BorderNormalize**: Normalize borders
8. **Advice elimination**: Remove the x^m prefix using two-stage advice

## Main Result

* `lx_rt_implies_rt` - If L_x(L) ∈ CA_RT then L ∈ CA_RT
-/

namespace CellularAutomatas

open CellAutomaton

/-! ## Part I: Definitions -/

/-- Key property: nextPow2 n ≤ 2 * (n - 1) for n ≥ 2. -/
lemma nextPow2_le_two_pred (n : ℕ) (hn : n ≥ 2) : nextPow2 n ≤ 2 * (n - 1) := by
  unfold nextPow2
  have h_gt : ¬(n ≤ 1) := by omega
  simp only [h_gt, ite_false]
  -- Goal: 2^(log2(n-1) + 1) ≤ 2 * (n - 1)
  -- = 2 * 2^(log2(n-1)) ≤ 2 * (n - 1)
  rw [Nat.pow_succ]
  -- Goal: 2^(log2(n-1)) * 2 ≤ 2 * (n - 1)
  have h_pos : n - 1 ≠ 0 := by omega
  have h_le : 2 ^ Nat.log2 (n - 1) ≤ n - 1 := Nat.log2_self_le h_pos
  omega

/-- For n ≥ 8, we have 8 ∣ nextPow2 n. -/
lemma eight_dvd_nextPow2 (n : ℕ) (hn : n ≥ 8) : 8 ∣ nextPow2 n := by
  unfold nextPow2
  have h_gt : ¬(n ≤ 1) := by omega
  simp only [h_gt, ite_false]
  -- Goal: 8 ∣ 2^(log2(n-1) + 1)
  -- For n ≥ 8, n-1 ≥ 7 ≥ 4 = 2^2, so log2(n-1) ≥ 2
  -- Hence log2(n-1) + 1 ≥ 3, and 8 = 2^3 ∣ 2^k for k ≥ 3
  have h_nm1_ge : n - 1 ≥ 4 := by omega
  have h_nm1_pos : n - 1 ≠ 0 := by omega
  have h_log2_ge : Nat.log2 (n - 1) ≥ 2 := by
    rw [ge_iff_le, Nat.le_log2 h_nm1_pos]
    exact h_nm1_ge
  have h_exp_ge : Nat.log2 (n - 1) + 1 ≥ 3 := by omega
  exact Nat.pow_dvd_pow 2 h_exp_ge

/-- nextPow2 n ≥ 1 for all n. -/
lemma nextPow2_pos (n : ℕ) : nextPow2 n ≥ 1 := by
  unfold nextPow2
  split_ifs with h
  · exact le_refl 1
  · exact Nat.one_le_two_pow

/-- nextPow2 n ≥ n for all n ≥ 1. -/
lemma nextPow2_ge (n : ℕ) (_hn : n ≥ 1) : nextPow2 n ≥ n := by
  unfold nextPow2
  split_ifs with h
  · -- Case n ≤ 1: since n ≥ 1, n = 1, and nextPow2 1 = 1 ≥ 1
    omega
  · -- Case n > 1: nextPow2 n = 2^(log2(n-1) + 1)
    -- By Nat.lt_log2_self: n-1 < 2^(log2(n-1) + 1)
    -- So 2^(log2(n-1) + 1) > n-1, hence ≥ n
    have h_lt : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) := Nat.lt_log2_self
    omega

/-- nextPow2 n ≥ n for all n (including n = 0). -/
lemma nextPow2_ge_self (n : ℕ) : n ≤ nextPow2 n := by
  by_cases hn : n ≥ 1
  · exact nextPow2_ge n hn
  · simp only [Nat.not_le, Nat.lt_one_iff] at hn
    simp [hn, nextPow2]

/-- nextPow2 returns either 1 or a power of 2 (≥ 2).
    This is the key structural property for the gap lemma. -/
lemma nextPow2_eq_one_or_pow2 (n : ℕ) :
    nextPow2 n = 1 ∨ ∃ k ≥ 1, nextPow2 n = 2^k := by
  unfold nextPow2
  split_ifs with h
  · left; rfl
  · right
    use Nat.log2 (n - 1) + 1
    constructor
    · omega
    · rfl

/-- Gap lemma for nextPow2: if nextPow2 a < nextPow2 b, then nextPow2 b ≥ 2 * nextPow2 a.
    This holds because nextPow2 returns 1 or powers of 2, and for any two distinct
    values in {1, 2, 4, 8, ...}, the larger is at least twice the smaller. -/
lemma nextPow2_gap (a b : ℕ) (h : nextPow2 a < nextPow2 b) : nextPow2 b ≥ 2 * nextPow2 a := by
  rcases nextPow2_eq_one_or_pow2 a with ha | ⟨j, _, hj⟩
  · -- Case: nextPow2 a = 1
    rw [ha]
    simp only [mul_one]
    -- Need: nextPow2 b ≥ 2, which follows from h : 1 < nextPow2 b
    rw [ha] at h
    rcases nextPow2_eq_one_or_pow2 b with hb | ⟨k, hk_ge, hk⟩
    · rw [hb] at h; omega  -- contradiction: 1 < 1
    · rw [hk]
      calc 2^k = 2^1 * 2^(k-1) := by rw [← Nat.pow_add]; congr; omega
           _ ≥ 2^1 := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow)
           _ = 2 := rfl
  · -- Case: nextPow2 a = 2^j with j ≥ 1
    rw [hj] at h ⊢
    rcases nextPow2_eq_one_or_pow2 b with hb | ⟨k, _, hk⟩
    · rw [hb] at h
      -- h : 2^j < 1, but 2^j ≥ 1, contradiction
      have : 2^j ≥ 1 := Nat.one_le_two_pow
      omega
    · rw [hk] at h ⊢
      -- h : 2^j < 2^k, so k > j, hence k ≥ j+1, so 2^k ≥ 2^(j+1) = 2 * 2^j
      have hkj : k > j := by
        by_contra h_not
        push_neg at h_not  -- k ≤ j
        have : 2^k ≤ 2^j := Nat.pow_le_pow_right (by omega) h_not
        omega
      calc 2^k ≥ 2^(j+1) := Nat.pow_le_pow_right (by omega) (by omega)
           _ = 2 * 2^j := by ring

/-- For n ≥ 2, we have 7*(n-1) ≥ 2*nextPow2(n).
    Uses: nextPow2(n) ≤ 2*(n-1), so 2*nextPow2(n) ≤ 4*(n-1) ≤ 7*(n-1). -/
lemma hr_from_n_ge_2 (n : ℕ) (hn : n ≥ 2) : 7*(n - 1) ≥ 2*(nextPow2 n) := by
  have h := nextPow2_le_two_pred n hn
  omega

-- The compression factor (must be ≥ 2, we use 8 for divisibility reasons)
@[reducible] def k_factor : ℕ := 8

lemma k_factor_ge_2 : k_factor ≥ 2 := by simp [k_factor]

/-- For n ≥ k_factor + 1 = 9, we have nextPow2(n) ≤ k_factor * (n + 1 - k_factor).
    Uses: nextPow2(n) ≤ 2*(n-1) = 2n - 2, and we need 2n - 2 ≤ 8n - 56,
    i.e., 54 ≤ 6n, i.e., n ≥ 9. -/
lemma hm_from_n_ge_9 (n : ℕ) (hn : n ≥ k_factor + 1) :
    (nextPow2 n : ℤ) ≤ k_factor * ((n : ℤ) + 1 - k_factor) := by
  simp only [k_factor] at hn ⊢
  have hn2 : n ≥ 2 := by omega
  have h := nextPow2_le_two_pred n hn2
  -- k_factor = 8, so k_factor + 1 = 9
  -- Need: nextPow2 n ≤ 8 * (n + 1 - 8) = 8 * (n - 7) = 8n - 56
  -- Have: nextPow2 n ≤ 2 * (n - 1) = 2n - 2
  -- Since n ≥ 9: 2n - 2 ≤ 8n - 56 ↔ 54 ≤ 6n ↔ 9 ≤ n ✓
  omega

/-- The L_x transformation: lifts L to Option α and prepends none-padding.
    L_x(L) = { none^k ++ w.map some | w ∈ L, k ≥ |w| }

    The padding length is relaxed: any k ≥ |w| is valid.
    The split is unique since none and some _ are disjoint. -/
def L_x {α : Type} (L : Language α) : Language (Option α) :=
  { u | ∃ (w : Word α) (k : ℕ), w ∈ L ∧ k ≥ w.length ∧
        u = List.replicate k none ++ w.map some }


/-! ## Part II: Shifted Embedding

The shifted embedding [v | w] places w starting at position 0,
and v to the left (v reversed, so v[0] is at position -1, v[1] at -2, etc.).
-/

/-- Shifted embedding: ⟪v||w⟫(p) = ⟬v ++ w⟭(p + |v|) -/
def ShiftedConfig {α : Type} (v w : Word α) : Config α？ :=
  fun p => word_to_config (v ++ w) (p + v.length)

notation:max "⟪" v:100 "||" w:100 "⟫" => ShiftedConfig v w

/-- Shift invariance: C.comp(⟪v||w⟫, t, p) = C.comp(⟬v ++ w⟭, t, p + |v|) -/
lemma comp_shift {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (v w : Word α) (t : ℕ) (p : ℤ) :
    C.comp ⟪v||w⟫ t p = C.comp ⟬v ++ w⟭ t (p + v.length) := by
  -- ⟪v||w⟫ is defined as: fun p => ⟬v ++ w⟭ (p + |v|)
  -- So ⦋⟪v||w⟫⦌ = fun p => ⦋⟬v ++ w⟭⦌ (p + |v|)
  simp only [CellAutomaton.comp, Function.comp_apply, CellAutomaton.project_config]
  -- Key: embed_config is pointwise, so shift commutes
  have h_config_eq : (embed_config (C := C) ⟪v||w⟫) = fun i => (embed_config (C := C) ⟬v ++ w⟭) (i + v.length) := by
    funext q
    simp only [embed_config, ShiftedConfig]
  -- Using nextt_shift with shift = v.length
  rw [h_config_eq]
  exact congrArg C.project (nextt_shift C (embed_config (C := C) ⟬v ++ w⟭) t p v.length).symm


/-! ## Part IV: The Advice for Injecting x^m

The advice provides compressed representations of x^m for each position.
This is a two-stage advice (RT transducer followed by FST).
-/

section Advice

variable {α : Type} [Alphabet α]

/-- The advice that injects x symbols in compressed form.
    For position i < m/k, provides Compressed(x,...,x).
    For position i ≥ m/k, provides Compressed(#,...,#). -/
def xPrefixAdvice (x : α) (k : ℕ) : Advice α (Fin k → α？) :=
  { f := fun w =>
      let m := nextPow2 w.length
      (List.range w.length).map fun i =>
        if i < m / k then fun _ => some x
        else fun _ => none
  }

/-- Maps Bool to xPrefixAdvice output: true → constant x, false → constant none. -/
private def to_x_output (x : α) : Bool → (Fin k_factor → α？) :=
  fun b => if b then (fun _ => some x) else (fun _ => none)

/-- The x-prefix advice is two-stage for k = k_factor = 8.
    CA stage: `exp_prefix_CA` marks positions where i+1 is a power of 2.
    FST stage: `bFST` counts 3 marks (excluding last) then fills. -/
theorem xPrefixAdvice_is_two_stage (x : α) :
    (xPrefixAdvice x k_factor).is_two_stage_advice := by
  -- Construct the two-stage advice
  refine ⟨⟨Bool, exp_prefix_CA, bFST.map_output (to_x_output x)⟩, ?_⟩
  -- Show ts.advice = xPrefixAdvice x k_factor
  apply advice_eq_iff
  funext w
  simp only [TwoStageAdvice.advice, Function.comp_apply]
  -- Use map_output_spec: (bFST.map_output g).scanr = List.map g ∘ bFST.scanr
  rw [show (bFST.map_output (to_x_output x)).scanr =
        List.map (to_x_output x) ∘ bFST.scanr from FiniteStateTransducer.map_output_spec]
  simp only [Function.comp_apply]
  -- Step 1: exp_prefix_CA.trace_rt w = mark_pow2_v w.length
  have h_trace : exp_prefix_CA.trace_rt w = mark_pow2_v w.length := by
    apply List.ext_getElem
    · simp [mark_pow2_v, CellAutomaton.trace_rt]
    intro i hi1 hi2
    have hi : i < w.length := by
      simp [CellAutomaton.trace_rt] at hi1; exact hi1
    rw [exp_prefix_CA_trace_spec w i hi]
    simp [mark_pow2_v]
  rw [h_trace]
  -- Step 2: bFST.scanr (mark_pow2_v n) = threshold_v n
  rw [bFST_scanr_mark_pow2_eq_threshold]
  -- Step 3: (threshold_v n).map (to_x_output x) = xPrefixAdvice x k_factor w
  simp only [threshold_v, xPrefixAdvice, List.map_map, k_factor]
  congr 1; funext i
  -- to_x_output x (decide (i < nextPow2 n / 8)) = if i < nextPow2 n / 8 then ... else ...
  by_cases h : i < nextPow2 w.length / 8 <;> simp [h, to_x_output]

end Advice


/-! ## Part V: The Main Pipeline

We chain together all the constructions to transform acceptance of x^m w
into acceptance of w. The pipeline is structured similarly to the composition
construction in `compose_cart.lean`.
-/

/-! ### BetaUnionSq extraction -/

/-- Extract value from BetaUnionSq, defaulting if not single. -/
def BetaUnionSq.toSingle {β : Type} [Inhabited β] : BetaUnionSq β → β
  | .single b => b
  | .pair _ _ => default

@[simp]
lemma BetaUnionSq.toSingle_single {β : Type} [Inhabited β] (b : β) :
    (BetaUnionSq.single b).toSingle = b := rfl

/-! ### map_project lemmas -/

@[simp]
lemma map_project_comp {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C : CellAutomaton α β) (f : β → γ) (c : Config C.Q) (t : ℕ) (p : ℤ) :
    (C.map_project f).comp c t p = f (C.comp c t p) := rfl

/-!
### Pipeline Structure

The `LxPipeline` structure encapsulates the entire construction, defining
intermediate CAs at each stage and proving the final specification.

Given:
- `C_orig` : CA_RT accepting `L_x(L)`
- `x` : the marker symbol

The pipeline constructs stages:
- `C₁` : RegularToLeftIndep - converts to left-independent CA
- `C₂` : BroadcastOCA - extends computation time (same CA, uses left-independence)
- Shift embedding - handled via `ShiftedConfig`
- `C₄` : LeftIndepSpeedupConfig - compresses k consecutive cells
- `C₅` : LeftIndepToRegular - converts back to regular CA
- `C₆` : FoldCA - folds bi-infinite config to right-infinite
- `C₇` : BorderNormalize - normalizes borders
- `C_final` : With two-stage advice for x^m prefix
-/

structure LxPipeline where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β
  x : α

attribute [instance] LxPipeline._inst_α
attribute [instance] LxPipeline._inst_β

namespace LxPipeline

  variable (e : LxPipeline)

  /-! #### Word-specific parameters

  For a word w with n = |w| ≥ 8, we define:
  - m := 2^⌈log₂ n⌉ (smallest power of 2 ≥ n)
  - x^m := the prefix of m copies of x
  - [x^m | w] := the shifted embedding with x^m to the left of w
  -/

  /-- The x-prefix of length m = nextPow2(|w|) -/
  def x_prefix (w : Word e.α) : Word e.α := List.replicate (nextPow2 w.length) e.x

  /-- n = |w| -/
  abbrev n (w : Word e.α) : ℕ := w.length

  /-- m = nextPow2(|w|) -/
  abbrev m (w : Word e.α) : ℕ := nextPow2 w.length

  /-! #### Stage 1: RegularToLeftIndep -/

  /-- Stage 1: Convert C_orig to a left-independent CA.
      Spec: C₁.comp(c, 2t, i) = BetaUnionSq.single(C_orig.comp(c, t, i+t)) -/
  abbrev stage1_data : RegularToLeftIndep := {
    C_orig := e.C_orig
  }

  /-- C₁ outputs BetaUnionSq β (intermediate representation) -/
  def C₁ : CellAutomaton e.α？ (BetaUnionSq e.β) := e.stage1_data.C

  /-- C₁' = C₁ with output projected through toSingle, giving β directly -/
  def C₁' : CellAutomaton e.α？ e.β := e.C₁.map_project BetaUnionSq.toSingle

  theorem stage1_spec (c : Config e.α？) (t : ℕ) (i : ℤ) :
      e.C₁.comp c (2*t) i = BetaUnionSq.single (e.C_orig.comp c t (i + t)) :=
    RegularToLeftIndep.spec_even e.stage1_data c t i

  /-- Generic version of stage1_full_spec -/
  theorem stage1_full_spec_generic (c : Config e.α？) (t : ℕ) (i : ℤ) :
      e.C₁'.comp c (2*t) i = e.C_orig.comp c t (i + t) := by
    show (e.C₁.comp c (2*t) i).toSingle = _
    rw [e.stage1_spec c t i]
    rfl

  /-- Stage 1 full spec: For word w with m = nextPow2(|w|), n = |w|:
      C₁'.comp(⟬x^m w⟭, 2(m+n-1), -(m+n-1)) = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      This is Step 1 in the chain. -/
  theorem stage1_full_spec (w : Word e.α) :
      e.C₁'.comp ⟬e.x_prefix w ++ w⟭ (2*(e.m w + e.n w - 1)) (-↑(e.m w + e.n w - 1)) =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    have h := e.stage1_full_spec_generic ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) (-↑(e.m w + e.n w - 1))
    -- Need: -↑(m+n-1) + ↑(m+n-1) = 0
    convert h using 2
    ring

  theorem stage1_left_indep : e.C₁.left_independent :=
    RegularToLeftIndep.C_left_independent e.stage1_data

  /-- C₁' has the same δ as C₁, hence also left-independent -/
  theorem stage1'_left_indep : e.C₁'.left_independent := by
    unfold C₁' left_independent CellAutomaton.map_project
    exact e.stage1_left_indep

  /-! #### Stage 2: Broadcast (conceptually same CA, uses left-independence) -/

  /-- Stage 2: Broadcast structure - extends computation time while preserving result.
      For left-independent CA: comp(c, 2T + r, -T - r) = comp(c, 2T, -T) -/
  abbrev stage2_data : BroadcastOCA := {
    C_orig := e.C₁'
    h_left_indep := e.stage1'_left_indep
  }

  /-- C₂ = C₁' (Broadcast uses same CA, just exploits left-independence property) -/
  def C₂ : CellAutomaton e.α？ e.β := e.stage2_data.C

  theorem stage2_left_indep : e.C₂.left_independent :=
    BroadcastOCA.C_left_independent e.stage2_data

  theorem stage2_spec (c : Config e.α？) (T r : ℕ)
      (hborder : ∀ p : ℤ, p < 0 → c p = none)
      (h0 : (c 0).isSome)
      (hT : T ≥ 1) :
      e.C₂.comp c (2*T + r) (-(T : ℤ) - r) = e.C₁'.comp c (2*T) (-(T : ℤ)) :=
    BroadcastOCA.spec e.stage2_data c T r hborder h0 hT

  /-- Stage 2 full spec: For word w with m = nextPow2(|w|), n = |w|:
      C₂.comp(⟬x^m w⟭, 9(n-1), m - 8(n-1)) = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      Uses T = m+n-1, r = 7(n-1) - 2m.
      This chains from stage1_full_spec. -/
  theorem stage2_full_spec (w : Word e.α) (hr : 7*(e.n w - 1) ≥ 2*(e.m w)) :
      e.C₂.comp ⟬e.x_prefix w ++ w⟭ (9*(e.n w - 1)) ((e.m w : ℤ) - 8*(e.n w - 1)) =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    -- T = m+n-1, r = 7(n-1) - 2m
    -- Time: 2T + r = 2(m+n-1) + 7(n-1) - 2m = 9(n-1)
    -- Position: -T - r = -(m+n-1) - (7(n-1) - 2m) = m - 8(n-1)
    have hm_pos : e.m w ≥ 1 := nextPow2_pos w.length
    -- Border condition: word_to_config returns none for negative positions
    have hborder : ∀ p : ℤ, p < 0 → (⟬e.x_prefix w ++ w⟭ : Config e.α？) p = none := by
      intro p hp
      simp [word_to_config, show ¬(p ≥ 0) from by omega]
    -- Position 0 is inside the word (word is non-empty since m ≥ 1)
    have h_len : (e.x_prefix w ++ w).length = e.m w + e.n w := by
      simp [x_prefix, List.length_append, List.length_replicate]
    have h0 : ((⟬e.x_prefix w ++ w⟭ : Config e.α？) 0).isSome = true := by
      show (word_to_config (e.x_prefix w ++ w) 0).isSome = true
      unfold word_to_config
      split
      · simp
      · exfalso; omega
    -- T = m+n-1 ≥ 1 since m ≥ 1
    have hT : e.m w + e.n w - 1 ≥ 1 := by
      have : e.m w ≥ 1 := hm_pos
      omega
    have h := e.stage2_spec ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) (7*(e.n w - 1) - 2*(e.m w)) hborder h0 hT
    -- h : C₂.comp(⟬x^m w⟭, 2(m+n-1) + r, -(m+n-1) - r) = C₁'.comp(⟬x^m w⟭, 2(m+n-1), -(m+n-1))
    -- RHS of h = C_orig.comp(..., m+n-1, 0) by stage1_full_spec
    calc e.C₂.comp ⟬e.x_prefix w ++ w⟭ (9*(e.n w - 1)) ((e.m w : ℤ) - 8*(e.n w - 1))
        = e.C₂.comp ⟬e.x_prefix w ++ w⟭ (2*(e.m w + e.n w - 1) + (7*(e.n w - 1) - 2*(e.m w)))
            (-↑(e.m w + e.n w - 1) - ↑(7*(e.n w - 1) - 2*(e.m w))) := by
          congr 1 <;> omega
      _ = e.C₁'.comp ⟬e.x_prefix w ++ w⟭ (2*(e.m w + e.n w - 1)) (-↑(e.m w + e.n w - 1)) := h
      _ = e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := e.stage1_full_spec w

  /-! #### Stage 3: Shift embedding (handled via ShiftedConfig notation ⟪v||w⟫) -/

  /-- Stage 3: Translation invariance for shifting.
      comp(⟪v||w⟫, t, p) = comp(⟬v++w⟭, t, p+|v|) -/
  theorem stage3_spec (v w : Word e.α) (t : ℕ) (p : ℤ) :
      e.C₂.comp ⟪v||w⟫ t p = e.C₂.comp ⟬v ++ w⟭ t (p + v.length) :=
    comp_shift e.C₂ v w t p

  /-- Stage 3 full spec: For word w with m = nextPow2(|w|), n = |w|:
      C₂.comp([x^m | w], 9(n-1), -8(n-1)) = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      This chains from stage2_full_spec via the shift.
      Note: [x^m | w] = ⟪x_prefix w || w⟫ -/
  theorem stage3_full_spec (w : Word e.α) (hr : 7*(e.n w - 1) ≥ 2*(e.m w)) :
      e.C₂.comp ⟪e.x_prefix w || w⟫ (9*(e.n w - 1)) (-(8*(e.n w - 1) : ℤ)) =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    -- By shift: C₂.comp(⟪x_prefix w || w⟫, t, p) = C₂.comp(⟬x_prefix w ++ w⟭, t, p + |x_prefix w|)
    rw [e.stage3_spec (e.x_prefix w) w (9*(e.n w - 1)) (-(8*(e.n w - 1) : ℤ))]
    -- p + m = -8(n-1) + m = m - 8(n-1)
    -- Now apply stage2_full_spec
    have h := e.stage2_full_spec w hr
    -- Need: C₂.comp(⟬x^m w⟭, 9(n-1), m - 8(n-1)) = C_orig.comp(⟬x^m w⟭, m+n-1, 0)
    convert h using 2
    simp only [x_prefix, List.length_replicate]
    ring

  /-! #### Stage 4: Speedup (k-compression) -/

  /-- Stage 4: Build the speedup configuration from C₂.
      Since C₂ = C₁' and C₁' is left-independent,
      we build a LeftIndepSpeedupConfig directly. -/
  abbrev stage4_data : LeftIndepSpeedupConfig := {
    C_orig := e.C₂
    k := k_factor
    hk := k_factor_ge_2
    h_left_indep := e.stage2_left_indep
  }

  /-- The compressed CA from Stage 4 -/
  def C₄ : CellAutomaton (SingleOrCompressed k_factor e.α？) (Fin k_factor → e.β) := e.stage4_data.C'

  /-- Stage 4 spec: After k-compression, comp(compress(c), t, i)[j] relates to
      original via time/space transform.

      For i < 0 and t ≥ -i (diagonal regime):
        C₄.comp(compress(c), t, i)[j] = C₂.comp(c, φ(t,i,j), k·i+j)
      where φ(t,i,j) = (t - (k-1)·i - j).toNat -/
  theorem stage4_spec (c : Config e.α？) (i : ℤ) (hi : i < 0) (t : ℕ)
      (ht : (t : ℤ) ≥ -i) (j : Fin k_factor) :
      e.C₄.comp (compressSpatial k_factor c) t i j =
      e.C₂.comp c ((t - (k_factor - 1 : ℕ) * i - j).toNat) (k_factor * i + j) :=
    LeftIndepSpeedupConfig.spec e.stage4_data c i hi t ht j

  /-- Stage 4 full spec: For word w with n = |w|:
      C₄.comp(compress([x^m | w]), 2(n-1), -(n-1))[0] = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      Uses d = n-1, j = 0, t = 2(n-1).
      Chains from stage3_full_spec. -/
  theorem stage4_full_spec (w : Word e.α) (hn : e.n w ≥ 2) (hr : 7*(e.n w - 1) ≥ 2*(e.m w)) :
      e.C₄.comp (compressSpatial k_factor ⟪e.x_prefix w || w⟫) (2*(e.n w - 1)) (-↑(e.n w - 1)) 0 =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    -- By stage4_spec with i = -(n-1), t = 2(n-1), j = 0:
    -- Time in C₂: (2(n-1) - (k-1)*(-(n-1)) - 0).toNat = (2(n-1) + 7(n-1)).toNat = 9(n-1)
    -- Position in C₂: k*(-(n-1)) + 0 = -8(n-1)
    -- First, show that -↑(n-1) = -(↑n - 1) when n ≥ 1
    have hn1 : e.n w ≥ 1 := Nat.le_of_succ_le hn
    have h_cast_sub : (↑(e.n w) - 1 : ℤ) = ↑(e.n w - 1) := by
      rw [Int.ofNat_sub hn1]; rfl
    have h_neg_eq : (-↑(e.n w - 1) : ℤ) = -(↑(e.n w) - 1) := by rw [← h_cast_sub]
    have hi : (-(↑(e.n w) - 1) : ℤ) < 0 := by omega
    have ht : ((↑(2*(e.n w - 1)) : ℤ)) ≥ -(-(↑(e.n w) - 1)) := by omega
    have h := e.stage4_spec ⟪e.x_prefix w || w⟫ (-(↑(e.n w) - 1)) hi (2*(e.n w - 1)) ht 0
    -- h: C₄.comp(...)[0] = C₂.comp(c, (t - 7*i - 0).toNat, 8*i + 0)
    rw [h_neg_eq, h]
    -- Convert to stage3_full_spec form
    have h3 := e.stage3_full_spec w hr
    -- Show the time/position match
    convert h3 using 2
    · -- Time: (↑(2*(n-1)) - ↑(k-1) * -(↑n - 1)).toNat = 9*(n-1)
      simp only [k_factor, Fin.val_zero, CharP.cast_eq_zero, sub_zero, h_cast_sub]
      -- Goal: (↑(2 * (e.n w - 1)) - ↑(8 - 1) * -↑(e.n w - 1)).toNat = 9 * (e.n w - 1)
      -- Key: ↑(8-1) = 7 as a nat, and - a * -b = a * b
      have h_calc : (↑(2 * (e.n w - 1)) - ↑(8 - 1 : ℕ) * -↑(e.n w - 1) : ℤ)
          = ↑(9 * (e.n w - 1)) := by push_cast; ring
      rw [h_calc, Int.toNat_natCast]
    · -- Position: ↑k_factor * -(↑(e.n w) - 1) + ↑(0 : Fin k_factor) = -(8 * (↑(e.n w) - 1))
      simp only [k_factor, Fin.val_zero, CharP.cast_eq_zero, add_zero]
      ring

  /-- C₄ is left-independent (needed for Stage 5) -/
  theorem stage4_left_indep : e.C₄.left_independent :=
    LeftIndepSpeedupConfig.C'_left_independent e.stage4_data

  /-! #### Stage 5: LeftIndepToRegular -/

  /-- Stage 5: Convert left-independent C₄ back to regular CA.
      Spec: C₅.comp(c, t, i) = C₄.comp(c, 2t, i - t) -/
  abbrev stage5_data : LeftIndepToRegular := {
    C_orig := e.C₄
    h_left_indep := e.stage4_left_indep
  }

  def C₅ : CellAutomaton (SingleOrCompressed k_factor e.α？) (Fin k_factor → e.β) := e.stage5_data.C

  theorem stage5_spec (c : Config (SingleOrCompressed k_factor e.α？)) (t : ℕ) (i : ℤ) :
      e.C₅.comp c t i = e.C₄.comp c (2*t) (i - t) :=
    LeftIndepToRegular.spec e.stage5_data c t i

  /-- Stage 5 full spec: For word w with n = |w|:
      C₅.comp(compress([x^m | w]), n-1, 0)[0] = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      Uses t = n-1, i = 0 so i - t = -(n-1).
      Chains from stage4_full_spec. -/
  theorem stage5_full_spec (w : Word e.α) (hn : e.n w ≥ 2) (hr : 7*(e.n w - 1) ≥ 2*(e.m w)) :
      e.C₅.comp (compressSpatial k_factor ⟪e.x_prefix w || w⟫) (e.n w - 1) 0 0 =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    -- By stage5_spec with t = n-1, i = 0:
    -- LHS = C₄.comp(compress([x^m | w]), 2(n-1), 0 - (n-1))
    --     = C₄.comp(compress([x^m | w]), 2(n-1), -(n-1))
    rw [e.stage5_spec (compressSpatial k_factor ⟪e.x_prefix w || w⟫) (e.n w - 1) 0]
    -- Now apply stage4_full_spec (need to show i-t = -(n-1))
    have h := e.stage4_full_spec w hn hr
    convert h using 2
    omega

  /-! #### Stage 6: FoldCA -/

  /-- Stage 6: Fold bi-infinite config to right-infinite.
      Spec: C₆.comp(FoldConfig c, t, i) = C₅.comp(c, t, i) for i ≥ 0 -/
  def C₆ : CellAutomaton (Option (SingleOrCompressed k_factor e.α？ × SingleOrCompressed k_factor e.α？)) (Fin k_factor → e.β) :=
    foldCA e.C₅

  theorem stage6_spec (c : Config (SingleOrCompressed k_factor e.α？)) (t : ℕ) (i : ℤ) (hi : 0 ≤ i) :
      e.C₆.comp (FoldConfig c) t i = e.C₅.comp c t i :=
    fold_spec e.C₅ c t i hi

  /-- Stage 6 full spec: For word w with n = |w|:
      C₆.comp(Fold(compress([x^m | w])), n-1, 0)[0] = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      Uses t = n-1, i = 0.
      Chains from stage5_full_spec. -/
  theorem stage6_full_spec (w : Word e.α) (hn : e.n w ≥ 2) (hr : 7*(e.n w - 1) ≥ 2*(e.m w)) :
      e.C₆.comp (FoldConfig (compressSpatial k_factor ⟪e.x_prefix w || w⟫)) (e.n w - 1) 0 0 =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    -- By stage6_spec with t = n-1, i = 0:
    -- LHS = C₅.comp(compress([x^m | w]), n-1, 0)
    rw [e.stage6_spec (compressSpatial k_factor ⟪e.x_prefix w || w⟫) (e.n w - 1) 0 (le_refl 0)]
    -- Now apply stage5_full_spec
    exact e.stage5_full_spec w hn hr

  /-! #### Stage 7: BorderNormalize -/

  /-- Abbreviation for the folded input type -/
  abbrev FoldedInput := Option (SingleOrCompressed k_factor e.α？ × SingleOrCompressed k_factor e.α？)

  /-- Left border: none represents p < 0 where FoldConfig returns none -/
  def left_border : e.FoldedInput := none

  /-- Right border value: The constant value FoldConfig returns for p ≥ n.
      Defined explicitly as the FoldConfig value at position 0 for the empty border config,
      which represents "all # / out of bounds". -/
  def right_border_const : e.FoldedInput :=
    -- For positions outside the word, compress returns:
    -- - At p ≥ 0: .single none  -- single border symbol
    -- - At p < 0: .compressed (fun _ => none)  -- compressed border symbols
    -- FoldConfig at p ≥ n gives: some (single_border, compressed_border)
    some (SingleOrCompressed.single none,
          SingleOrCompressed.compressed (fun _ => none))

  /-- Legacy alias for left_border -/
  abbrev border := e.left_border

  /-- Stage 7: Normalize borders.
      Input: FoldedInput?  (i.e., Option (Option (Input × Input)))
      Left border = none, Right border = (Single(#), Compressed(#,...,#)) -/
  def C₇ : CellAutomaton e.FoldedInput？ (Fin k_factor → e.β) :=
    borderNormalizeCA e.C₆ e.left_border e.right_border_const

  /-- Stage 7 spec: C₇.trace(w) = C₆.trace(BorderedConfig left_border [] w right_border_const) -/
  theorem stage7_spec (w : Word e.FoldedInput) (hw : w ≠ []) :
      e.C₇.trace w = e.C₆.trace (BorderedConfig e.left_border [] w e.right_border_const) :=
    borderNormalizeCA_trace e.C₆ e.left_border e.right_border_const w hw

  /-! #### Encoding: Extracting a finite word from FoldConfig

  The key insight is that `FoldConfig (compress ⟪x^m | w⟫)` is:
  - `none` for positions p < 0
  - varying for positions 0 ≤ p < n
  - constant (right border) for positions p ≥ n

  So we extract positions 0..n-1 as the finite "encoded word".
  -/

  /-- The folded configuration for the shifted embedding. -/
  abbrev foldedConfig (w : Word e.α) : Config e.FoldedInput :=
    FoldConfig (compressSpatial k_factor ⟪e.x_prefix w || w⟫)

  /-- Extract the finite word from FoldConfig at positions 0..n-1.
      This captures all the varying information; positions outside are borders. -/
  def encoded_word (w : Word e.α) : Word e.FoldedInput :=
    List.ofFn (fun i : Fin (e.n w) => (e.foldedConfig w) i)

  /-- Key lemma: For p ≥ n, FoldConfig returns the constant right border.
      This is because:
      - compress(c)(p) = Input.single(embed(c(p))) = Input.single(embed(#)) for p ≥ n
      - compress(c)(-(p+1)) = Input.compressed(...) with all embed(#)
  -/
  theorem foldedConfig_eq_right_border_const (w : Word e.α) (p : ℤ) (hw : e.n w ≥ 1)
      (hp : p ≥ e.n w)
      (hm : (e.m w : ℤ) ≤ k_factor * ((e.n w : ℤ) + 1 - k_factor)) :
      e.foldedConfig w p = e.right_border_const := by
    -- For p ≥ n ≥ 0, FoldConfig returns some (compress(c)(p), compress(c)(-(p+1)))
    simp only [foldedConfig, FoldConfig]
    have hp0 : ¬(p < 0) := by omega
    simp only [hp0, ↓reduceIte]
    -- Need to show some (...) = some (...)
    simp only [right_border_const]
    congr 1
    -- Now goal: (compress p, compress (-(p+1))) = (.single ..., .compressed ...)
    -- Both components reduce to the same "embed(none)" value
    unfold compressSpatial
    have hp_nn : p ≥ 0 := by omega
    have hneg : -p - 1 < 0 := by omega
    -- Bridge between e.n/e.m and w.length/nextPow2 w.length for omega
    have h_n_eq : e.n w = w.length := rfl
    have h_m_eq : e.m w = nextPow2 w.length := rfl
    -- Rewrite hw, hp, and hm in terms of w.length for omega
    simp only [h_n_eq, h_m_eq] at hw hp hm
    split_ifs with h1
    · -- p ≥ 0, -p-1 ≥ 0: impossible since hneg says -p-1 < 0
      omega
    · -- p ≥ 0, -p-1 < 0: this is our case
      ext
      · -- First component: show p ≥ w.length to use word_to_config_right_border
        simp only [ShiftedConfig, x_prefix]
        rw [word_to_config_right_border]
        simp only [List.length_append, List.length_replicate]
        omega
      · -- Second component: show k_factor * (-p - 1) + j + m < 0 for left border
        simp only []
        congr 1
        funext j
        simp only [ShiftedConfig, x_prefix]
        rw [word_to_config_left_border]
        simp only [List.length_replicate]
        -- Use: j < k_factor, p ≥ w.length ≥ 1, m ≤ k_factor * (w.length + 1 - k_factor)
        have hj : (j : ℤ) < k_factor := by omega
        -- Manual calculation: k_factor * (-p - 1) + j + m < 0
        -- Since p ≥ w.length ≥ 1, we have -p - 1 ≤ -w.length - 1 ≤ -2
        -- So k_factor * (-p - 1) ≤ k_factor * (-w.length - 1)
        -- And j ≤ k_factor - 1
        -- And m ≤ k_factor * (w.length + 1 - k_factor) from hm
        -- Total: k_factor * (-w.length - 1) + (k_factor - 1) + k_factor * (w.length + 1 - k_factor)
        --      = k_factor * ((-w.length - 1) + (w.length + 1 - k_factor)) + k_factor - 1
        --      = k_factor * (-k_factor) + k_factor - 1
        --      = -k_factor² + k_factor - 1
        --      = -64 + 8 - 1 = -57 < 0
        calc (k_factor : ℤ) * (-p - 1) + j + nextPow2 w.length
            ≤ k_factor * (-(w.length : ℤ) - 1) + (k_factor - 1) + (k_factor * ((w.length : ℤ) + 1 - k_factor)) := by
              have hp_bound : -p ≤ -(w.length : ℤ) := by omega
              have hj_bound : (j : ℤ) ≤ k_factor - 1 := by omega
              nlinarith
          _ = k_factor * (-(w.length : ℤ) - 1 + ((w.length : ℤ) + 1 - k_factor)) + k_factor - 1 := by ring
          _ = k_factor * (-k_factor) + k_factor - 1 := by ring
          _ = -(k_factor : ℤ)^2 + k_factor - 1 := by ring
          _ < 0 := by simp only [k_factor]; omega

  /-- The bordered config equals the folded config -/
  theorem bordered_eq_folded (w : Word e.α) (hw : e.n w ≥ 1)
      (hm : (e.m w : ℤ) ≤ k_factor * ((e.n w : ℤ) + 1 - k_factor)) :
      BorderedConfig e.left_border [] (e.encoded_word w) e.right_border_const = e.foldedConfig w := by
    funext p
    simp only [BorderedConfig, encoded_word, List.length_ofFn]
    split_ifs with h1 h2
    · -- 0 ≤ p < n: the varying region, read from encoded_word
      simp only [foldedConfig, List.getElem_ofFn]
      congr 1
      omega
    · -- -0 ≤ p < 0: impossible since v = []
      simp only [List.length_nil] at h2
      omega
    · -- p ≥ n: right border region
      simp only [not_and, not_lt] at h1 h2
      have hp : p ≥ (e.n w : ℤ) := by omega
      -- Use foldedConfig_eq_right_border_const
      rw [e.foldedConfig_eq_right_border_const w p hw hp hm]
    · -- p < 0: left border region, FoldConfig returns none
      simp only [not_and, not_lt] at h1 h2
      have hp : p < 0 := by omega
      simp only [foldedConfig, FoldConfig, hp, ↓reduceIte, left_border]

  /-- Length of encoded_word -/
  @[simp]
  theorem encoded_word_length (w : Word e.α) : (e.encoded_word w).length = e.n w := by
    simp only [encoded_word, List.length_ofFn]

  /-- encoded_word is non-empty when n ≥ 1 -/
  theorem encoded_word_ne_nil (w : Word e.α) (hw : e.n w ≥ 1) : e.encoded_word w ≠ [] := by
    simp only [encoded_word, ne_eq, List.ofFn_eq_nil_iff]
    omega

  /-- Stage 7 full spec (parameterized): For word w with explicit hr and hm bounds.
      C₇.trace(encoded_word w)(n-1)[0] = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      The encoded_word extracts the finite varying portion of FoldConfig.
      The theorem chains from stage6_full_spec via bordered_eq_folded. -/
  theorem stage7_full_spec' (w : Word e.α) (hn : e.n w ≥ 2) (hr : 7*(e.n w - 1) ≥ 2*(e.m w))
      (hm : (e.m w : ℤ) ≤ k_factor * ((e.n w : ℤ) + 1 - k_factor)) :
      e.C₇.trace (e.encoded_word w) (e.n w - 1) 0 =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    have hn1 : e.n w ≥ 1 := Nat.le_of_succ_le hn
    -- Step 1: C₇.trace(encoded_word) = C₆.trace(BorderedConfig(left_border, [], encoded_word, right_border_const))
    have h7 := e.stage7_spec (e.encoded_word w) (e.encoded_word_ne_nil w hn1)
    have h7' : e.C₇.trace (e.encoded_word w) (e.n w - 1) 0 =
               e.C₆.trace (BorderedConfig e.left_border [] (e.encoded_word w) e.right_border_const) (e.n w - 1) 0 :=
      congr_fun (congr_fun h7 (e.n w - 1)) 0
    rw [h7']
    -- Step 2: BorderedConfig = FoldConfig (by bordered_eq_folded)
    rw [e.bordered_eq_folded w hn1 hm]
    -- Step 3: Unfold trace and apply stage6_full_spec
    simp only [CellAutomaton.trace, foldedConfig]
    -- After unfolding, goal involves C₆.comp ⦋FoldConfig (compress ⟪...⟫)⦌
    -- We need embed_FoldConfig to convert ⦋FoldConfig c⦌ to the right form
    simp only [embed_FoldConfig]
    exact e.stage6_full_spec w hn hr

  /-- Stage 7 full spec (simplified): For word w with n = |w| ≥ 9 (= k_factor + 1):
      C₇.trace(encoded_word w)(n-1)[0] = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      This version derives hr and hm from the single bound n ≥ 9:
      - hr: 7*(n-1) ≥ 2*m follows from m ≤ 2*(n-1) for n ≥ 2
      - hm: m ≤ 8*(n-7) follows from m ≤ 2*(n-1) and n ≥ 9 -/
  theorem stage7_full_spec (w : Word e.α) (hn : e.n w ≥ k_factor + 1) :
      e.C₇.trace (e.encoded_word w) (e.n w - 1) 0 =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    simp only [k_factor] at hn
    have hn2 : e.n w ≥ 2 := by omega
    have hr : 7*(e.n w - 1) ≥ 2*(e.m w) := hr_from_n_ge_2 (e.n w) hn2
    have hm : (e.m w : ℤ) ≤ k_factor * ((e.n w : ℤ) + 1 - k_factor) := by
      simp only [k_factor]
      -- e.m w = nextPow2 (e.n w) = nextPow2 w.length
      have hm_eq : e.m w = nextPow2 (e.n w) := rfl
      have h := nextPow2_le_two_pred (e.n w) hn2
      -- h: nextPow2 (e.n w) ≤ 2 * (e.n w - 1)
      -- Need: m ≤ 8 * (n + 1 - 8) = 8 * (n - 7) = 8n - 56
      -- From h: m ≤ 2 * (n - 1) = 2n - 2
      -- Need: 2n - 2 ≤ 8n - 56 ↔ 54 ≤ 6n ↔ 9 ≤ n ✓
      omega
    exact e.stage7_full_spec' w hn2 hr hm

  /-! #### Stage 8: Two-stage advice elimination -/

  /-- Stage 8: Two-stage advice is RT-closed -/
  theorem stage8_two_stage_rt_closed
      {Γ : Type} [Alphabet Γ] (adv : TwoStageAdvice e.α Γ) :
      adv.advice.rt_closed :=
    two_stage_is_rt_closed adv

  /-! #### Stage 8b: Advice Decomposition and Elimination -/

  /-- The advice providing the compressed x-prefix information at each position.
      At position i of word w (with m = nextPow2(|w|), k = k_factor):
      - `fun _ => some x` if `i < m/k` (position falls in x-prefix region)
      - `fun _ => none`   if `i ≥ m/k` (position is past x-prefix) -/
  def foldAdvice : Advice e.α (Fin k_factor → e.α？) := xPrefixAdvice e.x k_factor

  /-- Encoding from (word letter, advice value) into FoldedInput.
      Maps (a, γ) to some (.single (some a), .compressed γ). -/
  def foldInputEncode : e.α × (Fin k_factor → e.α？) → e.FoldedInput :=
    fun (a, γ) => some (.single (some a), .compressed γ)

  /-- Decomposition: encoded_word w = (w ⨂ foldAdvice.f w).map foldInputEncode.

      Each position i of encoded_word w decomposes as:
      - Word component: .single (some w[i]) — the letter embedded in SingleOrCompressed
      - Advice component: .compressed (foldAdvice.f w [i]) — the x-prefix advice

      Together: some (.single (some w[i]), .compressed (advice[i]))
             = foldInputEncode (w[i], advice[i])

      Requires |w| ≥ k+1 = 9 so that 8 | m (ensuring k-cell boundaries
      align with the x-prefix boundary).

      TODO: Complete arithmetic proof showing:
      - First component: compressSpatial at position i lands in w part → some w[i]
      - Second component: compressSpatial at positions k*(-(i+1))+j:
        * If i < m/k: lands in x^m prefix → some x
        * If i ≥ m/k: lands in negative positions → none -/
  theorem encoded_word_eq_annotated (w : Word e.α) (hn : e.n w ≥ k_factor + 1) :
      e.encoded_word w = (w ⨂ e.foldAdvice.f w).map e.foldInputEncode := by
    -- Both sides are lists of length n = w.length
    apply List.ext_getElem
    · simp only [encoded_word, List.length_ofFn, List.length_map, List.length_zip, advice_len, min_self]
    -- Element-wise equality
    intro i hi1 hi2
    simp only [encoded_word, List.getElem_ofFn, List.getElem_map, List.getElem_zip]
    -- Unfold the definitions
    simp only [foldedConfig, FoldConfig, foldInputEncode, compressSpatial]
    -- For i : ℕ viewed as ℤ:
    -- - i ≥ 0 is true
    -- - -(i:ℤ) - 1 < 0 is true
    have hi_ge : (i : ℤ) ≥ 0 := Int.natCast_nonneg i
    have hi_neg : -↑i - 1 < (0 : ℤ) := by omega
    simp only [hi_ge, Int.not_lt.mpr hi_ge, Int.not_le.mpr hi_neg, ↓reduceIte]
    -- Both sides are now: some (.single (...), .compressed (...))
    -- First establish hi_lt: i < w.length
    have hi_lt : i < w.length := by simp only [encoded_word, List.length_ofFn, n] at hi1; exact hi1
    -- The goal is: some (..., ...) = some (..., ...)
    -- First unwrap Option.some, then handle the Prod
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    -- First component: .single (⟪...⟫ i) = .single (some w[i])
    -- ShiftedConfig ⟬x_prefix w ++ w⟭ m i = ⟬x_prefix w ++ w⟭ (i + m)
    -- Since i + m ∈ [m, m + n - 1], this is w[i]
    · simp only [ShiftedConfig, x_prefix, word_to_config, List.length_append, List.length_replicate]
      have hm_pos : e.m w ≥ 1 := nextPow2_pos w.length
      have h_in_range : 0 ≤ (i : ℤ) + ↑(e.m w) ∧ (i : ℤ) + ↑(e.m w) < ↑(e.m w + w.length) := by omega
      simp only [h_in_range, ↓reduceDIte, and_self, Int.toNat_add (Int.natCast_nonneg i) (Int.natCast_nonneg _),
                 Int.toNat_natCast]
      -- Need to prove: (List.replicate m e.x ++ w)[i + m] = w[i]
      have h_in_w : (List.replicate (e.m w) e.x).length ≤ i + e.m w := by simp [List.length_replicate]
      rw [List.getElem_append_right h_in_w]
      simp only [List.length_replicate, Nat.add_sub_cancel]
    -- Second component: .compressed (...) = .compressed (foldAdvice.f w[i])
    · show SingleOrCompressed.compressed _ = SingleOrCompressed.compressed _
      congr 1
      simp only [foldAdvice, xPrefixAdvice, List.getElem_map, List.getElem_range]
      funext j
      -- Calculate position: k_factor * (-(i:ℤ) - 1) + j + m = m - k*(i+1) + j
      simp only [ShiftedConfig, x_prefix, word_to_config, List.length_append, List.length_replicate]
      have hw_len : w.length ≥ 8 := Nat.le_of_succ_le hn
      have hm_div : k_factor ∣ e.m w := eight_dvd_nextPow2 w.length hw_len
      have hj_lt : (j : ℕ) < k_factor := j.isLt
      have pos_rewrite : (k_factor : ℤ) * (-(i : ℤ) - 1) + ↑↑j + ↑(e.m w) = ↑(e.m w) - ↑k_factor * (↑i + 1) + ↑j := by ring
      -- Explicitly split on the advice condition: i < m/k
      by_cases h_advlt : i < e.m w / k_factor
      · -- Case: i < m/k, positions land in x^m prefix → some x
        simp only [h_advlt, ↓reduceIte]
        have hi1_le : i + 1 ≤ e.m w / k_factor := Nat.lt_iff_add_one_le.mp h_advlt
        have h_mul_le : k_factor * (i + 1) ≤ e.m w :=
          calc k_factor * (i + 1) ≤ k_factor * (e.m w / k_factor) := Nat.mul_le_mul_left _ hi1_le
            _ ≤ e.m w := Nat.mul_div_le (e.m w) k_factor
        -- Convert all bounds to ℤ for omega
        have h_mul_le_int : (k_factor : ℤ) * (↑i + 1) ≤ ↑(e.m w) := by exact_mod_cast h_mul_le
        have hj_int : (↑↑j : ℤ) ≥ 0 := Int.natCast_nonneg _
        have hj_bound : (↑↑j : ℤ) < ↑k_factor := by exact_mod_cast hj_lt
        have hi_nonneg : (↑i : ℤ) ≥ 0 := Int.natCast_nonneg _
        have hk_pos : (↑k_factor : ℤ) > 0 := by simp [k_factor]
        -- i + 1 ≥ 1, so k * (i + 1) ≥ k > j
        have hi1_ge : (↑i : ℤ) + 1 ≥ 1 := by omega
        have hki_ge_k : (↑k_factor : ℤ) * (↑i + 1) ≥ ↑k_factor := by nlinarith
        -- Calculate bounds
        have h_pos_ge : (↑(e.m w) : ℤ) - ↑k_factor * (↑i + 1) + ↑↑j ≥ 0 := by linarith
        have h_in_prefix_int : (↑(e.m w) : ℤ) - ↑k_factor * (↑i + 1) + ↑↑j < ↑(e.m w) := by
          -- Need: -k*(i+1) + j < 0, i.e., j < k*(i+1)
          -- We have j < k and k*(i+1) ≥ k, so j < k ≤ k*(i+1)
          linarith
        have hwlen_pos : (↑w.length : ℤ) ≥ 0 := Int.natCast_nonneg _
        have h_pos_lt : (↑(e.m w) : ℤ) - ↑k_factor * (↑i + 1) + ↑↑j < ↑(e.m w) + ↑w.length := by linarith
        have h_cond : 0 ≤ (k_factor : ℤ) * (-(i : ℤ) - 1) + ↑↑j + ↑(e.m w) ∧
            (k_factor : ℤ) * (-(i : ℤ) - 1) + ↑↑j + ↑(e.m w) < ↑(e.m w + w.length) := by
          simp only [pos_rewrite, Nat.cast_add]; exact ⟨h_pos_ge, h_pos_lt⟩
        simp only [h_cond, ↓reduceDIte, and_self]
        -- Position is in the x^m prefix
        have h_in_prefix : ((k_factor : ℤ) * (-(i : ℤ) - 1) + ↑↑j + ↑(e.m w)).toNat < (List.replicate (e.m w) e.x).length := by
          simp only [List.length_replicate, pos_rewrite]
          omega
        simp only [List.getElem_append_left h_in_prefix, List.getElem_replicate]
      · -- Case: i ≥ m/k, positions land in negative region → none
        simp only [h_advlt, ↓reduceIte]
        have h1 : e.m w / k_factor ≤ i := Nat.not_lt.mp h_advlt
        have h_m_lt : e.m w < k_factor * (i + 1) := by
          have hk : k_factor > 0 := by omega
          calc e.m w = k_factor * (e.m w / k_factor) + e.m w % k_factor := (Nat.div_add_mod _ _).symm
            _ ≤ k_factor * (e.m w / k_factor) + (k_factor - 1) := by
                have : e.m w % k_factor < k_factor := Nat.mod_lt _ hk
                omega
            _ ≤ k_factor * i + (k_factor - 1) := by
                have : k_factor * (e.m w / k_factor) ≤ k_factor * i := Nat.mul_le_mul_left _ h1
                omega
            _ < k_factor * i + k_factor := by omega
            _ = k_factor * (i + 1) := by ring
        have h_m_lt_int : (↑(e.m w) : ℤ) < ↑k_factor * (↑i + 1) := by exact_mod_cast h_m_lt
        have hj_bound : (↑↑j : ℤ) < ↑k_factor := by exact_mod_cast hj_lt
        have hj_ge : (↑↑j : ℤ) ≥ 0 := Int.natCast_nonneg _
        -- m < k*(i+1) and j < k, so m + j < k*(i+1) + k = k*(i+2)
        -- But we need m - k*(i+1) + j < 0, which is m + j < k*(i+1)
        -- From h_m_lt_int: m < k*(i+1), and j ≥ 0, so m + j may not be < k*(i+1)
        -- Actually we need: m - k*(i+1) + j < 0 ⟺ j < k*(i+1) - m
        -- We have m < k*(i+1), so k*(i+1) - m > 0
        -- Also j < k. If m + k ≤ k*(i+1), then m + j < m + k ≤ k*(i+1), so m + j - k*(i+1) < 0
        -- We have m < k*(i+1) ≤ k*i + k. So k*(i+1) - m > 0.
        -- Need: j < k*(i+1) - m. Since j < k and m < k*(i+1), we have k*(i+1) - m ≥ 1 when k*(i+1) > m.
        -- Actually k*(i+1) > m by h_m_lt_int, and j < k, so if k*(i+1) - m ≥ k then j < k ≤ k*(i+1) - m.
        -- We need k*(i+1) - m ≥ k ⟺ k*i ≥ m ⟺ i ≥ m/k.
        -- We have h1: m/k ≤ i, so i ≥ m/k, hence k*i ≥ k*(m/k) ≥ m - (k-1) (by division).
        -- Actually this is getting complicated. Let's just use linarith more carefully.
        have hi_ge_div : (↑i : ℤ) ≥ ↑(e.m w / k_factor) := by exact_mod_cast h1
        have hkdiv_le : (↑k_factor : ℤ) * ↑(e.m w / k_factor) ≤ ↑(e.m w) := by
          exact_mod_cast Nat.mul_div_le (e.m w) k_factor
        have hki_ge_m : (↑k_factor : ℤ) * ↑i ≥ ↑k_factor * ↑(e.m w / k_factor) := by
          have hk_pos : (↑k_factor : ℤ) > 0 := by simp [k_factor]
          nlinarith
        -- So k*i ≥ k*(m/k) ≥ m (roughly)
        -- We have k - j > 0 (since j < k)
        -- m - k*(i+1) + j = m - k*i - k + j < m - m + 0 = 0 when k*i ≥ m and k > j
        -- Actually: m - k*i - k + j. If k*i ≥ m then m - k*i ≤ 0.
        -- So m - k*i - k + j ≤ 0 - k + j = j - k < 0 since j < k.
        have h_pos_neg : (↑(e.m w) : ℤ) - ↑k_factor * (↑i + 1) + ↑↑j < 0 := by
          have hk_pos : (↑k_factor : ℤ) > 0 := by simp [k_factor]
          -- Key: k | m, so m = k * (m/k) exactly (no remainder)
          have h_m_eq : e.m w = k_factor * (e.m w / k_factor) := Nat.eq_mul_of_div_eq_right hm_div rfl
          have h_m_eq_int : (↑(e.m w) : ℤ) = ↑k_factor * ↑(e.m w / k_factor) := by exact_mod_cast h_m_eq
          -- Since i ≥ m/k, we have i + 1 > m/k, so k*(i+1) > k*(m/k) = m
          have h_gt : k_factor * (e.m w / k_factor) < k_factor * (i + 1) := by
            have : e.m w / k_factor < i + 1 := Nat.lt_succ_of_le h1
            exact Nat.mul_lt_mul_of_pos_left this (by omega : k_factor > 0)
          have h_gt_int : (↑k_factor : ℤ) * ↑(e.m w / k_factor) < ↑k_factor * (↑i + 1) := by exact_mod_cast h_gt
          -- So m - k*(i+1) = k*(m/k) - k*(i+1) < 0
          -- In fact, m - k*(i+1) ≤ -k since m = k*(m/k) and k*(i+1) ≥ k*(m/k + 1) = m + k
          have h_diff_neg : (↑(e.m w) : ℤ) - ↑k_factor * (↑i + 1) ≤ -↑k_factor := by
            rw [h_m_eq_int]
            have hi_ge : i + 1 ≥ e.m w / k_factor + 1 := Nat.add_le_add_right h1 1
            have : (↑k_factor : ℤ) * (↑i + 1) ≥ ↑k_factor * (↑(e.m w / k_factor) + 1) := by
              have h : (↑i : ℤ) + 1 ≥ ↑(e.m w / k_factor) + 1 := by exact_mod_cast hi_ge
              nlinarith
            linarith
          -- Since j < k, we have j ≤ k - 1, so m - k*(i+1) + j ≤ -k + (k-1) = -1 < 0
          have hj_le : (↑↑j : ℤ) ≤ ↑k_factor - 1 := by
            have hk_ge : k_factor ≥ 1 := by omega
            have hj_add : (j : ℕ) + 1 ≤ k_factor := Nat.lt_iff_add_one_le.mp hj_lt
            have hj_nat : (j : ℕ) ≤ k_factor - 1 := by omega
            omega
          linarith
        have h_neg : ¬(0 ≤ (k_factor : ℤ) * (-(i : ℤ) - 1) + ↑↑j + ↑(e.m w) ∧
                       (k_factor : ℤ) * (-(i : ℤ) - 1) + ↑↑j + ↑(e.m w) < ↑(e.m w + w.length)) := by
          simp only [pos_rewrite]; omega
        simp only [h_neg, ↓reduceDIte]

  /-- The fold advice is two-stage (RT transducer marks powers of 2,
      then FST computes compressed cells). -/
  theorem foldAdvice_is_two_stage : e.foldAdvice.is_two_stage_advice :=
    xPrefixAdvice_is_two_stage e.x

  /-- The fold advice is RT-closed (two-stage ⟹ RT-closed). -/
  theorem foldAdvice_rt_closed : e.foldAdvice.rt_closed := by
    obtain ⟨ts, hts⟩ := e.foldAdvice_is_two_stage
    rw [← hts]
    exact two_stage_is_rt_closed ts

  /-- The advice alphabet: word letter paired with compressed x-prefix info. -/
  abbrev AdvicedInput := e.α × (Fin k_factor → e.α？)

  /-- C₇₀: CA over (α × (Fin k → α？))？ with output β.
      Built from C₇ by:
      - Projecting output to component 0 (map_project)
      - Embedding input through foldInputEncode (map_embed)
      This CA directly accepts annotated words w ⨂ foldAdvice.f w. -/
  def C₇₀ : CellAutomaton e.AdvicedInput？ e.β :=
    (e.C₇.map_project (· 0)).map_embed (Option.map e.foldInputEncode)

  /-- C₇₀.trace(w ⨂ advice)(t) = (C₇.map_project (· 0)).trace(w.map foldInputEncode)(t).
      Relates the remapped CA to the original via map_embed. -/
  theorem C₇₀_trace_eq (w : Word e.AdvicedInput) (t : ℕ) :
      e.C₇₀.trace w t =
      (e.C₇.map_project (· 0)).trace (w.map e.foldInputEncode) t := by
    simp only [C₇₀, CellAutomaton.trace, CellAutomaton.comp, Function.comp,
               CellAutomaton.project_config, CellAutomaton.map_project,
               CellAutomaton.map_embed]
    -- Goal: project the nextt at position 0, showing both sides equal
    -- Key: show nextt is the same for both CAs
    have h_embed_eq : ∀ p : ℤ,
        @embed_config _ _ ((e.C₇.map_project (· 0)).map_embed (Option.map e.foldInputEncode))
          (word_to_config w) p =
        @embed_config _ _ (e.C₇.map_project (· 0)) (word_to_config (w.map e.foldInputEncode)) p := by
      intro p
      simp only [embed_config, CellAutomaton.map_embed, CellAutomaton.map_project,
                 Function.comp, word_to_config, List.length_map]
      split_ifs with h
      · simp only [Option.map_some, List.getElem_map]
      · simp only [Option.map_none]
    have h_nextt_eq : ∀ t' : ℕ, ∀ p : ℤ,
        ((e.C₇.map_project (· 0)).map_embed (Option.map e.foldInputEncode)).nextt ⦋w⦌ t' p =
        (e.C₇.map_project (· 0)).nextt ⦋w.map e.foldInputEncode⦌ t' p := by
      intro t'
      induction t' with
      | zero => intro p; exact h_embed_eq p
      | succ t' ih =>
        intro p
        simp only [CellAutomaton.nextt, Function.iterate_succ_apply', CellAutomaton.next,
                   CellAutomaton.map_embed, CellAutomaton.map_project]
        congr 1 <;> exact ih _
    exact congrArg (e.C₇.map_project (· 0)).project (h_nextt_eq t 0)

  /-- Stage 8 full spec: For word w with n ≥ k+1 = 9:
      C₇₀.trace(w ⨂ foldAdvice.f w)(n-1) = C_orig.comp(⟬x^m w⟭, m+n-1, 0)

      This is the key result connecting the remapped CA to the original acceptance. -/
  theorem stage8_full_spec (w : Word e.α) (hn : e.n w ≥ k_factor + 1) :
      e.C₇₀.trace (w ⨂ e.foldAdvice.f w) (e.n w - 1) =
      e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 := by
    -- Step 1: C₇₀.trace(w ⨂ advice)(n-1) = (C₇.map_project (· 0)).trace(encoded_word w)(n-1)
    rw [e.C₇₀_trace_eq]
    -- Step 2: (w ⨂ foldAdvice.f w).map foldInputEncode = encoded_word w
    rw [← e.encoded_word_eq_annotated w hn]
    -- Step 3: (C₇.map_project (· 0)).trace(encoded_word w)(n-1) = C₇.trace(encoded_word w)(n-1) 0
    simp only [CellAutomaton.map_project, CellAutomaton.trace, CellAutomaton.comp,
               CellAutomaton.project_config, Function.comp]
    -- Step 4: = C_orig.comp(⟬x^m w⟭, m+n-1, 0) by stage7_full_spec
    exact e.stage7_full_spec w hn

  /-! #### Stage 9: Advice Elimination via RT-closedness

  Since `foldAdvice` is RT-closed, we can construct a CA_rt that accepts
  the same language as C₇₀ + foldAdvice, without needing the advice.

  This construction is only valid when β = Bool (i.e., for accepting CAs).
  -/

  /-- The advice type for the folding construction. -/
  abbrev FoldAdviceType := Fin k_factor → e.α？

  /-- foldAdvice is weak-RT-closed (follows from being RT-closed). -/
  theorem foldAdvice_weak_rt_closed : e.foldAdvice.weak_rt_closed := by
    have h := e.foldAdvice_rt_closed e.α id
    -- adv.lift id = adv since List.map id = id
    simp only [Advice.lift, List.map_id] at h
    exact h

end LxPipeline

/-!
### Advice Elimination Utilities

RT-closed advice can be eliminated: if advice is RT-closed,
then the language defined by a CA with advice still belongs to CA_rt.
-/

/-- RT-closed implies weak-RT-closed (taking π = id). -/
lemma rt_closed_implies_weak_rt_closed {α Γ : Type} [Alphabet α] [Alphabet Γ]
    (adv : Advice α Γ) (h : adv.rt_closed) : adv.weak_rt_closed := by
  have := h α id
  -- adv.lift id = adv since (List.map id w = w)
  simp only [Advice.lift, List.map_id] at this
  exact this

/-- Advice elimination lemma: Given a CA with RT-closed advice,
    there exists an RT CA accepting the same language.

    This is the key lemma dual to `tCellAutomatonWithAdvice.exists_CA_rt_of_weak_rt_closed`. -/
theorem exists_CA_rt_of_rt_closed_advice
    {α Γ : Type} [Alphabet α] [Alphabet Γ]
    (C : CA_rt (α × Γ))
    (adv : Advice α Γ)
    (h_rt_closed : adv.rt_closed) :
    ∃ (C' : CA_rt α), C'.val.L = (C.val + adv).L := by
  exact tCellAutomatonWithAdvice.exists_CA_rt_of_weak_rt_closed
    (rt_closed_implies_weak_rt_closed adv h_rt_closed) C

/-! ### Main Theorem -/

/-- Membership in L_x for lifted words with padding m = nextPow2|w| ≥ |w|. -/
lemma L_x_mem_of_mem {α : Type} [Alphabet α] {L : Language α} {w : Word α} (hw : w ∈ L) :
    List.replicate (nextPow2 w.length) none ++ w.map some ∈ L_x L := by
  refine ⟨w, nextPow2 w.length, hw, nextPow2_ge_self w.length, rfl⟩

/-- filterMap id removes none and unwraps some. -/
private lemma filterMap_replicate_none_append_map_some {α : Type} (k : ℕ) (v : List α) :
    (List.replicate k none ++ v.map some).filterMap id = v := by
  induction k with
  | zero => simp [List.filterMap_map]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, List.filterMap_cons, id_eq]
    exact ih

/-- Extracting the original word from an L_x membership.
    If none^k ++ v.map some ∈ L_x(L), then v ∈ L.

    Proof idea: none ≠ some _, so the split point in none^k ++ v.map some
    is uniquely determined by where `some` values start. Therefore v = u. -/
lemma mem_of_L_x_mem {α : Type} [Alphabet α] {L : Language α} {v : Word α} {k : ℕ}
    (h : List.replicate k none ++ v.map some ∈ L_x L) : v ∈ L := by
  obtain ⟨u, k', hu, _, heq⟩ := h
  -- heq: none^k ++ v.map some = none^k' ++ u.map some
  -- Key: filterMap id extracts the `some` values:
  -- (none^k ++ v.map some).filterMap id = v
  -- (none^k' ++ u.map some).filterMap id = u
  -- Since heq, these are equal, so v = u
  have hvu : v = u := by
    have h1 := filterMap_replicate_none_append_map_some k v
    have h2 := filterMap_replicate_none_append_map_some k' u
    rw [← h1, ← h2, heq]
  exact hvu ▸ hu

/-- L_x(L) ∈ ℒ(CA_rt (Option α)) implies L ∈ ℒ(CA_rt α).

Given a CA that accepts the padded lifted language L_x(L) in real-time,
we construct a CA that accepts L in real-time over the base alphabet.

**Proof outline** (8-stage pipeline):
1. C accepts L_x(L) = { none^k ++ w.map some | w ∈ L, k ≥ |w| }
2. Construct LxPipeline with C as C_orig and x = none
3. The pipeline transforms C through 8 stages to get C₇₀ + foldAdvice
4. `stage8_full_spec`: C₇₀.trace(w ⨂ foldAdvice w)(n-1) = C_orig accepts result
5. Since foldAdvice is RT-closed (`foldAdvice_rt_closed`), apply advice elimination
6. The result is a CA_rt over α accepting L

**Gap**: The pipeline assumes input has exact padding m = nextPow2(|w|), but
L_x allows m ≥ nextPow2(|w|). The minimal padding case suffices since
none^{m'} ++ w.map some ∈ L_x(L) for any m' ≥ m, and the RT CA accepts
based on the effective word w, not the padding length.

The full proof requires:
- Showing the pipeline handles the specific m = nextPow2(|w|) case
- Using advice elimination (`exists_CA_rt_of_rt_closed_advice`) -/
theorem lx_rt_implies_rt {α : Type} [Alphabet α] (L : Language α) :
    L_x L ∈ ℒ (CA_rt (Option α)) → L ∈ ℒ (CA_rt α) := by
  intro ⟨C, hC_rt, hC_L⟩
  -- C : tCellAutomaton (Option α) accepts L_x(L) in real-time
  -- hC_rt : C ∈ CA_rt (Option α)
  -- hC_L : L_x L = C.L

  -- Step 1: Build the pipeline over Option α with x = none
  let e : LxPipeline := { C_orig := C.toCellAutomaton, x := none }

  -- Step 2: Convert C₇₀ to an RT CA and eliminate advice
  let C₇₀_rt : CA_rt e.AdvicedInput := toRtCa e.C₇₀
  have h_adv_rt : e.foldAdvice.rt_closed := e.foldAdvice_rt_closed
  obtain ⟨C_elim, hC_elim_L⟩ := exists_CA_rt_of_rt_closed_advice C₇₀_rt e.foldAdvice h_adv_rt
  -- C_elim : CA_rt (Option α), C_elim.val.L = (C₇₀_rt.val + e.foldAdvice).L

  -- Step 3: Project C_elim down to alphabet α via map_embed some
  let C_final : CA_rt α :=
    ⟨C_elim.val.map_embed some, (c_map_embed_in_ca_rt_iff_c_in_ca_rt _ _).mpr C_elim.property⟩
  -- C_final accepts v : Word α iff v.map some ∈ C_elim.val.L

  -- Step 4: Show C_final.val.L = L using finite symmetric difference
  -- For |v| ≥ 9, we prove C_final agrees with L (via the pipeline chain).
  -- For |v| < 9, the disagreement set is finite since Alphabet α is Fintype.
  -- Then ca_rt_closed_finite_symmDiff gives L ∈ ℒ(CA_rt α).

  -- C_final.val.L ∈ ℒ(CA_rt α)
  have h_Cfinal_in : C_final.val.L ∈ ℒ (CA_rt α) :=
    ⟨C_final.val, C_final.property, rfl⟩

  -- For large words (|v| ≥ 9), C_final agrees with L
  have h_agree_large : ∀ v : Word α, v.length ≥ k_factor + 1 →
      (v ∈ L ↔ v ∈ C_final.val.L) := by
    intro v hv_len
    show v ∈ L ↔ v ∈ (C_elim.val.map_embed some).L
    rw [map_embed_L]
    let w := v.map some
    have hw_len : w.length ≥ k_factor + 1 := by simp [w]; exact hv_len
    have hstage8 := e.stage8_full_spec w hw_len

    -- Chain: v.map some ∈ C_elim.L ↔ ... ↔ v ∈ L
    have h1 : v.map some ∈ C_elim.val.L ↔ w ∈ (C₇₀_rt.val + e.foldAdvice).L := by
      constructor <;> intro hx
      · rw [hC_elim_L] at hx; exact hx
      · rw [hC_elim_L]; exact hx
    rw [h1]

    have h2 : w ∈ (C₇₀_rt.val + e.foldAdvice).L ↔
        e.C₇₀.trace (w ⨂ e.foldAdvice.f w) (e.n w - 1) = true := by
      simp only [tCellAutomatonWithAdvice.L, tCellAutomaton.accepts,
                 Advice.annotate]
      have h_ann_len : (w ⨂ e.foldAdvice.f w).length = w.length := by
        simp [advice_len]
      change (toRtCa e.C₇₀).val.toCellAutomaton.comp
        ⦋⟬w ⨂ e.foldAdvice.f w⟭⦌
        ((toRtCa e.C₇₀).val.t (w ⨂ e.foldAdvice.f w).length)
        ((toRtCa e.C₇₀).val.p (w ⨂ e.foldAdvice.f w).length) = true ↔ _
      simp only [toRtCa, h_ann_len, CellAutomaton.trace, CellAutomaton.comp,
                 CellAutomaton.project_config, Function.comp]

    have h3 : e.C₇₀.trace (w ⨂ e.foldAdvice.f w) (e.n w - 1) = true ↔
        (e.x_prefix w ++ w) ∈ C.L := by
      rw [show e.C₇₀.trace (w ⨂ e.foldAdvice.f w) (e.n w - 1) =
            e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 from hstage8]
      rw [CA_rt_L_iff (C := ⟨C, hC_rt⟩)]
      change e.C_orig.comp ⟬e.x_prefix w ++ w⟭ (e.m w + e.n w - 1) 0 = true ↔
          e.C_orig.comp ⟬e.x_prefix w ++ w⟭ ((e.x_prefix w ++ w).length - 1) 0 = true
      simp [LxPipeline.x_prefix, LxPipeline.m, LxPipeline.n, w]

    have h4 : (e.x_prefix w ++ w) ∈ C.L ↔ (e.x_prefix w ++ w) ∈ L_x L := by
      constructor <;> intro hx
      · have : (e.x_prefix w ++ w) ∈ DefinesLanguage.L C := hx
        rw [← hC_L] at this; exact this
      · have : (e.x_prefix w ++ w) ∈ DefinesLanguage.L C := by rw [← hC_L]; exact hx
        exact this

    have hw_vlen : w.length = v.length := by simp [w]
    have h5 : (e.x_prefix w ++ w) ∈ L_x L ↔ v ∈ L := by
      show List.replicate (nextPow2 w.length) none ++ v.map some ∈ L_x L ↔ v ∈ L
      rw [hw_vlen]
      exact ⟨fun h => mem_of_L_x_mem h, fun h => L_x_mem_of_mem h⟩

    rw [h2, h3, h4, h5]

  -- The symmetric difference C_final.val.L ∆ L only contains words of length < 9
  have h_symmDiff_finite : (symmDiff C_final.val.L L).Finite := by
    -- The set of all words of length < k_factor + 1 is finite
    let short_words : Finset (Word α) :=
      (Finset.range (k_factor + 1)).biUnion
        (fun n => (Finset.univ : Finset (Fin n → α)).image List.ofFn)
    -- The symm diff is a subset of short_words
    apply Set.Finite.subset short_words.finite_toSet
    intro w hw
    -- w ∈ symmDiff means L and C_final disagree on w
    -- Show w ∈ short_words, i.e., |w| < k_factor + 1
    simp only [short_words, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion,
               Set.mem_Iio, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
               true_and] at *
    -- Must have |w| < 9, otherwise h_agree_large gives contradiction
    refine ⟨w.length, ?_, fun i => w[i], List.ofFn_getElem w⟩
    by_contra h_ge
    push_neg at h_ge
    have h_iff := h_agree_large w h_ge
    simp only [symmDiff] at hw
    exact hw.elim (fun ⟨h1, h2⟩ => h2 (h_iff.mpr h1)) (fun ⟨h1, h2⟩ => h2 (h_iff.mp h1))

  exact ca_rt_closed_finite_symmDiff C_final.val.L L h_Cfinal_in h_symmDiff_finite

#print axioms lx_rt_implies_rt

end CellularAutomatas
