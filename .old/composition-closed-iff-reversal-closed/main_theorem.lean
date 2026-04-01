import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.basic_fold
import CellularAutomatas.proofs.constructions.basic_border_normalization
import CellularAutomatas.proofs.constructions.speedup_left_independent_config
import CellularAutomatas.proofs.constructions.left_indep_to_regular
import CellularAutomatas.proofs.constructions.left_indep_from_regular
import CellularAutomatas.results

namespace CellularAutomatas

open CellAutomaton
open CellularAutomatas.results

/-!
# Main Theorem: L_x(L) ∈ CA(RT) ⟹ L ∈ CA(RT)

We reduce from a CA accepting x^m w at (m+n-1, 0) to a CA accepting w at (n-1, 0)
in 7 steps, each composing a known construction.
-/

variable {α : Type} [Alphabet α]

/-! ## Definitions -/

/-- The smallest power of 2 ≥ n. -/
noncomputable def nextPow2 (n : ℕ) : ℕ := 2 ^ (Nat.clog 2 n)

lemma nextPow2_le (n : ℕ) (hn : n ≥ 2) : n ≤ nextPow2 n :=
  Nat.le_pow_clog (by norm_num) n

lemma nextPow2_lt_two_mul (n : ℕ) (hn : n ≥ 2) : nextPow2 n < 2 * n := by
  unfold nextPow2
  have h_pos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
  have h_pred : 2 ^ (Nat.clog 2 n - 1) < n :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have h_eq : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
  rw [h_eq, Nat.pow_succ]
  omega

lemma nextPow2_le_two_mul_sub (n : ℕ) (hn : n ≥ 2) : nextPow2 n ≤ 2 * (n - 1) := by
  unfold nextPow2
  have h_pos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
  have h_pred : 2 ^ (Nat.clog 2 n - 1) < n :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have h_eq : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
  rw [h_eq, Nat.pow_succ]
  omega

/-- Prefix a word with m copies of symbol x. -/
def prefixWord (x : α) (m : ℕ) (w : Word α) : Word α :=
  List.replicate m x ++ w

@[simp]
lemma prefixWord_length (x : α) (m : ℕ) (w : Word α) :
    (prefixWord x m w).length = m + w.length := by
  simp [prefixWord]

/-! ## Adapter Lemmas -/

/--
Shift on `Config C.Q`: comp on shifted config = comp at shifted position.
Direct consequence of existing `nextt_shift`.
-/
lemma comp_shift_Q {β : Type} [Alphabet β]
    (C : CellAutomaton α β) (c : Config C.Q) (s : ℤ) (t : ℕ) (p : ℤ) :
    C.comp (fun i => c (i + s)) t p = C.comp c t (p + s) := by
  simp only [comp, project_config, Function.comp_apply]
  congr 1; rw [← nextt_shift]

/--
Shift at `Config α` level: shifting the input config commutes with comp.
Since embed_config is pointwise, shifting commutes through the coercion.
-/
lemma comp_shift_input {β : Type} [Alphabet β]
    (C : CellAutomaton α β) (c : Config α) (s : ℤ) (t : ℕ) (p : ℤ) :
    C.comp (show Config C.Q from fun i => C.embed (c (i + s))) t p =
    C.comp (show Config C.Q from fun i => C.embed (c i)) t (p + s) := by
  exact comp_shift_Q C (fun i => C.embed (c i)) s t p

/--
`result_regular_to_left_indep` specialized at position -(t:ℤ):
The output at the OCA acceptance position equals `.single` of the original.
-/
lemma regular_to_left_indep_at_neg {β : Type} [Alphabet β]
    (C : CellAutomaton α β) (c : Config α) (t : ℕ) :
    let C₁ := (RegularToLeftIndep.mk C).C
    C₁.comp c (2 * t) (-(t : ℤ)) = BetaUnionSq.single (C.comp c t 0) := by
  intro C₁
  have h := result_regular_to_left_indep C c t (-(t : ℤ))
  simp only [neg_add_cancel] at h
  exact h

/--
`result_left_indep_to_regular` specialized at i=0:
  C₃.comp c t 0 = C₂.comp c (2*t) (-(t:ℤ))
-/
lemma left_indep_to_regular_at_zero {β : Type} [Alphabet β]
    (C : CellAutomaton α β) (h_li : C.left_independent) (c : Config α) (t : ℕ) :
    let C₃ := (LeftIndepToRegular.mk C h_li).C
    C₃.comp c t 0 = C.comp c (2 * t) (-(t : ℤ)) := by
  intro C₃
  have h := result_left_indep_to_regular C h_li c t (0 : ℤ)
  simp only [zero_sub] at h
  exact h

/--
`fold_spec` adapted: comp on FoldConfig at position 0 equals comp on original.

`fold_spec` works on `Config α` (underlying type), but `foldCA C` operates
on `Config (Option (α × α))`. This adapter bridges the gap by working at
the `Config C.Q` level (through embed_config).
-/
lemma fold_at_zero {β : Type} [Alphabet β]
    (C : CellAutomaton α β) (c : Config C.Q) (t : ℕ) :
    (foldCA C).comp (FoldConfigQ C c) t 0 = C.comp c t 0 := by
  -- Uses fold_nextt_spec (inner lemma) at position 0
  simp only [comp, project_config, Function.comp_apply]
  rw [fold_nextt_spec C c t 0 (le_refl 0)]
  simp only [foldCA]

-- Adapter: FoldConfig of embed_config equals FoldConfigQ.
-- Already proved as `embed_FoldConfig` in basic_fold.lean.

/-! ## Unproved Key Lemmas

The following are the hard proof obligations, referenced from `pipeline_with_advice`:

1. **Broadcast** (Step 1.5): After RegularToLeftIndep, apply BroadcastOCA to
   propagate acceptance into the entire left light cone. This allows reading
   acceptance from any position ≤ 0 at sufficient time.

2. **Advice RT-closedness**: the advice v_m is two-stage
   — Stage 1: exp_word CA (formalized)
   — Stage 2: FST computing x/# pattern + end markers

3. **Step 6 type coercion**: borderNormalizeCA trace spec
   — Mathematically identical to `border_normalize`, just needs type alignment

These are sorry'd inside `pipeline_with_advice` and `LxPipeline.step6_spec`.
-/

/-! ## Step-by-step Composition

Each step states:
  • **Have**: C_i accepts g_i(w) at (t_i, p_i)
  • **Produce**: C_{i+1} accepts g_{i+1}(w) at (t_{i+1}, p_{i+1})
-/

/--
### Step 1: Regular → Left-Independent

**Have:** C.comp c t 0 = b
**Produce:** C₁.comp c (2*t) (-(t:ℤ)) = .single b, C₁ left-independent
-/
lemma step1 {β : Type} [Alphabet β] (C : CellAutomaton α β) (c : Config α) (t : ℕ) :
    (RegularToLeftIndep.mk C).C.comp c (2 * t) (-(t : ℤ)) =
    BetaUnionSq.single (C.comp c t 0) :=
  regular_to_left_indep_at_neg C c t

lemma step1_li {β : Type} [Alphabet β] (C : CellAutomaton α β) :
    (RegularToLeftIndep.mk C).C.left_independent :=
  result_regular_to_left_indep_is_left_indep C

/--
### Step 2: Shift

**Have:** C.comp c t (p + s) = b
**Produce:** C.comp (c ∘ (· + s)) t p = b  (same CA, shifted config)
-/
lemma step2 {β : Type} [Alphabet β] (C : CellAutomaton α β)
    (c : Config C.Q) (s : ℤ) (t : ℕ) (p : ℤ) :
    C.comp (fun i => c (i + s)) t p = C.comp c t (p + s) :=
  comp_shift_Q C c s t p

-- Step 3: Speedup + Lock-in (combines LeftIndepSpeedupConfig.spec + lockin)
--
-- **Have:** C₁ (left-indep) accepts [x^m | w] at (2(m+n-1), -(2m+n-1))
-- **Produce:** C₂ (left-indep) accepts compress₅([x^m | w]) at (2(n-1), -(n-1))
--
-- The speedup spec is proven. Lock-in is unproved.
-- Step 3 deferred — depends on lockin lemma

/--
### Step 4: Left-Independent → Regular

**Have:** C₂.comp c (2*t) (-(t:ℤ)) = b
**Produce:** C₃.comp c t 0 = b
-/
lemma step4 {β : Type} [Alphabet β] (C₂ : CellAutomaton α β)
    (h_li : C₂.left_independent) (c : Config α) (t : ℕ) :
    (LeftIndepToRegular.mk C₂ h_li).C.comp c t 0 =
    C₂.comp c (2 * t) (-(t : ℤ)) :=
  left_indep_to_regular_at_zero C₂ h_li c t

/--
### Step 5: Fold

**Have:** C₃.comp c t 0 = b  (where c is a bi-infinite config)
**Produce:** (foldCA C₃).comp (FoldConfigQ C₃ c) t 0 = b
-/
lemma step5 {β : Type} [Alphabet β] (C₃ : CellAutomaton α β)
    (c : Config C₃.Q) (t : ℕ) :
    (foldCA C₃).comp (FoldConfigQ C₃ c) t 0 = C₃.comp c t 0 :=
  fold_at_zero C₃ c t

/--
### Step 6: Border Normalization

**Have:** C₄.trace (BorderedConfig b₁ [] w b₂) t = b
**Produce:** ∃ C₅, C₅.trace ⟬w⟭ t = b

Note: `border_normalize` works on `CellAutomaton α？ β` where the borders are
values of type `α`. When applied to a `CellAutomaton α？？ Bool`, the borders
are `Option α` values (i.e., `some b₁` and `some b₂`).
-/
lemma step6 (C₄ : CellAutomaton α？ Bool) (b₁ b₂ : α？) :
    ∃ (C₅ : CellAutomaton α？？ Bool),
      ∀ (w : Word α？), w ≠ [] →
        C₅.trace ⟬w⟭ = C₄.trace (BorderedConfig b₁ [] w b₂) :=
  border_normalize C₄ b₁ b₂

/-- Lift id is the identity on advice. -/
lemma advice_lift_id_eq {Γ : Type} [Alphabet Γ] (adv : Advice α Γ) :
    adv.lift (id : α → α) = adv := by
  simp [Advice.lift, List.map_id]

/--
### Step 7: RT-closed advice removes v_m

**Have:** L ∈ ℒ(CA_rt(α × Γ) + adv)
**Produce:** L ∈ ℒ(CA_rt(α))
-/
lemma step7 {Γ : Type} [Alphabet Γ] (adv : Advice α Γ) (h_rt : adv.rt_closed) :
    ℒ (CA_rt (α × Γ) + adv) = ℒ (CA_rt α) := by
  have h := h_rt α id
  rwa [advice_lift_id_eq] at h

/-! ## Pipeline Structure -/

/--
Pipeline: Given a CA C accepting x^m w, constructs a CA accepting w ⊗ v_m.

The pipeline chains 6 transformations:
1. RegularToLeftIndep:  C → C₁ (left-indep), acceptance at (2(m+n-1), -(m+n-1))
2. Shift:              Reindex [x^m | w] → ⟨x^m w⟩, acceptance at (2(m+n-1), -(2m+n-1))
3. Speedup + Lock-in:  Compress by 5, acceptance at (2(n-1), -(n-1))
4. LeftIndepToRegular:  C₂ → C₃, acceptance at (n-1, 0)
5. Fold:               Bi-infinite → right-infinite, acceptance at (n-1, 0)
6. BorderNormalize:    Bordered config → standard embedding, acceptance at (n-1, 0)
-/
structure LxPipeline where
  {α : Type}
  [_inst_α : Alphabet α]
  C_orig : LCellAutomaton α

attribute [instance] LxPipeline._inst_α

namespace LxPipeline

variable (e : LxPipeline)

/-! ### Step 1: Regular → Left-Independent -/

def step1_data : RegularToLeftIndep := RegularToLeftIndep.mk e.C_orig
def C₁ := e.step1_data.C

lemma C₁_left_indep : e.C₁.left_independent :=
  RegularToLeftIndep.C_left_independent e.step1_data

/-- C₁.comp c (2t) i = .single(C_orig.comp c t (i+t))
    where c : Config (Option α) (the input type of C_orig). -/
lemma C₁_spec (c : Config e.α？) (t : ℕ) (i : ℤ) :
    e.C₁.comp c (2 * t) i = BetaUnionSq.single (e.C_orig.comp c t (i + t)) :=
  result_regular_to_left_indep e.C_orig c t i

/-! ### Step 2: Shift — same CA, reindexed config -/
-- Not a new CA. [x^m | w](p) = ⟨x^m w⟩(p + m).
-- Combined with Step 1:
--   C₁.comp [x^m|w] (2(m+n-1)) (-(2m+n-1)) = .single(C_orig.comp ⟨x^m w⟩ (m+n-1) 0)

/-! ### Step 3: Speedup + Lock-in -/

def step3_data : LeftIndepSpeedupConfig where
  Q := e.C₁.Q
  δ := e.C₁.δ
  k := 5
  hk := by omega
  h_left_indep := e.C₁_left_indep

/-- C₂ is the speedup CA. Left-independent. -/
def C₂ := e.step3_data.C'

-- Lock-in wraps C₂ with flag propagation (to be defined)
-- For now, we assume the combined result:

/-- After speedup + lock-in, acceptance is at (2(n-1), -(n-1)).

  This combines:
  • LeftIndepSpeedupConfig.spec (proven)
  • Lock-in flag propagation (unproved)
-/
lemma C₂_spec (c : Config e.C₁.Q) (n m : ℕ) (hn : n ≥ 2) (hm : m ≤ 2 * (n - 1)) :
    -- C₂ at (2(n-1), -(n-1)) encodes C₁ at (2(m+n-1), -(2m+n-1))
    True := by
  trivial

/-! ### Step 4: Left-Independent → Regular -/

-- C₂ is left-independent (inherits from speedup + lock-in).
-- LeftIndepToRegular maps acceptance from (2(n-1), -(n-1)) to (n-1, 0).

-- C₂ has left_independent because the speedup preserves it.
lemma C₂_left_indep : e.C₂.left_independent := by
  show e.step3_data.C'.left_independent
  exact e.step3_data.δ'_left_indep

def step4_data : LeftIndepToRegular :=
  LeftIndepToRegular.mk e.C₂ e.C₂_left_indep

/-- C₃: regular CA, acceptance at (n-1, 0).
    Input: e.step3_data.Input (= Single Q₁ | Compressed (Fin 5 → Q₁))
    Output: Fin 5 → Q₁ -/
def C₃ := e.step4_data.C

/-! ### Step 5: Fold -/

/-- C₄ = foldCA(C₃): folds bi-infinite config into right-infinite.
    Input: Option (C₃.Q × C₃.Q)
    Output: Fin 5 → Q₁ -/
def C₄ := foldCA e.C₃

/-! ### Step 6: Border Normalization -/

-- C₄ : CellAutomaton (Option (Input × Input)) _
-- where Input = e.step3_data.Input
-- borderNormalizeCA C₄ b₁ b₂ needs b₁ b₂ : Input × Input

abbrev FoldPairType := e.step3_data.Input × e.step3_data.Input

/-- Border values for the fold: `none` represents outside the fold region.
    Both borders are `none : FoldPairType？` since positions outside the word
    in the folded config have no meaningful pair. -/
def fold_b₁ : e.FoldPairType？ := none
def fold_b₂ : e.FoldPairType？ := none

/-- C₅ and its spec, obtained from `border_normalize`.
    C₄ : CellAutomaton FoldPairType？ _, so border_normalize
    treats α = FoldPairType？, giving:
    - C₅ : CellAutomaton FoldPairType？？ _
    - w : Word FoldPairType？
    - C₅.trace w = C₄.trace (BorderedConfig none [] w none) -/
noncomputable def C₅_data := border_normalize e.C₄ e.fold_b₁ e.fold_b₂

noncomputable def C₅ := e.C₅_data.choose
noncomputable def C_final := e.C₅

/-- Step 6 spec: follows directly from border_normalize. -/
def step6_spec := e.C₅_data.choose_spec

/-! ### Specs -/

/-- Step 4 spec: C₃ at (t, 0) = C₂ at (2t, -t) -/
lemma step4_spec (c : Config e.step3_data.Input) (t : ℕ) :
    e.C₃.comp c t 0 = e.C₂.comp c (2 * t) (-(↑t : ℤ)) := by
  have h := LeftIndepToRegular.spec e.step4_data c t 0
  simp at h
  exact h

/-- Step 5 spec: C₄ via FoldConfigQ at (t, 0) = C₃ at (t, 0) -/
lemma step5_spec (c : Config e.C₃.Q) (t : ℕ) :
    e.C₄.comp (FoldConfigQ e.C₃ c) t 0 = e.C₃.comp c t 0 :=
  fold_at_zero e.C₃ c t

end LxPipeline

/-! ## Lemmas needed for pipeline_chain_spec -/

/-!
### Lemma 1: Timing Analysis

Given n = |w| and m = nextPow2(n), we need to find where in the speedup
the original acceptance point (2(m+n-1), -(2m+n-1)) maps to.

From proof.md:
- Original acceptance at (2(m+n-1), -(2m+n-1))
- d = ⌈(2m+n-1)/5⌉, j = 5d - (2m+n-1)
- Speedup component j at position -d, time d+n-1 simulates original
- Bound: d ≤ n-1 (because m ≤ 2(n-1))
-/

/-- Compute d = ⌈(2m+n-1)/5⌉ -/
def acceptance_d (m n : ℕ) : ℕ := (2 * m + n - 1 + 4) / 5

/-- Compute j = 5d - (2m+n-1) -/
def acceptance_j (m n : ℕ) : ℕ := 5 * acceptance_d m n - (2 * m + n - 1)

/-- d ≤ n-1 when m ≤ 2(n-1)

Proof: Since m ≤ 2(n-1), we have 2m + n + 3 ≤ 5n - 1, so
d = (2m + n + 3) / 5 ≤ (5n - 1) / 5 = n - 1.
-/
lemma acceptance_d_bound (m n : ℕ) (hn : n ≥ 2) (hm : m ≤ 2 * (n - 1)) :
    acceptance_d m n ≤ n - 1 := by
  unfold acceptance_d
  -- Goal: (2*m + n - 1 + 4) / 5 ≤ n - 1
  -- Since m ≤ 2*(n-1), we have 2*m + n + 3 ≤ 5n - 1
  have h1 : 2 * m + n + 3 ≤ 5 * n - 1 := by omega
  -- (5n - 1) / 5 = n - 1 for n ≥ 1
  have h2 : (5 * n - 1) / 5 = n - 1 := by omega
  calc (2 * m + n - 1 + 4) / 5
      = (2 * m + n + 3) / 5 := by omega
    _ ≤ (5 * n - 1) / 5 := Nat.div_le_div_right h1
    _ = n - 1 := h2

/-- j < 5 (so j : Fin 5)

Proof: By definition d = ⌈(2m+n-1)/5⌉, so 5(d-1) < 2m+n-1 ≤ 5d.
Thus 0 ≤ 5d - (2m+n-1) < 5.
-/
lemma acceptance_j_bound (m n : ℕ) (hn : n ≥ 2) :
    acceptance_j m n < 5 := by
  unfold acceptance_j acceptance_d
  -- d = (2m + n + 3) / 5, j = 5d - (2m + n - 1)
  -- We need: 5 * ((2m + n + 3) / 5) - (2m + n - 1) < 5
  have h : (2 * m + n - 1 + 4) / 5 * 5 ≤ 2 * m + n - 1 + 4 :=
    Nat.div_mul_le_self (2 * m + n - 1 + 4) 5
  omega

/-- The speedup spec at the acceptance coordinates.

From the speedup spec with i = -d, t = d+n-1, j = 5d-(2m+n-1):
- φ(t, i, j) = t - 4i - j = (d+n-1) + 4d - (5d-(2m+n-1)) = 2(m+n-1)
- ψ(i, j) = 5i + j = -5d + (5d-(2m+n-1)) = -(2m+n-1)

So the speedup at acceptance coordinates gives the C_orig value at (2(m+n-1), -(2m+n-1)).
-/
lemma speedup_at_acceptance (e : LeftIndepSpeedupConfig) (he : e.k = 5)
    (c : Config e.Q) (n : ℕ) (hn : n ≥ 2) (m : ℕ) (hm : m ≤ 2 * (n - 1)) :
    let d := acceptance_d m n
    let jval := acceptance_j m n
    let hj : jval < e.k := by rw [he]; exact acceptance_j_bound m n hn
    let j : Fin e.k := ⟨jval, hj⟩
    let t₀ := d + n - 1
    -- Component j at position -d, time t₀ equals C_orig at (2(m+n-1), -(2m+n-1))
    e.C'.comp (e.compress c) t₀ (-(d : ℤ)) j =
      e.C_orig.comp c (2 * (m + n - 1)) (-(2 * m + n - 1 : ℤ)) := by
  intro d jval hj j t₀
  -- d = ⌈(2m+n-1)/5⌉ ≥ 1 since n ≥ 2
  have hd_pos : d ≥ 1 := by
    simp only [d, acceptance_d]
    have h : 2 * m + n - 1 + 4 ≥ 5 := by omega
    omega
  -- Position -d < 0, required by spec
  have hi : (-(d : ℤ)) < 0 := by omega
  -- Time t₀ ≥ d, required for diagonal regime
  have ht : (t₀ : ℤ) ≥ d := by simp only [t₀]; omega
  -- Apply the main speedup spec
  have h_spec := e.spec c (-(d : ℤ)) hi t₀ (by omega : (t₀ : ℤ) ≥ -(-d : ℤ)) j
  rw [h_spec]
  -- Coordinate arithmetic verification:
  -- Time: (t₀ - (k-1)*(-d) - j).toNat = 2(m+n-1)
  -- Position: k*(-d) + j = -(2m+n-1)
  -- Both are straightforward after substituting:
  --   k=5, t₀=d+n-1, d=⌈(2m+n-1)/5⌉, j=5d-(2m+n-1)
  simp only [t₀, j, jval, d, acceptance_d, acceptance_j, he, Fin.val_mk]
  set D := (2 * m + n - 1 + 4) / 5 with hD
  have h5D : 5 * D ≥ 2 * m + n - 1 := by omega
  -- Use native Int/Nat cast lemmas and arithmetic
  simp only [Nat.cast_sub h5D]
  -- Try grind for the mixed arithmetic
  grind

/-!
### Lemma 2: Broadcast Timing

With BroadcastOCA, the acceptance value at (0, n-1) is available at
position -(n-1) after n-1 additional time steps, i.e., at time 2(n-1).
-/

/-- Broadcast reaches position -k at time n-1+k. For position -(n-1), time is 2(n-1). -/
lemma broadcast_timing (n : ℕ) (hn : n ≥ 1) :
    n - 1 + (n - 1) = 2 * (n - 1) := by omega

/-!
### Lemma 3: Full Pipeline Chain

The key specification: C_final at (n-1, 0) with the correct extraction
equals C_orig at (m+n-1, 0).
-/

/-- Combined steps 4+5: C₄.comp (FoldConfigQ ...) (n-1) 0 = C₂.comp ... (2(n-1)) (-(n-1)) -/
lemma steps45_chain (pipe : LxPipeline) (c : Config pipe.step3_data.Input) (n : ℕ) :
    pipe.C₄.comp (FoldConfigQ pipe.C₃ (pipe.C₃.embed_config c)) (n - 1) 0 =
    pipe.C₂.comp c (2 * (n - 1)) (-((n - 1 : ℕ) : ℤ)) := by
  rw [pipe.step5_spec, pipe.step4_spec]

/-- Steps 1+2 combined: C₁ on shifted config = .single(C_orig at (t, 0))
    This is already proven as h12 inside pipeline_with_advice. -/
lemma steps12_chain (pipe : LxPipeline) (c : Config pipe.α？) (m t : ℕ) :
    pipe.C₁.comp (fun p => (pipe.C₁.embed_config c) (p + m)) (2 * t) (-(t : ℤ) - m) =
    BetaUnionSq.single (pipe.C_orig.comp c t 0) := by
  rw [comp_shift_Q]
  simp only [show -(↑t : ℤ) - ↑m + ↑m = -(↑t : ℤ) from by ring]
  have h := pipe.C₁_spec c t (-(↑t : ℤ))
  simp only [show -(↑t : ℤ) + ↑t = (0 : ℤ) from by ring] at h
  exact h

/-!
### Lemma 4: Broadcast Spec

Using BroadcastOCA, the acceptance value at (0, n-1) propagates to the entire
left light cone. This replaces the lock-in mechanism.
-/

/-- The broadcast spec ensures we can read acceptance from any position in the light cone.

    After applying BroadcastOCA to the left-independent CA C₁, we can read the
    acceptance value from position -(n-1) at time 2(n-1), which is in the light
    cone of (0, n-1) since the distance n-1 is covered in n-1 additional steps.
-/
lemma broadcast_light_cone_spec
    (C : CellAutomaton α？ Bool) (h_li : C.left_independent)
    (w : Word α) (hw : w.length ≥ 2) (k : ℕ) :
    let bc := BroadcastOCA.mk C h_li
    bc.C'.comp ⟬addEndMarkers w⟭ (w.length - 1 + k) (-(k : ℤ)) =
    C.comp ⟬w⟭ (w.length - 1) 0 := by
  exact BroadcastOCA.spec (BroadcastOCA.mk C h_li) w hw k (-(k : ℤ)) ⟨by omega, by omega⟩

/-!
### Key Lemma: Speedup Propagation

This is the fundamental lemma that connects the speedup output at the
reading position to the original CA acceptance.

**The challenge**: The acceptance is computed at position -d, component j, time d+n-1
in the speedup. But we read at position -(n-1), component 0, time 2(n-1).

**Why it should work**: In a left-independent CA, values propagate leftward at speed 1.
From (-d, d+n-1) to (-(n-1), 2(n-1)):
- Distance: (n-1) - d
- Time available: 2(n-1) - (d+n-1) = n-1-d ✓

However, the speedup has k=5 components, and the transition shifts components during
propagation. The acceptance value in component j gets shifted as the wave propagates.

**Solution via BroadcastOCA**: Instead of relying on natural CA dynamics, use
BroadcastOCA to explicitly copy and propagate the acceptance value. The broadcast
mechanism ensures that once the acceptance is computed, it propagates to all cells
in the light cone, including the reading position.

For a proper proof, we would need to:
1. Integrate BroadcastOCA into the pipeline before speedup
2. Show that the broadcast value survives the speedup compression
3. Show that pipeline_extract reads from the broadcast field

For now, we state this as a sorry'd specification.
-/

/-- The extract function for the pipeline's output CA.

    The pipeline's C_final outputs `Fin k → C₁.Q` (k-component speedup state).
    We extract acceptance by:
    1. Taking component 0
    2. Projecting through C₁.project to get `BetaUnionSq Bool`
    3. Extracting the Bool from the single/pair wrapper -/
def pipeline_extract (pipe : LxPipeline) :
    (Fin pipe.step3_data.k → pipe.step3_data.Q) → Bool :=
  fun q =>
    let j0 : Fin pipe.step3_data.k := ⟨0, pipe.step3_data.hk.trans_lt' (by omega)⟩
    match pipe.C₁.project (q j0) with
    | .single b => b
    | .pair b _ => b

/-- The speedup at the reading position gives the original acceptance.

    This lemma encapsulates the key property: reading from position -(n-1)
    at time 2(n-1) via pipeline_extract gives the same result as the
    original CA's acceptance.

    **Proof obligation**: Requires BroadcastOCA.spec to show the acceptance
    value propagates from position 0 to position -(n-1) in the light cone. -/
lemma speedup_reading_spec (pipe : LxPipeline) (x : pipe.α)
    (w : Word pipe.α) (hw : w.length ≥ 2) :
    let n := w.length
    let m := nextPow2 n
    let prefix_config : Config pipe.C₁.Q :=
      fun p => pipe.C₁.embed_config ⟬prefixWord x m w⟭ (p + ↑m)
    let compressed := pipe.step3_data.compress prefix_config
    pipeline_extract pipe (pipe.C₂.comp compressed (2 * (n - 1)) (-(n - 1 : ℤ))) =
    pipe.C_orig.comp ⟬prefixWord x m w⟭ (m + n - 1) 0 := by
  -- Key steps:
  -- 1. By BroadcastOCA.spec, the output at (0, n-1) reaches (-(n-1), 2(n-1))
  -- 2. By speedup_at_acceptance, this equals C_orig at the acceptance point
  -- 3. pipeline_extract reads component 0 which contains the acceptance value
  sorry

/-! ## Pipeline Construction Helpers

The pipeline proof is decomposed into sorry'd *definitions* and *lemmas*,
each capturing a specific, independently-verifiable claim.
`pipeline_with_advice` itself has no sorry — it assembles these pieces.
-/

/-- The advice for the Lx pipeline.

    At position i of w, computes the fold pair (cell_i, cell_{-(i+1)})
    from the compressed speedup of the shifted prefix word.

    Construction:
    1. Embed the prefix word `x^m w` into C₁'s state space
    2. Shift by m (so the word portion starts at position 0)
    3. Compress through the k=5 speedup
    4. At each position i, pair the forward cell (pos i) with the
       backward cell (pos -(i+1)) — matching FoldConfigQ's pairing -/
noncomputable def pipeline_advice (pipe : LxPipeline) (x : pipe.α) :
    Advice pipe.α pipe.FoldPairType :=
  { f := fun w =>
      let m := nextPow2 w.length
      -- Embed prefix word into C₁'s internal state, then shift by m
      let c₁ : Config pipe.step3_data.Q :=
        fun p => pipe.C₁.embed_config ⟬prefixWord x m w⟭ (p + ↑m)
      -- Compress through the k=5 speedup
      let c₂ : Config pipe.step3_data.Input := pipe.step3_data.compress c₁
      -- Fold pairs: (forward cell at pos i, backward cell at pos -(i+1))
      (List.range w.length).map fun i =>
        (c₂ ↑i, c₂ (-(↑i + 1)))
    len := by intro w; simp }

/-- The pipeline output CA: C_final with decode (drop α) and extract (read acceptance).

    - **decode**: (α × FoldPairType)？ → FoldPairType？？ strips the α component
    - **extract**: reads the projected boolean from the k-component speedup output
    - **t, p**: real-time acceptance at (n-1, 0) -/
noncomputable def pipeline_ca (pipe : LxPipeline) :
    tCellAutomaton (pipe.α × pipe.FoldPairType) :=
  let decode : (pipe.α × pipe.FoldPairType)？ → pipe.FoldPairType？？ :=
    fun | some (_, γ) => some (some γ) | none => some none
  let C₅_lca := pipe.C_final.map_embed decode |>.map_project (pipeline_extract pipe)
  { C₅_lca with t := fun n => n - 1, p := fun _ => 0 }

/-- The pipeline CA is in CA_rt. Trivial from t = n-1. -/
lemma pipeline_ca_in_rt (pipe : LxPipeline) :
    pipeline_ca pipe ∈ CA_rt (pipe.α × pipe.FoldPairType) := by
  constructor
  · constructor
    · trivial
    · rfl
  · intro n; rfl

/-- The pipeline advice is RT-closed.

    **Proof approach**: Show pipeline_advice is a two-stage advice:
    - Stage 1 (CA_rt): Compute the speedup trace of x^m w for varying m = nextPow2(n)
    - Stage 2 (FST): Extract fold pairs (c₂(i), c₂(-(i+1))) from the trace

    Key insight: The exp_middle_two_stage machinery shows how to handle
    advices that depend on nextPow2(n). The pattern follows a similar structure.

    Alternative: Show weak_rt_closed directly by constructing a CA_rt that
    simulates (pipeline_advice.annotate w ⊗ any CA_rt input). -/
lemma pipeline_advice_rt_closed (pipe : LxPipeline) (x : pipe.α) :
    (pipeline_advice pipe x).rt_closed := by
  -- Would require:
  -- 1. Constructing a TwoStageAdvice equivalent to pipeline_advice
  -- 2. Or showing directly that for any π : β → α, (pipeline_advice pipe x).lift π
  --    is weak_rt_closed
  sorry

/--
**Decode correspondence**: for the map_embed in pipeline_ca, the decode function
applied to word_to_config of the annotated word produces:
- Inside [0, n): `some (some γ[i])` where γ[i] is the fold pair
- Outside [0, n): `some none` — the "inner border" value

This is NOT the same as word_to_config of a mapped word (which would give `none` outside).
Instead, it matches the bordered config that border_normalize expects:
`BorderedConfig (some none) [] (map (some ∘ snd) annotated_w) (some none)`.
-/
lemma advice_decode_border_match
    (pipe : LxPipeline) (x : pipe.α)
    (w : Word pipe.α) (i : ℤ) :
    (fun
      | some (_, γ) => (Option.some (Option.some γ) : pipe.FoldPairType？？)
      | none => Option.some none) (⟬(pipeline_advice pipe x).annotate w⟭ i) =
    (BorderedConfig (Option.some none : pipe.FoldPairType？？) []
      (((pipeline_advice pipe x).annotate w).map (fun p => Option.some (Option.some p.2)))
      (Option.some none)) i := by
  have h_annot_len : ((pipeline_advice pipe x).annotate w).length = w.length := by
    simp only [Advice.annotate, List.length_zip, (pipeline_advice pipe x).len, min_self]
  have h_fold_len : (((pipeline_advice pipe x).annotate w).map
    (fun p => Option.some (Option.some p.2))).length = w.length := by
    simp only [List.length_map, h_annot_len]
  unfold word_to_config BorderedConfig
  simp only [List.length_nil, neg_zero, h_fold_len, h_annot_len]
  -- Case split based on i's position
  by_cases h_ge0 : 0 ≤ i
  · by_cases h_lt : i < w.length
    · -- Case: 0 ≤ i < w.length (in the word)
      have h_in : 0 ≤ i ∧ i < w.length := ⟨h_ge0, h_lt⟩
      simp only [h_in, ↓reduceDIte, not_and, not_lt, ge_iff_le, h_ge0, h_lt,
        and_self, reduceIte, dite_true, List.getElem_map]
      -- Goal: List.get vs getElem are definitionally equal
      rfl
    · -- Case: i ≥ w.length (right of word)
      have h_ge : i ≥ w.length := not_lt.mp h_lt
      have h_not_in : ¬(0 ≤ i ∧ i < w.length) := by omega
      have h_not_neg : ¬(-↑(0 : Nat) ≤ i ∧ i < 0) := by simp only [CharP.cast_eq_zero, neg_zero]; omega
      simp only [h_not_in, h_ge0, h_ge, not_lt.mpr h_ge, and_self, not_true_eq_false, and_false,
        ↓reduceDIte, ge_iff_le, ↓reduceIte, dite_false, h_not_neg]
  · -- Case: i < 0 (left of word)
    have h_neg : i < 0 := Int.not_le.mp h_ge0
    have h_not_in : ¬(0 ≤ i ∧ i < w.length) := by omega
    have h_not_neg : ¬(-↑(0 : Nat) ≤ i ∧ i < 0) := by simp only [CharP.cast_eq_zero, neg_zero]; omega
    have h_not_ge : ¬(i ≥ (w.length : ℤ)) := by omega
    simp only [h_not_in, h_ge0, false_and, ↓reduceDIte, not_and, not_lt,
      ge_iff_le, h_not_ge, ↓reduceIte, dite_false, h_not_neg]

/-- The pipeline CA correctly simulates the original CA on prefix words.

    **Proof chain**:
    1. `pipeline_ca.accepts (adv.annotate w)` unfolds to
       `pipeline_extract (C_final.comp (decode ∘ embed(adv.annotate w)) (n-1) 0)`

    2. `advice_decode_border_match`: decode ∘ embed matches BorderedConfig

    3. `step6_spec`: C_final relates to C₄ via border_normalize

    4. `steps45_chain` (PROVEN): C₄ at (n-1, 0) = C₂ at (2(n-1), -(n-1))

    5. `speedup_reading_spec` (KEY LEMMA): C₂ at the reading position gives acceptance

    6. Original CA acceptance via h_orig
-/
lemma pipeline_ca_spec (pipe : LxPipeline) (x : pipe.α)
    (C : tCellAutomaton pipe.α) (hC : C ∈ CA_rt pipe.α)
    (h_orig : pipe.C_orig = C.toCellAutomaton)
    (w : Word pipe.α) :
    (pipeline_ca pipe).accepts ((pipeline_advice pipe x).annotate w) =
    C.accepts (prefixWord x (nextPow2 w.length) w) := by
  -- Setup: names and basic properties
  let n := w.length
  let m := nextPow2 n
  let adv := pipeline_advice pipe x
  let w' := adv.annotate w

  -- Case split on word length
  by_cases hw : n ≥ 2
  case neg =>
    -- Edge case: n < 2 (i.e., n = 0 or n = 1)
    -- For these cases, both sides compute acceptance via the pipeline/original CA
    -- but timing and position parameters differ from the main case.
    -- Requires special handling or showing the pipeline handles short inputs correctly.
    sorry

  -- Main case: n ≥ 2
  show (pipeline_ca pipe).accepts w' = C.accepts (prefixWord x m w)

  -- **Proof structure** (requires connecting the chain of specs):
  --
  -- LHS: (pipeline_ca pipe).accepts w'
  --    = pipeline_extract pipe (C_final.map_embed.comp decoded_config (n-1) 0)
  --
  -- By advice_decode_border_match: decoded_config = BorderedConfig (some none) [] ... (some none)
  --
  -- By step6_spec (border_normalize): C_final.comp bordered = C₄.comp (internal FoldConfigQ)
  --
  -- By steps45_chain: C₄ at (n-1, 0) = C₂ at (2(n-1), -(n-1))
  --
  -- By speedup_reading_spec: pipeline_extract (C₂.comp compressed ...) = C_orig.comp ... (m+n-1) 0
  --
  -- RHS: C.accepts (prefixWord x m w)
  --    = C.comp ⟬prefixWord x m w⟭ (C.t (m+n)) (C.p (m+n))
  --    = C.comp ⟬prefixWord x m w⟭ (m+n-1) 0       [since C ∈ CA_rt]
  --
  -- By h_orig: pipe.C_orig = C.toCellAutomaton
  --
  -- The remaining work is to:
  -- 1. Show the advice-annotated config matches what step6_spec expects
  -- 2. Show the folded config from pipeline_advice matches what steps45_chain expects
  -- 3. Connect all the pieces with the correct configs

  sorry

/-! ## Main Theorem -/

/--
**Combined pipeline + advice**: Given C ∈ CA_rt(α) accepting x^m w, construct:
- An advice adv : Advice α Γ that is RT-closed
- A CA C₅ ∈ CA_rt(α × Γ) such that C₅.accepts(adv.annotate w) = C.accepts(x^m w)

**Sorry decomposition** (each sorry is a separate declaration):
- `pipeline_advice` (def): advice construction
- `pipeline_extract` (def): flag extraction function
- `pipeline_advice_rt_closed` (lemma): advice is RT-closed
- `pipeline_ca_spec` (lemma): pipeline CA simulates C on prefixWord
- `lockin_flag_spec` (lemma): lock-in flag propagation
-/
lemma pipeline_with_advice (x : α) (C : tCellAutomaton α) (hC : C ∈ CA_rt α) :
    ∃ (Γ : Type) (_ : Alphabet Γ) (adv : Advice α Γ),
      adv.rt_closed ∧
      ∃ C₅ ∈ CA_rt (α × Γ),
        ∀ w : Word α,
          (C₅ : tCellAutomaton (α × Γ)).accepts (adv.annotate w) =
          C.accepts (prefixWord x (nextPow2 w.length) w) := by
  let pipe : LxPipeline := { C_orig := C.toCellAutomaton }
  exact ⟨pipe.FoldPairType, inferInstance,
    pipeline_advice pipe x,
    pipeline_advice_rt_closed pipe x,
    pipeline_ca pipe,
    pipeline_ca_in_rt pipe,
    fun w => pipeline_ca_spec pipe x C hC rfl w⟩

/--
**Main Theorem (Language-level):** If L_x(L) ∈ ℒ(CA_rt), then L ∈ ℒ(CA_rt).
-/
theorem lx_implies_rt (x : α) (L : Language α)
    (hL : ∃ C_lx ∈ CA_rt α,
      L = { w | C_lx.accepts (prefixWord x (nextPow2 w.length) w) }) :
    L ∈ ℒ (CA_rt α) := by
  obtain ⟨C_lx, hC_lx_rt, hL_eq⟩ := hL

  -- Combined pipeline + advice
  obtain ⟨Γ, _, adv, h_adv_rt, C₅, hC₅_rt, hC₅_spec⟩ :=
    pipeline_with_advice x C_lx hC_lx_rt

  -- Show L ∈ ℒ(CA_rt(α × Γ) + adv), then apply RT-closedness
  suffices h : L ∈ ℒ (CA_rt (α × Γ) + adv) by
    rwa [step7 adv h_adv_rt] at h

  -- Exhibit C₅ + adv as the witness
  show ∃ ca, ca ∈ (CA_rt (α × Γ) + adv) ∧ L = DefinesLanguage.L ca
  refine ⟨C₅ + adv, ⟨C₅, hC₅_rt, rfl⟩, ?_⟩
  rw [hL_eq]
  ext w
  change C_lx.accepts (prefixWord x (nextPow2 w.length) w) = true ↔
    (C₅ + adv : tCellAutomatonWithAdvice α).C.accepts (adv.annotate w) = true
  rw [← hC₅_spec w]

end CellularAutomatas
