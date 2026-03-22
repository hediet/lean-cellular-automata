import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.speedup_left_independent

namespace CellularAutomatas

/-!
# Generalized Left-Independent Speedup (Config-Level)

Generalization of `LeftIndepSpeedupQuiescent` from word-based to config-based.
Instead of assuming a word embedded into a border-quiescent configuration,
we take an arbitrary configuration and compress it spatially on the left (i < 0),
leaving the right (i ≥ 0) uncompressed.

## Key difference from `LeftIndepSpeedupQuiescent`:
- No quiescent border assumption
- No word — works with arbitrary `Config Q`
- Two compression regimes:
  - **spatial** (outside light cone, `t < -i`): all k components at same orig time `k·t`
  - **diagonal** (inside light cone, `t ≥ -i`): components staggered by 1 orig step

## Diagram (k=2):

```
  COMPRESSED:     i'=-3        i'=-2        i'=-1          0   1
  t'=0 :         [spat]       [spat]       [spat]          a   b
  t'=1 :         [spat]       [spat]       (diag)          a₁  ·
  t'=2 :         [spat]       (diag)       (diag)          a₂  ·
  t'=3 :         (diag)       (diag)       (diag)           ·  ·
```
-/

/-!
## Structure and state space
-/

structure LeftIndepSpeedupConfig where
  {Q : Type}
  [_inst_Q : Alphabet Q]
  δ : Q → Q → Q → Q
  k : ℕ
  hk : k ≥ 2
  h_left_indep : ∀ (q1 q2 q3 q1'), δ q1 q2 q3 = δ q1' q2 q3

attribute [instance] LeftIndepSpeedupConfig._inst_Q

namespace LeftIndepSpeedupConfig

variable (e : LeftIndepSpeedupConfig)

lemma hk1 : e.k ≥ 1 := Nat.one_le_of_lt e.hk

-- Since δ is left-independent, we define a two-argument version
def δ₂ (b c : e.Q) : e.Q := e.δ default b c

lemma δ₂_eq (a b c : e.Q) : e.δ a b c = e.δ₂ b c := by
  show e.δ a b c = e.δ default b c
  exact e.h_left_indep a b c default

/-!
## State space Q' with three constructors
-/

inductive Q' where
  | single (q : e.Q)              -- uncompressed cell (i ≥ 0)
  | spatial (w : Fin e.k → e.Q)   -- compressed, all components at same orig time
  | diagonal (w : Fin e.k → e.Q)  -- compressed, components staggered in time
deriving DecidableEq

instance : Fintype e.Q' :=
  Fintype.ofEquiv (e.Q ⊕ (Fin e.k → e.Q) ⊕ (Fin e.k → e.Q))
    { toFun := fun
        | .inl q => Q'.single q
        | .inr (.inl w) => Q'.spatial w
        | .inr (.inr w) => Q'.diagonal w
      invFun := fun
        | Q'.single q => .inl q
        | Q'.spatial w => .inr (.inl w)
        | Q'.diagonal w => .inr (.inr w)
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr _) => rfl
      right_inv := fun
        | Q'.single _ => rfl
        | Q'.spatial _ => rfl
        | Q'.diagonal _ => rfl }

instance : Inhabited e.Q' := ⟨Q'.single default⟩

instance : Alphabet e.Q' := {}

/-!
## Extracting values from Q'
-/

-- Extract the "effective single" state (component 0 for compressed states)
def asQ : e.Q' → e.Q
  | Q'.single q => q
  | Q'.spatial w => w ⟨0, by have := e.hk; omega⟩
  | Q'.diagonal w => w ⟨0, by have := e.hk; omega⟩

@[simp] lemma asQ_single (q : e.Q) : e.asQ (Q'.single q) = q := rfl
@[simp] lemma asQ_spatial (w : Fin e.k → e.Q) :
    e.asQ (Q'.spatial w) = w ⟨0, by have := e.hk; omega⟩ := rfl
@[simp] lemma asQ_diagonal (w : Fin e.k → e.Q) :
    e.asQ (Q'.diagonal w) = w ⟨0, by have := e.hk; omega⟩ := rfl

/-!
## Fold functions

Three fold operations corresponding to the three transition types:
- `fold_diag`: diagonal → diagonal (existing chain from `LeftIndepSpeedupQuiescent`)
- `fold_spatial`: spatial + spatial → spatial (full k-step triangle)
- `fold_switch`: spatial + single/diagonal → diagonal (regime transition)
-/

-- fold_diag: chain δ₂ from right to left (same as existing `fold`)
-- Given center tuple w and right-neighbor's component-0 value q:
--   result[k-1] = δ₂(w[k-1], q)
--   result[j]   = δ₂(w[j], result[j+1])   for j < k-1
def foldDiagAux : (n : ℕ) → (Fin n → e.Q) → e.Q → (Fin n → e.Q)
  | 0, _, _ => Fin.elim0
  | n + 1, w, q =>
      let r := e.δ₂ (w (Fin.last n)) q
      Fin.snoc (foldDiagAux n (Fin.init w) r) r

def foldDiag := e.foldDiagAux e.k

-- foldDiagAux at last position
private lemma foldDiagAux_last (n : ℕ) (hn : n ≥ 1) (w : Fin n → e.Q) (q : e.Q) :
    e.foldDiagAux n w q ⟨n - 1, by omega⟩ = e.δ₂ (w ⟨n - 1, by omega⟩) q := by
  cases n with
  | zero => omega
  | succ n =>
    unfold foldDiagAux
    simp only [Nat.succ_sub_one, Fin.snoc]
    split_ifs with h
    · omega
    · rfl

-- foldDiagAux at index j < n-1
private lemma foldDiagAux_step (n : ℕ) (w : Fin n → e.Q) (q : e.Q) (j : Fin n)
    (hj : j.val + 1 < n) :
    e.foldDiagAux n w q j = e.δ₂ (w j) (e.foldDiagAux n w q ⟨j.val + 1, hj⟩) := by
  induction n generalizing q with
  | zero => exact Fin.elim0 j
  | succ n ihn =>
    have hj_lt_n : j.val < n := by omega
    have h_j : e.foldDiagAux (n + 1) w q j =
        e.foldDiagAux n (Fin.init w) (e.δ₂ (w (Fin.last n)) q) ⟨j.val, hj_lt_n⟩ := by
      simp [foldDiagAux, Fin.snoc, dif_pos hj_lt_n]; rfl
    rw [h_j]
    by_cases h : j.val + 1 < n
    · have h_j1 : e.foldDiagAux (n + 1) w q ⟨j.val + 1, hj⟩ =
          e.foldDiagAux n (Fin.init w) (e.δ₂ (w (Fin.last n)) q) ⟨j.val + 1, h⟩ := by
        simp [foldDiagAux, Fin.snoc, dif_pos h]
      rw [h_j1, ihn _ _ ⟨j.val, hj_lt_n⟩ h]
      congr 1
    · have h_last : e.foldDiagAux (n + 1) w q ⟨j.val + 1, hj⟩ =
          e.δ₂ (w (Fin.last n)) q := by
        simp [foldDiagAux, Fin.snoc, show ¬(↑(⟨j.val + 1, hj⟩ : Fin (n + 1)) < n) from by omega]
      rw [h_last]
      have hj_val : j.val = n - 1 := by omega
      have hj_eq : (⟨j.val, hj_lt_n⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
        ext; exact hj_val
      rw [hj_eq, e.foldDiagAux_last n (by omega) (Fin.init w) (e.δ₂ (w (Fin.last n)) q)]
      simp only [δ₂, Fin.init]
      congr 2
      exact Fin.ext hj_val.symm

-- fold_diag at last component: δ₂(w[k-1], q)
lemma foldDiag_last (w : Fin e.k → e.Q) (q : e.Q) :
    e.foldDiag w q ⟨e.k - 1, by have := e.hk; omega⟩ = e.δ₂ (w ⟨e.k - 1, by have := e.hk; omega⟩) q :=
  e.foldDiagAux_last e.k e.hk1 w q

-- fold_diag at component j < k-1: δ₂(w[j], foldDiag[j+1])
lemma foldDiag_step (w : Fin e.k → e.Q) (q : e.Q) (j : Fin e.k) (hj : j.val + 1 < e.k) :
    e.foldDiag w q j = e.δ₂ (w j) (e.foldDiag w q ⟨j.val + 1, hj⟩) :=
  e.foldDiagAux_step e.k w q j hj

/-!
## Spatial fold: full k-step triangle simulation

For `spatial + spatial → spatial`, we simulate k original steps.
The center tuple has components at positions {k·i', ..., k·i'+k-1} all at time T.
The right neighbor has components at positions {k·(i'+1), ..., k·(i'+1)+k-1} all at time T.
Together they form a window of 2k original cells, and we simulate k steps of δ₂ on them.

For k=2, center=(a₀,a₁), right=(a₂,a₃):
  Level 0: a₀  a₁  a₂  a₃         (time T)
  Level 1: δ₂(a₀,a₁) δ₂(a₁,a₂) δ₂(a₂,a₃)   (time T+1)
  Level 2: δ₂(L1[0],L1[1])  δ₂(L1[1],L1[2])  (time T+2) ← result
-/

-- Simulate one step of a left-independent CA on a finite window of n cells.
-- Given n cells [c₀, ..., c_{n-1}], returns n-1 cells [δ₂(c₀,c₁), ..., δ₂(c_{n-2}, c_{n-1})].
def stepWindow : {n : ℕ} → (Fin n → e.Q) → (Fin (n - 1) → e.Q)
  | 0, _ => Fin.elim0
  | 1, _ => Fin.elim0
  | n + 2, cs => fun j => e.δ₂ (cs ⟨j.val, by omega⟩) (cs ⟨j.val + 1, by omega⟩)

-- Apply stepWindow k times to a window of 2k cells, yielding k cells.
-- This computes k steps of the left-independent CA on a local window.
def foldSpatialAux : (steps : ℕ) → (width : ℕ) → (Fin width → e.Q) → (Fin (width - steps) → e.Q)
  | 0, _, cs => by rwa [Nat.sub_zero]
  | n + 1, width, cs =>
      have h : width - 1 - n = width - (n + 1) := by omega
      h ▸ foldSpatialAux n (width - 1) (e.stepWindow cs)

-- Full spatial fold: given center (Fin k → Q) and right (Fin k → Q),
-- concatenate them into a 2k window and simulate k steps.
def concatTuples (center right : Fin e.k → e.Q) : Fin (2 * e.k) → e.Q :=
  fun j => if h : j.val < e.k then center ⟨j.val, h⟩
           else right ⟨j.val - e.k, by omega⟩

-- The spatial fold: result is k cells after k steps on 2k-cell window
def foldSpatial (center right : Fin e.k → e.Q) : Fin e.k → e.Q :=
  have h : 2 * e.k - e.k = e.k := by omega
  h ▸ e.foldSpatialAux e.k (2 * e.k) (e.concatTuples center right)

/-!
## Switch fold: spatial → diagonal transition

When a spatial cell first meets a diagonal/single neighbor on the right,
it must transition from "all at same time T" to "staggered times".
Component j advances by (k - j) steps, so component 0 is at T+k, component k-1 is at T+1.

For k=2, center=(a,b), q=asQ(right) (at time T, same as center):
  result[1] = δ₂(b, q)                     -- 1 step:  T+1
  result[0] = δ₂(δ₂(a, b), result[1])      -- 2 steps: T+2
-/

-- Build a window [center[0], ..., center[k-1], q] of size k+1
def switchWindow (center : Fin e.k → e.Q) (q : e.Q) : Fin (e.k + 1) → e.Q :=
  fun j => if h : j.val < e.k then center ⟨j.val, h⟩ else q

-- Triangle diagonal extraction: given a window of (n+1) cells, apply stepWindow
-- repeatedly and extract the rightmost new element at each level.
-- result[n-1] = stepWindow(row₀)[n-1]  (the last element of row 1)
-- result[n-2] = stepWindow(row₁)[n-2]  (second-to-last of row 2)
-- result[j]   = row_{n-j}[j]           (column j of row n-j)
def foldSwitchAux : (n : ℕ) → (Fin (n + 1) → e.Q) → (Fin n → e.Q)
  | 0, _ => Fin.elim0
  | n + 1, row =>
      let stepped : Fin (n + 1) → e.Q :=
        have h : n + 2 - 1 = n + 1 := by omega
        h ▸ e.stepWindow row
      let diag_elem : e.Q := stepped ⟨n, by omega⟩
      Fin.snoc (foldSwitchAux n stepped) diag_elem

-- The switch fold: extract the diagonal of the triangle on [center[0], ..., center[k-1], q].
-- Component j ends up at row (k-j) of the triangle, column j.
-- For k=2: result = (δ₂(δ₂(a,b), δ₂(b,q)), δ₂(b,q))
def foldSwitch (center : Fin e.k → e.Q) (q : e.Q) : Fin e.k → e.Q :=
  e.foldSwitchAux e.k (e.switchWindow center q)

/-!
## Transition function δ'
-/

def δ' (_ b c : e.Q') : e.Q' :=
  match b, c with
  | Q'.single q_b, _ => Q'.single (e.δ₂ q_b (e.asQ c))
  | Q'.diagonal w_b, _ => Q'.diagonal (e.foldDiag w_b (e.asQ c))
  | Q'.spatial w_b, Q'.spatial w_c => Q'.spatial (e.foldSpatial w_b w_c)
  | Q'.spatial w_b, _ => Q'.diagonal (e.foldSwitch w_b (e.asQ c))

-- δ' is left-independent
lemma δ'_left_indep : ∀ (a b c a' : e.Q'), e.δ' a b c = e.δ' a' b c := by
  intros a b c a'
  simp only [δ']

/-!
## Compressed initial configuration
-/

-- Compress a configuration: spatial tuples on the left, singles on the right
def compress (c : Config e.Q) : Config e.Q' :=
  fun i => if i ≥ 0 then Q'.single (c i)
           else Q'.spatial (fun j => c (e.k * i + j))

/-!
## Position and time mappings
-/

def ψ (i : ℤ) (j : Fin e.k) : ℤ := e.k * i + j

-- Time mapping: piecewise depending on light-cone
def τ (t : ℕ) (i : ℤ) (j : Fin e.k) : ℕ :=
  if (t : ℤ) ≥ -i then (t - (e.k - 1 : ℕ) * i - j).toNat  -- diagonal regime
  else e.k * t                                                 -- spatial regime

/-!
## Invariant: what we want to prove by induction on t

For `i < 0`, at compressed time `t`:

  if t < -i:
    nextt(compress c, t, i) = spatial(j ↦ nextt(c, k·t, k·i+j))
  if t ≥ -i:
    nextt(compress c, t, i) = diagonal(j ↦ nextt(c, t-(k-1)·i-j, k·i+j))

For `i ≥ 0`:
    nextt(compress c, t, i) = single(nextt(c, t, i))
-/

-- The compressed CA (without embed/project — we work at the Q level)
-- For the generalized version, we don't need embed/project.
-- We define it as a raw transition system.
noncomputable def C' : CellAutomaton e.Q (Fin e.k → e.Q) := {
  Q := e.Q'
  δ := e.δ'
  embed := fun q => Q'.single q   -- identity embedding for raw Q
  project := fun
    | Q'.single q => fun _ => q
    | Q'.spatial w => w
    | Q'.diagonal w => w
}

-- Simp lemmas for C' transitions
@[simp] lemma C'_δ_single (a : e.Q') (q : e.Q) (c : e.Q') :
    e.C'.δ a (Q'.single q) c = Q'.single (e.δ₂ q (e.asQ c)) := rfl

@[simp] lemma C'_δ_diagonal (a : e.Q') (w : Fin e.k → e.Q) (c : e.Q') :
    e.C'.δ a (Q'.diagonal w) c = Q'.diagonal (e.foldDiag w (e.asQ c)) := rfl

@[simp] lemma C'_δ_spatial_spatial (a : e.Q') (w_b w_c : Fin e.k → e.Q) :
    e.C'.δ a (Q'.spatial w_b) (Q'.spatial w_c) = Q'.spatial (e.foldSpatial w_b w_c) := rfl

@[simp] lemma C'_δ_spatial_single (a : e.Q') (w_b : Fin e.k → e.Q) (q : e.Q) :
    e.C'.δ a (Q'.spatial w_b) (Q'.single q) = Q'.diagonal (e.foldSwitch w_b q) := rfl

@[simp] lemma C'_δ_spatial_diagonal (a : e.Q') (w_b w_c : Fin e.k → e.Q) :
    e.C'.δ a (Q'.spatial w_b) (Q'.diagonal w_c) =
    Q'.diagonal (e.foldSwitch w_b (w_c ⟨0, by have := e.hk; omega⟩)) := rfl

/-!
## Main theorem

The specification relates the compressed CA's evolution to the original CA's evolution.
-/

-- Helper: build the original CA from the stored δ
noncomputable def C_orig : CellAutomaton e.Q e.Q := {
  Q := e.Q
  δ := e.δ
  embed := id
  project := id
}

-- Invariant for non-negative positions
theorem spec_nonneg (c : Config e.Q) (i : ℤ) (hi : i ≥ 0) (t : ℕ) :
    e.C'.nextt (e.compress c) t i = Q'.single (e.C_orig.nextt c t i) := by
  induction t generalizing i with
  | zero =>
    show e.compress c i = Q'.single (c i)
    simp only [compress, if_pos hi]
  | succ t iht =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    rw [iht i hi, iht (i + 1) (by omega)]
    -- Goal: δ'(_, single(nextt c t i), single(nextt c t (i+1))) = single(δ(nextt c t (i-1), ...))
    simp only [C'_δ_single, asQ_single]
    show Q'.single (e.δ₂ _ _) = Q'.single (e.δ _ _ _)
    congr 1
    exact (e.δ₂_eq _ _ _).symm

/-!
## Helper lemmas for left-independent CA evolution
-/

-- Evaluating a cast function at a Fin index
private lemma cast_fin_fun_apply {α : Type} {a b : ℕ} (h : a = b) (f : Fin a → α) (j : Fin b) :
    (h ▸ f) j = f ⟨j.val, h ▸ j.isLt⟩ := by subst h; rfl

-- One step of a left-independent CA only depends on center and right neighbor
private lemma nextt_succ_left_indep (c : Config e.Q) (t : ℕ) (p : ℤ) :
    e.C_orig.nextt c (t + 1) p = e.δ₂ (e.C_orig.nextt c t p) (e.C_orig.nextt c t (p + 1)) := by
  simp only [CellAutomaton.nextt_succ, CellAutomaton.next, C_orig]
  exact e.δ₂_eq _ _ _

-- stepWindow on a window of size ≥ 2 computes δ₂ of consecutive entries
private lemma stepWindow_apply_eq {n : ℕ} (hn : n ≥ 2) (cs : Fin n → e.Q) (j : Fin (n - 1)) :
    e.stepWindow cs j = e.δ₂ (cs ⟨j.val, by omega⟩) (cs ⟨j.val + 1, by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rfl

-- stepWindow on a "correct window" at time T gives a correct window at time T+1
private lemma stepWindow_nextt (c : Config e.Q) (T : ℕ) (P : ℤ) (n : ℕ) (hn : n ≥ 2)
    (w : Fin n → e.Q) (hw : ∀ j : Fin n, w j = e.C_orig.nextt c T (P + (j.val : ℤ))) :
    ∀ j : Fin (n - 1), e.stepWindow w j = e.C_orig.nextt c (T + 1) (P + (j.val : ℤ)) := by
  intro j
  rw [e.stepWindow_apply_eq hn, hw, hw, e.nextt_succ_left_indep]
  congr 1 ; push_cast ; ring_nf

-- foldSpatialAux iterated on a correct window gives time-advanced cells
private lemma foldSpatialAux_correct (c : Config e.Q) (T : ℕ) (P : ℤ)
    (steps width : ℕ) (hw : width ≥ steps + 1)
    (w : Fin width → e.Q)
    (h_w : ∀ j : Fin width, w j = e.C_orig.nextt c T (P + (j.val : ℤ)))
    (j_val : ℕ) (hj : j_val < width - steps) :
    e.foldSpatialAux steps width w ⟨j_val, hj⟩ = e.C_orig.nextt c (T + steps) (P + (j_val : ℤ)) := by
  induction steps generalizing width T w with
  | zero =>
    simp only [foldSpatialAux, Nat.add_zero]
    exact h_w ⟨j_val, by omega⟩
  | succ n ih =>
    -- Unfold one level: foldSpatialAux (n+1) = h ▸ foldSpatialAux n (width-1) (stepWindow w)
    show ((_ : width - 1 - n = width - (n + 1)) ▸
          e.foldSpatialAux n (width - 1) (e.stepWindow w)) ⟨j_val, hj⟩ = _
    rw [cast_fin_fun_apply]
    -- stepWindow gives a correct window at time T+1
    have h_sw : ∀ j' : Fin (width - 1),
        e.stepWindow w j' = e.C_orig.nextt c (T + 1) (P + (j'.val : ℤ)) :=
      e.stepWindow_nextt c T P width (by omega) w h_w
    -- Apply IH
    have h_ih := ih (T + 1) (width - 1) (by omega) (e.stepWindow w) h_sw (by omega)
    have h_arith : T + 1 + n = T + (n + 1) := by omega
    rw [h_arith] at h_ih; exact h_ih

-- concatTuples represents consecutive cells
private lemma concatTuples_correct (c : Config e.Q) (T : ℕ) (P : ℤ)
    (center right : Fin e.k → e.Q)
    (hc : ∀ j : Fin e.k, center j = e.C_orig.nextt c T (P + (j.val : ℤ)))
    (hr : ∀ j : Fin e.k, right j = e.C_orig.nextt c T (P + e.k + (j.val : ℤ))) :
    ∀ j : Fin (2 * e.k),
      e.concatTuples center right j = e.C_orig.nextt c T (P + (j.val : ℤ)) := by
  intro j
  simp only [concatTuples]
  split_ifs with h
  · exact hc ⟨j.val, h⟩
  · rw [hr]; congr 1; push_cast; omega

-- foldSpatial simulates k steps of the original CA on a 2k-cell window
private lemma foldSpatial_correct (c : Config e.Q) (T : ℕ) (P : ℤ)
    (center right : Fin e.k → e.Q)
    (hc : ∀ j : Fin e.k, center j = e.C_orig.nextt c T (P + (j.val : ℤ)))
    (hr : ∀ j : Fin e.k, right j = e.C_orig.nextt c T (P + e.k + (j.val : ℤ))) :
    ∀ j : Fin e.k,
      e.foldSpatial center right j = e.C_orig.nextt c (T + e.k) (P + (j.val : ℤ)) := by
  intro j
  unfold foldSpatial
  rw [cast_fin_fun_apply]
  have h_concat := e.concatTuples_correct c T P center right hc hr
  have hk := e.hk
  exact e.foldSpatialAux_correct c T P e.k (2 * e.k) (by omega)
    (e.concatTuples center right) h_concat j.val (by have := j.isLt; omega)

-- switchWindow represents consecutive cells
private lemma switchWindow_correct (c : Config e.Q) (T : ℕ) (P : ℤ)
    (center : Fin e.k → e.Q) (q : e.Q)
    (hc : ∀ j : Fin e.k, center j = e.C_orig.nextt c T (P + (j.val : ℤ)))
    (hq : q = e.C_orig.nextt c T (P + e.k)) :
    ∀ j : Fin (e.k + 1),
      e.switchWindow center q j = e.C_orig.nextt c T (P + (j.val : ℤ)) := by
  intro j
  simp only [switchWindow]
  split_ifs with h
  · exact hc ⟨j.val, h⟩
  · rw [hq]; congr 1; have := j.isLt; omega

-- foldSwitchAux extracts the diagonal of the triangle
private lemma foldSwitchAux_correct (c : Config e.Q) (T : ℕ) (P : ℤ) (n : ℕ)
    (row : Fin (n + 1) → e.Q)
    (h_row : ∀ j : Fin (n + 1), row j = e.C_orig.nextt c T (P + (j.val : ℤ)))
    (j_val : ℕ) (hj : j_val < n) :
    e.foldSwitchAux n row ⟨j_val, hj⟩ =
    e.C_orig.nextt c (T + n - j_val) (P + (j_val : ℤ)) := by
  induction n generalizing T with
  | zero => omega
  | succ m ih =>
    -- foldSwitchAux (m+1) row = snoc(foldSwitchAux m stepped, diag_elem)
    simp only [foldSwitchAux]
    -- The stepped function from the definition is definitionally stepWindow row
    -- since m + 2 - 1 = m + 1 definitionally
    have h_stepped : ∀ j' : Fin (m + 1),
        ((show m + 2 - 1 = m + 1 from by omega) ▸ e.stepWindow row) j' =
        e.C_orig.nextt c (T + 1) (P + (j'.val : ℤ)) := by
      intro j'
      -- m + 2 - 1 = m + 1 definitionally, so the cast is identity
      change e.stepWindow row j' = _
      exact e.stepWindow_nextt c T P (m + 2) (by omega) row h_row j'
    -- Split on j_val < m or j_val = m using Fin.snoc lemmas
    by_cases h_lt : j_val < m
    · -- j_val < m: inner recursion
      have h_eq : (⟨j_val, hj⟩ : Fin (m + 1)) = Fin.castSucc ⟨j_val, h_lt⟩ := Fin.ext rfl
      rw [h_eq, Fin.snoc_castSucc]
      have h_ih := ih (T + 1) _ h_stepped h_lt
      have h_arith : T + 1 + m - j_val = T + (m + 1) - j_val := by omega
      rw [h_arith] at h_ih; exact h_ih
    · -- j_val = m: last element (diagonal element)
      have hj_eq : j_val = m := by omega
      have h_eq : (⟨j_val, hj⟩ : Fin (m + 1)) = Fin.last m := Fin.ext hj_eq
      rw [h_eq, Fin.snoc_last, show j_val = m from hj_eq,
          show T + (m + 1) - m = T + 1 from by omega]
      exact h_stepped ⟨m, by omega⟩

-- foldSwitch extracts diagonal of the triangle on [center[0], ..., center[k-1], q]
private lemma foldSwitch_correct (c : Config e.Q) (T : ℕ) (P : ℤ)
    (center : Fin e.k → e.Q) (q : e.Q)
    (hc : ∀ j : Fin e.k, center j = e.C_orig.nextt c T (P + (j.val : ℤ)))
    (hq : q = e.C_orig.nextt c T (P + e.k)) :
    ∀ j : Fin e.k,
      e.foldSwitch center q j = e.C_orig.nextt c (T + e.k - j.val) (P + (j.val : ℤ)) := by
  intro j
  unfold foldSwitch
  exact e.foldSwitchAux_correct c T P e.k (e.switchWindow center q)
    (e.switchWindow_correct c T P center q hc hq) j.val j.isLt

/-!
## Negative position structural lemma
-/

-- At negative positions, the state is always spatial or diagonal
private lemma neg_is_spatial_or_diagonal (c : Config e.Q) (i : ℤ) (hi : i < 0) (t : ℕ) :
    (∃ w, e.C'.nextt (e.compress c) t i = Q'.spatial w) ∨
    (∃ w, e.C'.nextt (e.compress c) t i = Q'.diagonal w) := by
  induction t with
  | zero =>
    left
    exact ⟨fun j => c (e.k * i + ↑↑j),
      by simp only [CellAutomaton.nextt_zero, compress, show ¬(i ≥ 0) from by omega, ite_false]⟩
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    rcases ih with ⟨w, hw⟩ | ⟨w, hw⟩
    · -- center is spatial
      rw [hw]
      rcases (e.C'.nextt (e.compress c) t (i + 1)) with q' | w_c | w_c
      · right; exact ⟨_, rfl⟩   -- spatial + single → diagonal
      · left; exact ⟨_, rfl⟩    -- spatial + spatial → spatial
      · right; exact ⟨_, rfl⟩   -- spatial + diagonal → diagonal
    · -- center is diagonal
      rw [hw]; right; exact ⟨_, rfl⟩  -- diagonal + anything → diagonal

/-!
## Main theorems
-/

-- Invariant for negative positions, spatial regime
theorem spec_spatial (c : Config e.Q) (i : ℤ) (hi : i < 0) (t : ℕ) (ht : (t : ℤ) < -i) :
    e.C'.nextt (e.compress c) t i =
    Q'.spatial (fun j => e.C_orig.nextt c (e.k * t) (e.k * i + j)) := by
  induction t generalizing i with
  | zero =>
    simp only [CellAutomaton.nextt_zero, Nat.mul_zero, CellAutomaton.nextt_zero]
    simp only [compress, show ¬(i ≥ 0) from by omega, ite_false]
  | succ t iht =>
    -- (t+1 : ℤ) < -i means t < -(i+1), so i+1 < 0 (since i ≤ -2)
    have hi1 : i + 1 < 0 := by omega
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- By IH: center at i and right at i+1 are both spatial
    rw [iht i hi (by omega), iht (i + 1) hi1 (by omega)]
    -- δ'(_, spatial, spatial) = spatial(foldSpatial ...)
    simp only [C'_δ_spatial_spatial]
    apply congrArg Q'.spatial; ext j
    -- foldSpatial correctness with T = k*t, P = k*i
    have h_fold := e.foldSpatial_correct c (e.k * t) (e.k * i)
      (fun j => e.C_orig.nextt c (e.k * t) (e.k * i + ↑↑j))
      (fun j => e.C_orig.nextt c (e.k * t) (e.k * (i + 1) + ↑↑j))
      (fun _ => rfl)
      (fun _ => by push_cast; ring_nf)
      j
    simp only [show e.k * t + e.k = e.k * (t + 1) from by ring] at h_fold; exact h_fold

-- Helper: the φ-like time mapping for this construction
private def φ (t : ℕ) (i : ℤ) (j : Fin e.k) : ℤ := t - (e.k - 1 : ℕ) * i - j
private def φ_nat (t : ℕ) (i : ℤ) (j : Fin e.k) (_hi : i < 0) : ℕ :=
  (e.φ t i j).toNat

private lemma φ_nonneg (t : ℕ) (i : ℤ) (hi : i < 0) (ht : (t : ℤ) ≥ -i) (j : Fin e.k) :
    0 ≤ e.φ t i j := by
  simp only [φ]
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  rw [hk1]
  have hj : (j : ℤ) ≤ e.k - 1 := by have := j.isLt; omega
  nlinarith

private lemma φ_succ_last (t : ℕ) (i : ℤ) :
    e.φ (t + 1) i ⟨e.k - 1, by have := e.hk; omega⟩ = e.φ t i ⟨e.k - 1, by have := e.hk; omega⟩ + 1 := by
  simp only [φ]; push_cast; ring

private lemma φ_step (t : ℕ) (i : ℤ) (m : ℕ) (hm : m + 1 < e.k) :
    e.φ (t + 1) i ⟨m + 1, hm⟩ = e.φ t i ⟨m, by omega⟩ := by
  simp only [φ]; push_cast; ring

private lemma φ_succ (t : ℕ) (i : ℤ) (m : ℕ) (hm : m < e.k) :
    e.φ (t + 1) i ⟨m, hm⟩ = e.φ t i ⟨m, hm⟩ + 1 := by
  simp only [φ]; push_cast; ring

-- The ψ-like position mapping
private lemma ψ_step (i : ℤ) (m : ℕ) (_hm : m + 1 < e.k) :
    e.k * i + (↑(m + 1) : ℤ) = e.k * i + ↑m + 1 := by push_cast; ring

-- q (right neighbor's component 0) position/time for the steady-state diagonal case
-- When right is at i+1 < 0: q = nextt c (φ(t,i+1,0).toNat) (k*(i+1))
-- φ(t,i+1,0) = t - (k-1)*(i+1) = t - (k-1)*i - (k-1)  = φ(t,i,k-1)
private lemma φ_right_zero_eq (t : ℕ) (i : ℤ) :
    e.φ t (i + 1) ⟨0, by have := e.hk; omega⟩ = e.φ t i ⟨e.k - 1, by have := e.hk; omega⟩ := by
  simp only [φ]
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  simp only [hk1, Nat.cast_zero, sub_zero]; ring

private lemma ψ_right_zero_eq (i : ℤ) :
    e.k * (i + 1) + (0 : ℤ) = e.k * i + ↑(e.k - 1 : ℕ) + 1 := by
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  rw [hk1]; ring

-- The key inner step for the diagonal regime: uses foldDiag
-- Shows that foldDiag(w, q)[m] = nextt c (φ(t+1,i,m).toNat) (k*i+m)
-- given w[j] = nextt c (φ(t,i,j).toNat) (k*i+j) and q = nextt c (φ(t,i,k-1).toNat) (k*i+(k-1)+1)
private lemma foldDiag_diagonal_step (c : Config e.Q) (i : ℤ) (hi : i < 0) (t : ℕ) (ht : (t : ℤ) ≥ -i)
    (w : Fin e.k → e.Q) (q : e.Q)
    (hw : ∀ j : Fin e.k, w j = e.C_orig.nextt c (e.φ t i j).toNat (e.k * i + j))
    (hq : q = e.C_orig.nextt c (e.φ t i ⟨e.k - 1, by have := e.hk; omega⟩).toNat (e.k * i + ↑(e.k - 1 : ℕ) + 1)) :
    ∀ m : ℕ, (hm : m < e.k) →
      e.foldDiag w q ⟨m, hm⟩ = e.C_orig.nextt c (e.φ (t + 1) i ⟨m, hm⟩).toNat (e.k * i + ↑m) := by
  intro m hm
  -- We need: φ(t,i,j).toNat ≥ 0 for various j
  have h_φ_nn : ∀ j : Fin e.k, 0 ≤ e.φ t i j := fun j => e.φ_nonneg t i hi ht j
  induction hd : e.k - 1 - m generalizing m with
  | zero =>
    -- m = k-1 (base case of descending induction)
    have hm_eq : m = e.k - 1 := by omega
    subst hm_eq
    rw [e.foldDiag_last, hw, hq]
    -- Goal: δ₂(nextt c T₁ P₁, nextt c T₁ (P₁+1)) = nextt c (T₁+1) P₁
    -- where T₁ = φ(t,i,k-1).toNat and P₁ = k*i+(k-1)
    -- This is exactly nextt_succ_left_indep applied backwards
    have h_succ : (e.φ (t + 1) i ⟨e.k - 1, hm⟩).toNat = (e.φ t i ⟨e.k - 1, hm⟩).toNat + 1 := by
      have h1 : e.φ (t + 1) i ⟨e.k - 1, hm⟩ = e.φ t i ⟨e.k - 1, hm⟩ + 1 := by simp [φ]; ring
      rw [h1, Int.toNat_add (h_φ_nn _) (by omega)]; simp
    rw [h_succ, ← e.nextt_succ_left_indep]
  | succ d ih_inner =>
    -- m < k-1 (inductive step)
    have hm_lt : m + 1 < e.k := by omega
    rw [e.foldDiag_step w q ⟨m, hm⟩ hm_lt]
    rw [ih_inner (m + 1) hm_lt (by omega)]
    rw [hw ⟨m, hm⟩]
    -- Goal: δ₂(nextt c (φ t i m).toNat (k*i+m), nextt c (φ(t+1) i (m+1)).toNat (k*i+m+1))
    --     = nextt c (φ(t+1) i m).toNat (k*i+m)
    -- Key identities:
    --   φ(t+1, i, m+1) = φ(t, i, m)  [time step]
    --   φ(t+1, i, m) = φ(t, i, m) + 1  [succ]
    have h_step : (e.φ (t + 1) i ⟨m + 1, hm_lt⟩).toNat = (e.φ t i ⟨m, hm⟩).toNat := by
      exact congrArg Int.toNat (e.φ_step t i m hm_lt)
    have h_pos : (↑e.k * i + (↑(m + 1) : ℤ)) = ↑e.k * i + ↑m + 1 := by push_cast; ring
    have h_succ : (e.φ (t + 1) i ⟨m, hm⟩).toNat = (e.φ t i ⟨m, hm⟩).toNat + 1 := by
      have h1 : e.φ (t + 1) i ⟨m, hm⟩ = e.φ t i ⟨m, hm⟩ + 1 := by simp [φ]; ring
      rw [h1, Int.toNat_add (h_φ_nn _) (by omega)]; simp
    rw [h_step, h_pos, h_succ, ← e.nextt_succ_left_indep]

-- Invariant for negative positions, diagonal regime
theorem spec_diagonal (c : Config e.Q) (i : ℤ) (hi : i < 0) (t : ℕ) (ht : (t : ℤ) ≥ -i) :
    e.C'.nextt (e.compress c) t i =
    Q'.diagonal (fun j => e.C_orig.nextt c ((t - (e.k - 1 : ℕ) * i - j).toNat) (e.k * i + j)) := by
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  induction t generalizing i with
  | zero => omega
  | succ t iht =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    by_cases ht_prev : (t : ℤ) < -i
    · ---- SWITCH CASE ----
      rw [e.spec_spatial c i hi t ht_prev]
      by_cases hi1 : i + 1 < 0
      · -- Right i+1 is negative, becomes diagonal
        have ht1 : (t : ℤ) ≥ -(i + 1) := by omega
        rw [iht (i + 1) hi1 ht1]
        simp only [C'_δ_spatial_diagonal]
        congr 1; ext m
        have ht_eq : (t : ℤ) = -(i + 1) := by omega
        -- Prove the right[0] argument equals nextt c (k*t) (k*i+k)
        have hq : e.C_orig.nextt c
            ((↑t - ↑(e.k - 1) * (i + 1) - ↑↑(⟨0, by have := e.hk; omega⟩ : Fin e.k)).toNat)
            (↑e.k * (i + 1) + ↑↑(⟨0, by have := e.hk; omega⟩ : Fin e.k))
            = e.C_orig.nextt c (e.k * t) (↑e.k * i + ↑e.k) := by
          congr 1
          · simp only [Nat.cast_zero, sub_zero]
            have h_int : (↑t - ↑(e.k - 1) * (i + 1) : ℤ) = ↑(e.k * t) := by
              rw [hk1]; push_cast; nlinarith
            rw [h_int, Int.toNat_natCast]
          · simp only [Nat.cast_zero, add_zero]; ring
        -- Apply foldSwitch_correct with the actual q (unified via hq)
        have h_fold := e.foldSwitch_correct c (e.k * t) (↑e.k * i)
          (fun j => e.C_orig.nextt c (e.k * t) (↑e.k * i + ↑↑j))
          _ (fun _ => rfl) hq m
        rw [h_fold]
        -- Goal: nextt c (k*t+k-m) (k*i+m) = nextt c ((t+1-(k-1)*i-m).toNat) (k*i+m)
        congr 1
        symm
        have h_int : (↑(t + 1) - ↑(e.k - 1) * i - ↑↑m : ℤ) = ↑(e.k * t + e.k - m.val) := by
          simp only [Nat.cast_sub e.hk1, Nat.cast_sub (show m.val ≤ e.k * t + e.k from by omega)]
          push_cast; nlinarith [m.isLt]
        rw [h_int, Int.toNat_natCast]
      · -- i = -1
        push_neg at hi1
        have hi_eq : i = -1 := by omega
        subst hi_eq
        have h_t_eq : t = 0 := by omega
        subst h_t_eq
        simp only [show (-1 : ℤ) + 1 = 0 from by omega]
        rw [e.spec_nonneg c 0 (by omega) 0]
        simp only [C'_δ_spatial_single]
        congr 1; ext m
        -- q = c 0 = nextt c 0 0, which equals nextt c 0 (k*(-1) + k) by position
        have hq : e.C_orig.nextt c 0 0 = e.C_orig.nextt c 0 (↑e.k * (-1 : ℤ) + ↑e.k) := by
          congr 1; ring
        have h_fold := e.foldSwitch_correct c 0 (↑e.k * (-1 : ℤ))
          (fun j => e.C_orig.nextt c 0 (↑e.k * (-1 : ℤ) + ↑↑j))
          _ (fun _ => by simp) hq m
        simp only [Nat.mul_zero] at *
        rw [h_fold]
        congr 1
        have hm := m.isLt
        have hk1' : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
        -- Show the ℤ expression = ↑(e.k - m.val), then use Int.toNat_natCast
        have h_eq : (↑(0 + 1 : ℕ) - ↑(e.k - 1 : ℕ) * (-1 : ℤ) - (↑m.val : ℤ)) = ↑(e.k - m.val) := by
          rw [hk1']; push_cast; omega
        change 0 + e.k - m.val = (↑(0 + 1 : ℕ) - ↑(e.k - 1 : ℕ) * (-1 : ℤ) - (↑m.val : ℤ)).toNat
        rw [h_eq, Int.toNat_natCast]; omega
    · ---- STEADY-STATE CASE ----
      push_neg at ht_prev
      rw [iht i hi ht_prev]
      by_cases hi1 : i + 1 < 0
      · -- Right i+1 is negative and diagonal
        have ht1 : (t : ℤ) ≥ -(i + 1) := by omega
        rw [iht (i + 1) hi1 ht1]
        simp only [C'_δ_diagonal, asQ_diagonal]
        -- q = right[0] matches φ/ψ
        have hq_match : e.C_orig.nextt c
            ((↑t - ↑(e.k - 1) * (i + 1) - ↑↑(⟨0, by have := e.hk; omega⟩ : Fin e.k)).toNat)
            (↑e.k * (i + 1) + ↑↑(⟨0, by have := e.hk; omega⟩ : Fin e.k))
            = e.C_orig.nextt c (e.φ t i ⟨e.k - 1, by have := e.hk; omega⟩).toNat
              (↑e.k * i + ↑(e.k - 1 : ℕ) + 1) := by
          congr 1
          · exact congrArg Int.toNat (e.φ_right_zero_eq t i)
          · exact e.ψ_right_zero_eq i
        rw [hq_match]
        congr 1; ext m
        exact e.foldDiag_diagonal_step c i hi t ht_prev _ _
          (fun j => rfl) rfl m.val m.isLt
      · -- i = -1
        push_neg at hi1
        have hi_eq : i = -1 := by omega
        subst hi_eq
        simp only [show (-1 : ℤ) + 1 = 0 from by omega]
        rw [e.spec_nonneg c 0 (by omega) t]
        simp only [C'_δ_diagonal, asQ_single]
        -- q = nextt c t 0 matches φ(t,-1,k-1).toNat and pos 0
        have hq_match : e.C_orig.nextt c t 0 =
            e.C_orig.nextt c (e.φ t (-1) ⟨e.k - 1, by have := e.hk; omega⟩).toNat
              (↑e.k * (-1 : ℤ) + ↑(e.k - 1 : ℕ) + 1) := by
          congr 1
          · -- φ(t,-1,k-1) = t
            simp only [φ]
            have : (↑t : ℤ) - ↑(e.k - 1 : ℕ) * (-1 : ℤ) - ↑(e.k - 1 : ℕ) = ↑t := by
              have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
              rw [hk1]; ring
            rw [this, Int.toNat_natCast]
          · have := e.hk1; omega
        rw [hq_match]
        congr 1; ext m
        exact e.foldDiag_diagonal_step c (-1) (by omega) t (by omega) _ _
          (fun j => rfl) rfl m.val m.isLt

-- Main specification: combines both regimes
-- For i < 0 and t ≥ -i (diagonal regime), the compressed CA tracks the original:
--   component j at compressed position i, time t
--   = original CA at time (t - (k-1)·i - j) and position (k·i + j)
theorem spec (c : Config e.Q) (i : ℤ) (hi : i < 0) (t : ℕ) (ht : (t : ℤ) ≥ -i) (j : Fin e.k) :
    e.C'.comp (e.compress c) t i j =
    e.C_orig.comp c ((t - (e.k - 1 : ℕ) * i - j).toNat) (e.k * i + j) := by
  simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply]
  rw [e.spec_diagonal c i hi t ht]
  simp only [C', C_orig, id]

end LeftIndepSpeedupConfig

end CellularAutomatas
