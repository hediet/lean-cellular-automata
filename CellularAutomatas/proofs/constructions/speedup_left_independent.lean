import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.border
import CellularAutomatas.proofs.constructions.border_quiescent_left_independent

namespace CellularAutomatas

/-!
# Left-Independent CA Compression (k-step speedup)

Given a left-independent CA `C = (Q, δ)` and compression factor `k ≥ 2`, we construct
a new left-independent CA `C' = (Q', δ')` that compresses k consecutive diagonal cells
into a single tuple.

## Key properties required:
- Left-independence: `δ(a, b, c) = δ(a', b, c)` for all `a, a'`
- Border state `#` is quiescent and initial
-/

structure LeftIndepSpeedupQuiescent where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β
  k : ℕ
  hk : k ≥ 2
  h_left_indep : C_orig.left_independent
  h_quiescent : C_orig.quiescent C_orig.border

attribute [instance] LeftIndepSpeedupQuiescent._inst_α
attribute [instance] LeftIndepSpeedupQuiescent._inst_β

namespace LeftIndepSpeedupQuiescent

variable (e : LeftIndepSpeedupQuiescent)

-- Convenience: k ≥ 1
lemma hk1 : e.k ≥ 1 := Nat.one_le_of_lt e.hk

-- Quiescence: δ(border, border, border) = border
lemma quiescent_border : e.C_orig.δ e.C_orig.border e.C_orig.border e.C_orig.border = e.C_orig.border := by
  have h := e.h_quiescent
  unfold CellAutomaton.quiescent CellAutomaton.quiescent_set at h
  exact h ⟨e.C_orig.border, rfl⟩ ⟨e.C_orig.border, rfl⟩ ⟨e.C_orig.border, rfl⟩

-- Since C is left-independent, δ(_, b, c) only depends on b and c
def δ₂ (b c : e.C_orig.Q) : e.C_orig.Q := e.C_orig.δ e.C_orig.border b c

-- State space Q' for the compressed automaton
inductive Q' where
  | single (q : e.C_orig.Q) : Q'
  | compr (w : Fin e.k → e.C_orig.Q) : Q'
deriving DecidableEq

instance : Fintype e.Q' :=
  Fintype.ofEquiv (e.C_orig.Q ⊕ (Fin e.k → e.C_orig.Q))
    { toFun := fun
        | .inl q => Q'.single q
        | .inr w => Q'.compr w
      invFun := fun
        | Q'.single q => .inl q
        | Q'.compr w => .inr w
      left_inv := fun
        | .inl _ => rfl
        | .inr _ => rfl
      right_inv := fun
        | Q'.single _ => rfl
        | Q'.compr _ => rfl }

instance : Inhabited e.Q' := ⟨Q'.single e.C_orig.border⟩

instance : Alphabet e.Q' := {}

-- Border state for C' is the all-# tuple
def border' : e.Q' := Q'.compr (fun _ => e.C_orig.border)

-- Extract the "effective single" from a Q' state
def asQ : e.Q' → e.C_orig.Q
  | Q'.single q => q
  | Q'.compr w  => w ⟨0, by have := e.hk; omega⟩

@[simp] lemma asQ_single (q : e.C_orig.Q) : e.asQ (Q'.single q) = q := rfl
@[simp] lemma asQ_compr (w : Fin e.k → e.C_orig.Q) :
    e.asQ (Q'.compr w) = w ⟨0, by have := e.hk; omega⟩ := rfl

@[simp] lemma asQ_border' : e.asQ e.border' = e.C_orig.border := rfl

-- Extract j-th component from compr, or border for single
def compr_at (q : e.Q') (j : Fin e.k) : e.C_orig.Q :=
  match q with
  | Q'.single _ => e.C_orig.border
  | Q'.compr w  => w j

/-- Project Q' to a k-tuple of β: for compr return the projected tuple, for single broadcast the projected value -/
def projectQ' (q : e.Q') : Fin e.k → e.β :=
  match q with
  | Q'.single q => fun _ => e.C_orig.project q
  | Q'.compr w  => fun j => e.C_orig.project (w j)

/-- Project component j of Q' to β -/
def projectQ'_at (q : e.Q') (j : Fin e.k) : e.β :=
  e.C_orig.project (e.compr_at q j)

def foldAux : (n : ℕ) → (Fin n → e.C_orig.Q) → e.C_orig.Q → (Fin n → e.C_orig.Q)
  | 0, _, _ => Fin.elim0
  | n + 1, w, q =>
      let r := e.δ₂ (w (Fin.last n)) q
      Fin.snoc (foldAux n (Fin.init w) r) r

def fold := e.foldAux e.k

-- foldAux on all-border input with border accumulator stays all-border
lemma foldAux_border (n : ℕ) : e.foldAux n (fun _ => e.C_orig.border) e.C_orig.border = fun _ => e.C_orig.border := by
  induction n with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
    simp only [foldAux]
    have hr : e.δ₂ e.C_orig.border e.C_orig.border = e.C_orig.border := by
      simp only [δ₂]
      exact e.quiescent_border
    simp only [hr, Fin.init_def]
    conv => lhs; rw [ih]
    funext j
    simp only [Fin.snoc]
    split_ifs <;> rfl

lemma fold_border : e.fold (fun _ => e.C_orig.border) e.C_orig.border = fun _ => e.C_orig.border :=
  e.foldAux_border e.k

-- Key property: foldAux at last position equals δ₂ applied to last element
lemma foldAux_last (n : ℕ) (hn : n ≥ 1) (w : Fin n → e.C_orig.Q) (q : e.C_orig.Q) :
    e.foldAux n w q ⟨n - 1, by omega⟩ = e.δ₂ (w ⟨n - 1, by omega⟩) q := by
  cases n with
  | zero => omega
  | succ n =>
    unfold foldAux
    simp only [Nat.succ_sub_one, Fin.snoc]
    split_ifs with h
    · omega
    · rfl

-- foldAux at index j < n-1 equals δ₂ of w_j and foldAux at j+1
-- This lemma describes the recursive structure of foldAux
-- The proof requires handling dite/cast from Fin.snoc; deferred to separate verification.
lemma foldAux_step (n : ℕ) (w : Fin n → e.C_orig.Q) (q : e.C_orig.Q) (j : Fin n)
    (hj : j.val + 1 < n) :
    e.foldAux n w q j = e.δ₂ (w j) (e.foldAux n w q ⟨j.val + 1, hj⟩) := by
  induction n generalizing q with
  | zero => exact Fin.elim0 j
  | succ n ihn =>
    have hj_lt_n : j.val < n := by omega
    -- Reduce foldAux (n+1) at j (j.val < n) to inner foldAux n
    have h_j : e.foldAux (n + 1) w q j =
        e.foldAux n (Fin.init w) (e.δ₂ (w (Fin.last n)) q) ⟨j.val, hj_lt_n⟩ := by
      simp [foldAux, Fin.snoc, dif_pos hj_lt_n]; rfl
    rw [h_j]
    by_cases h : j.val + 1 < n
    · -- j+1 also in the inner part
      have h_j1 : e.foldAux (n + 1) w q ⟨j.val + 1, hj⟩ =
          e.foldAux n (Fin.init w) (e.δ₂ (w (Fin.last n)) q) ⟨j.val + 1, h⟩ := by
        simp [foldAux, Fin.snoc, dif_pos h]
      rw [h_j1, ihn _ _ ⟨j.val, hj_lt_n⟩ h]
      congr 1
    · -- j+1 = n
      have h_last : e.foldAux (n + 1) w q ⟨j.val + 1, hj⟩ =
          e.δ₂ (w (Fin.last n)) q := by
        simp [foldAux, Fin.snoc, show ¬(↑(⟨j.val + 1, hj⟩ : Fin (n + 1)) < n) from by omega]
      rw [h_last]
      have hj_val : j.val = n - 1 := by omega
      have hj_eq : (⟨j.val, hj_lt_n⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
        ext; exact hj_val
      rw [hj_eq, e.foldAux_last n (by omega) (Fin.init w) (e.δ₂ (w (Fin.last n)) q)]
      -- δ₂ (init w ⟨n-1, _⟩) r = δ₂ (w j) r; both Fin args have same val (n-1 = j.val)
      simp only [δ₂, Fin.init]
      congr 2
      exact Fin.ext hj_val.symm

-- fold at last component j = k-1: fold(w, q)_{k-1} = δ₂(w_{k-1}, q)
lemma fold_last (w : Fin e.k → e.C_orig.Q) (q : e.C_orig.Q) :
    e.fold w q ⟨e.k - 1, by have := e.hk; omega⟩ = e.δ₂ (w ⟨e.k - 1, by have := e.hk; omega⟩) q := by
  exact e.foldAux_last e.k e.hk1 w q

-- fold at component j < k-1: fold(w, q)_j = δ₂(w_j, fold(w, q)_{j+1})
lemma fold_step (w : Fin e.k → e.C_orig.Q) (q : e.C_orig.Q) (j : Fin e.k) (hj : j.val + 1 < e.k) :
    e.fold w q j = e.δ₂ (w j) (e.fold w q ⟨j.val + 1, hj⟩) := by
  exact e.foldAux_step e.k w q j hj

-- Transition function δ' for the compressed automaton
def δ' (_a b c : e.Q') : e.Q' :=
  match b with
  | Q'.single q_b => Q'.single (e.δ₂ q_b (e.asQ c))
  | Q'.compr w_b  => Q'.compr (fun j => e.fold w_b (e.asQ c) j)

-- The compressed CA
def C : CellAutomaton e.α？ (Fin e.k → e.β) := {
  Q := e.Q'
  δ := e.δ'
  embed := fun a => match a with
    | some a' => Q'.single (e.C_orig.embed (some a'))
    | none    => e.border'
  project := e.projectQ'
}

-- Simp lemmas for the compressed transition, keeping asQ folded
@[simp] lemma C_δ_single (a : e.Q') (q : e.C_orig.Q) (c : e.Q') :
    e.C.δ a (Q'.single q) c = Q'.single (e.δ₂ q (e.asQ c)) := rfl

@[simp] lemma C_δ_compr (a : e.Q') (w : Fin e.k → e.C_orig.Q) (c : e.Q') :
    e.C.δ a (Q'.compr w) c = Q'.compr (fun j => e.fold w (e.asQ c) j) := rfl

-- The compressed CA is left-independent
lemma C_left_indep : e.C.left_independent := by
  intro q1 q2 q3 q1'
  simp only [C, δ']

-- The border of C is border'
@[simp] lemma C_border : e.C.border = e.border' := rfl

/-- Compute and project component j: run C for t steps, then project component j at position i -/
def comp_at (c : Config e.C.Q) (t : ℕ) (i : ℤ) (j : Fin e.k) : e.β :=
  e.C.comp c t i j

-- The compressed CA is quiescent at border'
lemma C_quiescent : e.C.quiescent e.C.border := by
  unfold CellAutomaton.quiescent CellAutomaton.quiescent_set
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  simp only [Set.mem_singleton_iff] at ha hb hc
  subst ha hb hc
  simp only [C_border, C_δ_compr, border']
  congr 1
  exact e.fold_border

/-!
## The Specification

Position and time mappings for the correctness statement (0-indexed):
- `ψ(i, j) = k*i + j` : maps compressed position `i` and component `j` to original position
- `φ(t, i, j) = t - (k-1)*i - j` : maps time and position to original time

For i = 0 (first cell in word): ψ(0, j) = j, so components 0..k-1 map to positions 0..k-1.
For i = -1 (last compressed cell): ψ(-1, k-1) = -1, so last component maps to position -1.

The spec states: for `i < 0` and the compressed cell at position `i` after `t` steps,
component `j` equals the original cell at position `ψ(i,j)` after `φ(t,i,j)` steps.
-/

def ψ (i : ℤ) (j : Fin e.k) : ℤ := e.k * i + j
def φ (t : ℕ) (i : ℤ) (j : Fin e.k) : ℤ := t - (e.k - 1 : ℕ) * i - j

-- Key algebraic properties of ψ and φ (from the markdown spec)

-- ψ(i+1, 0) = ψ(i, k-1) + 1 : Position continuity across cells
lemma psi_succ_zero_eq (i : ℤ) : e.ψ (i + 1) ⟨0, by have := e.hk; omega⟩ = e.ψ i ⟨e.k - 1, by have := e.hk; omega⟩ + 1 := by
  simp only [ψ]
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  simp only [Nat.cast_zero, hk1]
  ring

-- ψ(i, j+1) = ψ(i, j) + 1 : Components are consecutive positions
lemma psi_succ_j (i : ℤ) (j : Fin e.k) (hj : j.val + 1 < e.k) :
    e.ψ i ⟨j.val + 1, hj⟩ = e.ψ i j + 1 := by
  simp only [ψ, Nat.cast_add, Nat.cast_one]
  ring

-- φ(t, i+1, 0) = φ(t, i, k-1) : Time continuity across cells
lemma phi_pos_succ_zero_eq (t : ℕ) (i : ℤ) :
    e.φ t (i + 1) ⟨0, by have := e.hk; omega⟩ = e.φ t i ⟨e.k - 1, by have := e.hk; omega⟩ := by
  simp only [φ]
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  simp only [Nat.cast_zero, hk1]
  ring

-- φ(t+1, i, j+1) = φ(t, i, j) : Staircase time relation (for j+1 < k)
lemma phi_time_succ_j (t : ℕ) (i : ℤ) (j : Fin e.k) (hj : j.val + 1 < e.k) :
    e.φ (t + 1) i ⟨j.val + 1, hj⟩ = e.φ t i j := by
  simp only [φ, Nat.cast_add, Nat.cast_one]
  ring

-- φ(t, i, j) ≥ 0 for i < 0 : ensures toNat doesn't clip
lemma phi_nonneg (t : ℕ) (i : ℤ) (hi : i < 0) (j : Fin e.k) : 0 ≤ e.φ t i j := by
  simp only [φ]
  have hj : (j : ℤ) ≤ e.k - 1 := by have := j.isLt; omega
  have hk_sub : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by
    have h := e.hk1
    omega
  rw [hk_sub]
  -- φ = t - (k-1)*i - j = t + (k-1)*(-i) - j
  -- Since i < 0, -i ≥ 1, so (k-1)*(-i) ≥ k-1
  -- Thus φ ≥ t + (k-1) - j ≥ t + (k-1) - (k-1) = t ≥ 0
  have hi' : -i ≥ 1 := by omega
  have h1 : ((e.k : ℤ) - 1) * (-i) ≥ ((e.k : ℤ) - 1) * 1 := by
    apply mul_le_mul_of_nonneg_left hi'
    have := e.hk
    omega
  linarith

-- ψ(i, j) < 0 for i < 0 : compressed positions stay negative
lemma psi_neg (i : ℤ) (hi : i < 0) (j : Fin e.k) : e.ψ i j < 0 := by
  simp only [ψ]
  have hj : (j : ℤ) ≤ e.k - 1 := by have := j.isLt; omega
  -- ψ = k*i + j ≤ k*i + (k-1) ≤ k*(-1) + (k-1) = -1 < 0
  have hki : e.k * i ≤ -e.k := by
    have hk : (0 : ℤ) < e.k := by have := e.hk; omega
    have : i ≤ -1 := by omega
    calc e.k * i ≤ e.k * (-1) := by apply Int.mul_le_mul_of_nonneg_left this; omega
      _ = -e.k := by ring
  linarith

-- φ(0, i, j) < -ψ(i, j) for i < 0: at t=0, we're strictly in the quiescent zone
-- Proof: φ(0,i,j) = -(k-1)*i - j and -ψ(i,j) = -k*i - j, so φ - (-ψ) = i < 0.
lemma phi_zero_lt_neg_psi (i : ℤ) (hi : i < 0) (j : Fin e.k) : e.φ 0 i j < -e.ψ i j := by
  simp only [φ, ψ]
  have hk_sub : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have h := e.hk1; omega
  simp only [Nat.cast_zero, hk_sub]
  linarith

-- compr_at of border' is border
@[simp] lemma compr_at_border' (j : Fin e.k) : e.compr_at e.border' j = e.C_orig.border := rfl

-- compr_at of compr is just indexing
@[simp] lemma compr_at_compr (w : Fin e.k → e.C_orig.Q) (j : Fin e.k) :
    e.compr_at (Q'.compr w) j = w j := rfl

-- At t=0, position i < 0 has border' state
lemma nextt_zero_neg (w : Word e.α) (i : ℤ) (hi : i < 0) :
    e.C.nextt (w) 0 i = e.border' := by
  simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config,
             word_to_config, C]
  split_ifs with h
  · omega
  · rfl

-- C_orig stays border at negative positions within the light-cone.
-- For left-independent CAs, cell (p, t) depends on initial cells p..p+t.
-- So if p + t < 0, all dependencies are in the border zone.
lemma C_orig_neg_border (w : Word e.α) (p : ℤ) (hp : p < 0) (t : ℕ) (ht : t < -p) :
    e.C_orig.nextt (w) t p = e.C_orig.border := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config,
               word_to_config]
    split_ifs with h
    · omega
    · rfl
  | succ t iht =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- t+1 < -p means p+t+1 < 0, so p+t < -1 < 0
    have hmid := iht p hp (by omega)
    have hleft := iht (p - 1) (by omega) (by omega)
    -- Right neighbor: p+1 < 0 since p + (t+1) < 0 implies p + 1 ≤ p + t + 1 < 0
    have hright := iht (p + 1) (by omega) (by omega)
    rw [hmid, hleft, hright]
    exact e.quiescent_border

/-!
## Main Specification Theorem

For a word `w`, the compressed automaton satisfies the spec relating C' states to C_orig states
via ψ and φ. The embedding of the word automatically provides border conditions.
-/

-- asQ of the embedded configuration equals the original embedded configuration
lemma asQ_embed_word (w : Word e.α) (p : ℤ) :
    e.asQ (CellAutomaton.embed_config (C := e.C) (⟬w⟭) p) =
    CellAutomaton.embed_config (C := e.C_orig) (⟬w⟭) p := by
  simp only [CellAutomaton.embed_config, word_to_config]
  split_ifs with h
  · simp only [C, asQ]
  · simp only [C, asQ, border', CellAutomaton.border]

-- C_orig.nextt at border position stays border (left-independence + quiescence)
theorem C_orig_border_stays (w : Word e.α) (i : ℤ) (hi : i ≥ w.length) (t : ℕ) :
    e.C_orig.nextt (w) t i = e.C_orig.border :=
  CellAutomaton.border_stays_right e.C_orig e.h_left_indep e.h_quiescent w i hi t

-- For i ≥ w.length: cell stays border' (compressed border)
theorem spec_border (w : Word e.α) (i : ℤ) (hi : i ≥ w.length) (t : ℕ) :
    e.C.nextt (w) t i = e.border' := by
  rw [← e.C_border]
  exact CellAutomaton.border_stays_right e.C e.C_left_indep e.C_quiescent w i hi t

-- For 0 ≤ i < w.length: compressed automaton tracks original as single states
-- Key: δ'(_, single q, c) = single (δ₂ q (asQ c)), so single propagates
theorem spec_nonneg (w : Word e.α) (i : ℤ) (hi : 0 ≤ i) (hi' : i < w.length) (t : ℕ) :
    e.C.nextt (w) t i =
    Q'.single (e.C_orig.nextt (w) t i) := by
  induction t generalizing i with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config,
               word_to_config, C]
    split_ifs with h
    · rfl
    · omega
  | succ t iht =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- Get IH for middle position
    have ihm := iht i hi hi'
    rw [ihm]
    simp only [C_δ_single]
    congr 1
    simp only [δ₂]
    -- The right neighbor: either within word (single by IH) or at border
    by_cases hr : i + 1 < w.length
    · -- Right neighbor is within word, use IH
      have ihr := iht (i + 1) (by omega) hr
      simp only [ihr, asQ_single]
      exact e.h_left_indep _ _ _ _
    · -- Right neighbor is at border (i + 1 ≥ w.length)
      have hbr := e.spec_border w (i + 1) (by omega) t
      simp only [hbr, asQ_border']
      rw [e.C_orig_border_stays w (i + 1) (by omega) t]
      exact e.h_left_indep _ _ _ _

-- asQ of nextt result equals C_orig.nextt for i ≥ 0
-- Corollary: follows from spec_nonneg (single case) and spec_border (border case)
theorem asQ_nextt (w : Word e.α) (i : ℤ) (hi : 0 ≤ i) (t : ℕ) :
    e.asQ (e.C.nextt (w) t i) =
    e.C_orig.nextt (w) t i := by
  by_cases hi' : i < w.length
  · -- Within word: it's a single, so asQ extracts the value
    rw [e.spec_nonneg w i hi hi' t]
    simp only [asQ_single]
  · -- At or past border
    rw [e.spec_border w i (by omega) t]
    simp only [asQ_border']
    exact (e.C_orig_border_stays w i (by omega) t).symm

-- Helper: at negative positions, the state is always compr
lemma neg_is_compr (w : Word e.α) (i : ℤ) (hi : i < 0) (t : ℕ) :
    ∃ w', e.C.nextt (w) t i = Q'.compr w' := by
  induction t with
  | zero => rw [e.nextt_zero_neg w i hi]; exact ⟨_, rfl⟩
  | succ t' ih' =>
    obtain ⟨w_prev, hw_prev⟩ := ih'
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next, hw_prev, C_δ_compr]
    exact ⟨_, rfl⟩

-- Specification: for i < 0, component j of the compressed cell at position i after t steps
-- equals the original cell at position ψ(i,j) after φ(t,i,j) steps.
--
-- Proof by outer induction on t, with inner descending induction on j for the inductive case.
theorem spec_nextt (w : Word e.α) (i : ℤ) (hi : i < 0) (t : ℕ) (j : Fin e.k) :
    e.compr_at (e.C.nextt (w) t i) j =
    e.C_orig.nextt (w) (e.φ t i j).toNat (e.ψ i j) := by
  -- Outer induction on t
  induction t generalizing i j with
  | zero =>
    -- Base case: at t=0, position i < 0 has border' state
    rw [e.nextt_zero_neg w i hi]
    simp only [compr_at_border']
    -- Need: C_orig.nextt ... (φ(0,i,j)).toNat (ψ(i,j)) = border
    -- Since ψ(i,j) < 0 and φ(0,i,j) ≤ -ψ(i,j), we're in the quiescent zone
    have hpsi : e.ψ i j < 0 := e.psi_neg i hi j
    have hphi_lt : e.φ 0 i j < -e.ψ i j := e.phi_zero_lt_neg_psi i hi j
    have hphi_nonneg : 0 ≤ e.φ 0 i j := e.phi_nonneg 0 i hi j
    rw [e.C_orig_neg_border w (e.ψ i j) hpsi (e.φ 0 i j).toNat (by
      rw [Int.toNat_of_nonneg hphi_nonneg]
      omega)]
  | succ t iht =>
    -- Inductive case
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]

    -- Use helper lemma for compr structure
    obtain ⟨w_a, hw_a⟩ := e.neg_is_compr w i hi t
    simp only [hw_a, C_δ_compr, compr_at_compr]

    -- By IH, w_a j' = C_orig.nextt (φ(t,i,j')).toNat (ψ(i,j'))
    have h_wa : ∀ j', w_a j' = e.C_orig.nextt (w) (e.φ t i j').toNat (e.ψ i j') := by
      intro j'
      have h_ih := iht i hi j'
      rw [hw_a] at h_ih
      simp only [compr_at_compr] at h_ih
      exact h_ih

    -- Get q = asQ (nextt t (i+1))
    set q := e.asQ (e.C.nextt (w) t (i + 1)) with hq_def

    -- Key: q = C_orig.nextt (φ(t,i,k-1)).toNat (ψ(i,k-1)+1)
    have hq : q = e.C_orig.nextt (w) (e.φ t i ⟨e.k - 1, by have := e.hk; omega⟩).toNat (e.ψ i ⟨e.k - 1, by have := e.hk; omega⟩ + 1) := by
      by_cases hi1 : i + 1 < 0
      · -- i+1 < 0: Use helper lemma and main IH
        obtain ⟨w_b, hw_b⟩ := e.neg_is_compr w (i + 1) hi1 t
        rw [hq_def, hw_b, asQ_compr]
        -- By IH: w_b 0 = C_orig.nextt (φ(t,i+1,0)).toNat (ψ(i+1,0))
        have h_ih_i1 := iht (i + 1) hi1 ⟨0, by have := e.hk; omega⟩
        rw [hw_b] at h_ih_i1
        simp only [compr_at_compr] at h_ih_i1
        rw [h_ih_i1]
        congr 1
        · exact congrArg Int.toNat (e.phi_pos_succ_zero_eq t i)
        · exact e.psi_succ_zero_eq i
      · -- i+1 ≥ 0: q = C_orig.nextt t (i+1)
        -- When i+1 ≥ 0 and i < 0, we have i = -1
        have hi_eq : i = -1 := by omega
        subst hi_eq
        simp only [neg_add_cancel] at hq_def ⊢
        rw [hq_def, e.asQ_nextt w 0 (by omega) t]
        -- Need: C_orig.nextt t 0 = C_orig.nextt (φ(t,-1,k-1)).toNat (ψ(-1,k-1)+1)
        -- With 0-indexed formulas:
        --   ψ(-1, k-1) = k*(-1) + (k-1) = -1, so ψ(-1, k-1) + 1 = 0
        --   φ(t, -1, k-1) = t - (k-1)*(-1) - (k-1) = t + (k-1) - (k-1) = t
        -- So the goal is C_orig.nextt t 0 = C_orig.nextt t 0, which is trivial!
        have hpsi : e.ψ (-1) ⟨e.k - 1, by have := e.hk; omega⟩ + 1 = 0 := by
          simp only [ψ]
          have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
          simp only [hk1]
          ring
        have hphi : e.φ t (-1) ⟨e.k - 1, by have := e.hk; omega⟩ = t := by
          simp only [φ]
          have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
          simp only [hk1]
          ring
        simp only [hpsi, hphi, Int.toNat_natCast]

    -- Inner descending induction on j from k-1 to 0
    -- Goal: fold w_a q j = C_orig.nextt (φ(t+1,i,j)).toNat (ψ(i,j))
    obtain ⟨j_val, hj_lt⟩ := j
    -- Use descending induction: prove for all m from k-1 down to 0
    suffices h : ∀ m : ℕ, (hm : m < e.k) →
      e.fold w_a q ⟨m, hm⟩ =
      e.C_orig.nextt (w) (e.φ (t + 1) i ⟨m, hm⟩).toNat (e.ψ i ⟨m, hm⟩) by
      exact h j_val hj_lt
    intro m hm
    -- Induction on (k-1-m)
    induction hd : e.k - 1 - m generalizing m with
    | zero =>
      -- m = k - 1
      have hm_eq : m = e.k - 1 := by omega
      subst hm_eq
      rw [e.fold_last w_a q, h_wa ⟨e.k - 1, hm⟩, hq]
      simp only [δ₂]
      -- Goal: δ # (nextt φ.toNat ψ) (nextt φ.toNat (ψ+1)) = nextt (φ+1).toNat ψ
      have hphi_nonneg : 0 ≤ e.φ t i ⟨e.k - 1, hm⟩ := e.phi_nonneg t i hi ⟨e.k - 1, hm⟩
      -- φ(t+1, i, k-1) = φ(t, i, k-1) + 1
      have phi_succ_eq : e.φ (t + 1) i ⟨e.k - 1, hm⟩ = e.φ t i ⟨e.k - 1, hm⟩ + 1 := by
        simp only [φ]; push_cast; ring
      have phi_toNat_succ : (e.φ (t + 1) i ⟨e.k - 1, hm⟩).toNat = (e.φ t i ⟨e.k - 1, hm⟩).toNat + 1 := by
        rw [phi_succ_eq]
        have h1 : (e.φ t i ⟨e.k - 1, hm⟩ + 1).toNat = (e.φ t i ⟨e.k - 1, hm⟩).toNat + 1 := by
          rw [Int.toNat_add hphi_nonneg (by decide : (0 : ℤ) ≤ 1)]
          simp
        exact h1
      rw [phi_toNat_succ, CellAutomaton.nextt_succ, CellAutomaton.next]
      exact (e.h_left_indep _ _ _ _).symm
    | succ d ih_d =>
      -- m < k - 1
      have hm_lt_k1 : m + 1 < e.k := by omega
      have hd' : e.k - 1 - (m + 1) = d := by omega
      have ih_m1 := ih_d (m + 1) hm_lt_k1 hd'
      rw [e.fold_step w_a q ⟨m, hm⟩ hm_lt_k1]
      rw [h_wa ⟨m, hm⟩, ih_m1]
      simp only [δ₂]
      -- φ(t+1, i, m+1) = φ(t, i, m) and ψ(i, m+1) = ψ(i, m) + 1
      have hphi_step : e.φ (t + 1) i ⟨m + 1, hm_lt_k1⟩ = e.φ t i ⟨m, hm⟩ := e.phi_time_succ_j t i ⟨m, hm⟩ hm_lt_k1
      have hpsi_step : e.ψ i ⟨m + 1, hm_lt_k1⟩ = e.ψ i ⟨m, hm⟩ + 1 := e.psi_succ_j i ⟨m, hm⟩ hm_lt_k1
      rw [hphi_step, hpsi_step]
      have hphi_nonneg : 0 ≤ e.φ t i ⟨m, hm⟩ := e.phi_nonneg t i hi ⟨m, hm⟩
      -- φ(t+1, i, m) = φ(t, i, m) + 1
      have phi_succ_eq : e.φ (t + 1) i ⟨m, hm⟩ = e.φ t i ⟨m, hm⟩ + 1 := by
        simp only [φ]; push_cast; ring
      have phi_toNat_succ : (e.φ (t + 1) i ⟨m, hm⟩).toNat = (e.φ t i ⟨m, hm⟩).toNat + 1 := by
        rw [phi_succ_eq]
        have h1 : (e.φ t i ⟨m, hm⟩ + 1).toNat = (e.φ t i ⟨m, hm⟩).toNat + 1 := by
          rw [Int.toNat_add hphi_nonneg (by decide : (0 : ℤ) ≤ 1)]
          simp
        exact h1
      rw [phi_toNat_succ, CellAutomaton.nextt_succ, CellAutomaton.next]
      exact (e.h_left_indep _ _ _ _).symm

/-- Specification using comp: for i < 0, component j of the projected output
    equals the original CA's output at position ψ(i,j) after φ(t,i,j) steps. -/
theorem spec' (w : Word e.α) (i : ℤ) (hi : i < 0) (t : ℕ) (j : Fin e.k) :
    (e.C.comp (w) t i) j = e.C_orig.comp (w) (e.φ t i j).toNat (e.ψ i j) := by
  obtain ⟨w', hw'⟩ := e.neg_is_compr w i hi t
  have h := e.spec_nextt w i hi t j
  rw [hw', compr_at_compr] at h
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold, Function.comp_apply, C]
  show e.projectQ' (e.C.nextt (w) t i) j = _
  rw [hw']
  simp only [projectQ']
  exact congrArg e.C_orig.project h


--def ψ (i : ℤ) (j : Fin e.k) : ℤ := e.k * i + j
--def φ (t : ℕ) (i : ℤ) (j : Fin e.k) : ℤ := t - (e.k - 1 : ℕ) * i - j

/-- Main specification with inlined φ and ψ: for i < 0, component j of the projected output
    equals the original CA's output at position (k*i + j) after (t - (k-1)*i - j) steps. -/
theorem spec (w : Word e.α) (i : ℤ) (hi : i < 0) (t : ℕ) (j : Fin e.k) :
    (e.C.comp (w) t i) j =
    e.C_orig.comp (w) (t - ((e.k - 1) * i) - j).toNat (e.k * i + j) := by
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  have h := e.spec' w i hi t j
  simp only [φ, ψ, hk1] at h
  exact h

end LeftIndepSpeedupQuiescent

/-!
## LeftIndepSpeedup (without quiescence requirement)

By composing with QuiescentBorderLeftIndep, we can apply the k-step speedup
to any left-independent CA without requiring the border to be quiescent.
-/

structure LeftIndepSpeedup where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β
  k : ℕ
  hk : k ≥ 2
  h_left_indep : C_orig.left_independent

attribute [instance] LeftIndepSpeedup._inst_α
attribute [instance] LeftIndepSpeedup._inst_β

namespace LeftIndepSpeedup

variable (e : LeftIndepSpeedup)

/-- The QuiescentBorderLeftIndep construction applied to the original CA -/
def pb : QuiescentBorderLeftIndep :=
  { C_orig := e.C_orig
    h_left_indep := e.h_left_indep }

/-- The LeftIndepSpeedupQuiescent construction applied to the quiescent border CA -/
def speedup : LeftIndepSpeedupQuiescent :=
  { C_orig := e.pb.C
    k := e.k
    hk := e.hk
    h_left_indep := e.pb.C_left_indep
    h_quiescent := e.pb.C_border_quiescent }

/-- The compressed CA: C = speedup.C -/
def C : CellAutomaton e.α？ (Fin e.k → e.β) := e.speedup.C

/-- The compressed CA is left-independent -/
lemma C_left_indep : e.C.left_independent := e.speedup.C_left_indep

/-- Main specification with inlined φ and ψ: for i < 0 and i ≥ -t, component j of the projected output
    equals the original CA's output at position (k*i + j) after (t - (k-1)*i - j) steps.

    This version works without requiring the original CA to have a quiescent border.
    The constraint i ≥ -t ensures the position is within the light cone. -/
theorem spec (w : Word e.α) (hw : w.length > 0) (t : ℕ) (i : ℤ) (hi2 : -(t : ℤ) ≤ i) (hi : i < 0)
    (j : Fin e.k) :
    (e.C.comp (w) t i) j =
    e.C_orig.comp (w) (t - ((e.k - 1) * i) - j).toNat (e.k * i + j) := by
  -- Key definitional equalities
  have hk_eq : e.speedup.k = e.k := rfl
  have hC_orig_eq : e.speedup.C_orig = e.pb.C := rfl
  have hpb_C_orig_eq : e.pb.C_orig = e.C_orig := rfl
  -- Use the speedup spec
  have h_speedup := e.speedup.spec w i hi t j
  simp only [hk_eq] at h_speedup
  -- For i < 0, ψ(i, j) = k*i + j < 0 (always in the cone for left-indep)
  have h_psi_neg : e.k * i + (j : ℤ) < 0 := by
    have hj : (j : ℤ) ≤ e.k - 1 := by have := j.isLt; omega
    have hki : (e.k : ℤ) * i ≤ -(e.k : ℤ) := by
      have hk : (0 : ℤ) < e.k := by have := e.hk; omega
      have : i ≤ -1 := by omega
      calc (e.k : ℤ) * i ≤ (e.k : ℤ) * (-1) := by apply Int.mul_le_mul_of_nonneg_left this; omega
        _ = -(e.k : ℤ) := by ring
    linarith
  have h_phi_nonneg : 0 ≤ (t : ℤ) - ((e.k - 1) * i) - j := by
    have hj : (j : ℤ) ≤ e.k - 1 := by have := j.isLt; omega
    have hi' : -i ≥ 1 := by omega
    have h1 : ((e.k : ℤ) - 1) * (-i) ≥ ((e.k : ℤ) - 1) * 1 := by
      apply mul_le_mul_of_nonneg_left hi'
      have := e.hk; omega
    linarith
  have h_psi_in_cone : e.k * i + (j : ℤ) ∈ WordConeLeftIndep w (t - ((e.k - 1) * i) - j).toNat := by
    rw [WordConeLeftIndep_mem]
    constructor
    · rw [Int.toNat_of_nonneg h_phi_nonneg]
      -- Need: -(t - (k-1)*i - j) ≤ k*i + j
      -- Simplifies to: -t ≤ i (use hi')
      have hk_pos : (e.k : ℤ) > 0 := by have := e.hk; omega
      calc -(↑t - (↑e.k - 1) * i - ↑↑j)
          = -↑t + (↑e.k - 1) * i + ↑↑j := by ring
        _ ≤ i + (↑e.k - 1) * i + ↑↑j := by linarith [hi2]
        _ = ↑e.k * i + ↑↑j := by ring
    · omega
  -- Use quiescent_border.spec
  have h_pb := e.pb.spec w hw (t - ((e.k - 1) * i) - j).toNat (e.k * i + j)
  rw [if_pos h_psi_in_cone, hpb_C_orig_eq] at h_pb
  -- Combine: C.comp = speedup.C.comp → pb.C.comp → C_orig.comp
  simp only [C]
  rw [h_speedup, hC_orig_eq, h_pb]

end LeftIndepSpeedup

end CellularAutomatas
