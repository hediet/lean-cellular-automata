import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.border
import CellularAutomatas.proofs.constructions.border_quiescent

namespace CellularAutomatas

/-!
# Right-Border Speedup for Left-Independent CAs (OCAs)

Given a left-independent CA `C` with quiescent border and compression factor `k ≥ 2`,
we construct a new CA `C'` that compresses k temporal steps into one.

## Key Insight

For left-independent CAs, information flows right-to-left. The right border is quiescent.
At each compressed step, a cell uses its right neighbor's k-tuple to perform k original
temporal steps via a left fold: component j tracks original time T+j at position i.

## Main Spec

At position 0, for compressed time t ≥ n (where n = |w|):
  C'.nextt w t 0 = compressed v  where  v[j] = C.nextt w (k·t - (k-1)·n + j) 0
-/

/-- State type for right-border compressed automaton -/
inductive SingleOrCompressed (β : Type) (k : ℕ) where
  | single (q : β) : SingleOrCompressed β k
  | compressed (w : Fin k → β) : SingleOrCompressed β k
deriving DecidableEq

namespace SingleOrCompressed

variable {β : Type} {k : ℕ}

instance [Fintype β] : Fintype (SingleOrCompressed β k) :=
  Fintype.ofEquiv (β ⊕ (Fin k → β))
    { toFun := fun
        | .inl q => single q
        | .inr w => compressed w
      invFun := fun
        | single q => .inl q
        | compressed w => .inr w
      left_inv := fun
        | .inl _ => rfl
        | .inr _ => rfl
      right_inv := fun
        | single _ => rfl
        | compressed _ => rfl }

instance [Inhabited β] : Inhabited (SingleOrCompressed β k) := ⟨single default⟩

instance [Alphabet β] : Alphabet (SingleOrCompressed β k) := {}

/-- Get component j from compressed, or the single value broadcast -/
def getComponent (s : SingleOrCompressed β k) (j : Fin k) : β :=
  match s with
  | single q => q
  | compressed w => w j

end SingleOrCompressed

open SingleOrCompressed

structure RightBorderSpeedupOCA where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β
  k : ℕ
  hk : k ≥ 2
  h_left_indep : C_orig.left_independent
  h_quiescent : C_orig.quiescent C_orig.border

attribute [instance] RightBorderSpeedupOCA._inst_α
attribute [instance] RightBorderSpeedupOCA._inst_β

namespace RightBorderSpeedupOCA

variable (e : RightBorderSpeedupOCA)

lemma hk1 : e.k ≥ 1 := Nat.one_le_of_lt e.hk

lemma quiescent_border : e.C_orig.δ e.C_orig.border e.C_orig.border e.C_orig.border = e.C_orig.border := by
  have h := e.h_quiescent
  unfold CellAutomaton.quiescent CellAutomaton.quiescent_set at h
  exact h ⟨e.C_orig.border, rfl⟩ ⟨e.C_orig.border, rfl⟩ ⟨e.C_orig.border, rfl⟩

/-- Since C is left-independent, δ(_, b, c) only depends on b and c -/
def δ₂ (b c : e.C_orig.Q) : e.C_orig.Q := e.C_orig.δ e.C_orig.border b c

lemma δ₂_eq (a b c : e.C_orig.Q) : e.C_orig.δ a b c = e.δ₂ b c := e.h_left_indep a b c e.C_orig.border

lemma δ₂_border : e.δ₂ e.C_orig.border e.C_orig.border = e.C_orig.border := by
  simp only [δ₂]
  exact e.quiescent_border

/-! ## Left fold for temporal compression

The left fold computes k temporal steps: given initial state q and neighbor states
w[0], w[1], ..., w[k-1] (at consecutive times), produce the state at k consecutive
future times via: `foldLeft q w [j] = δ₂(δ₂(...δ₂(q, w[0])..., w[j-1]), w[j])`.
-/

/-- Auxiliary recursive left fold: applies m steps starting from q. -/
def foldLeftAux (q : e.C_orig.Q) (w : Fin e.k → e.C_orig.Q) : (m : ℕ) → (hm : m ≤ e.k) → e.C_orig.Q
  | 0, _ => q
  | m + 1, hm => e.δ₂ (foldLeftAux q w m (by omega)) (w ⟨m, by omega⟩)

/-- Left fold: component j applies j+1 steps of δ₂ with neighbor states. -/
def foldLeft (q : e.C_orig.Q) (w : Fin e.k → e.C_orig.Q) : Fin e.k → e.C_orig.Q :=
  fun j => e.foldLeftAux q w (j.val + 1) (by have := j.isLt; omega)

@[simp]
lemma foldLeft_zero (q : e.C_orig.Q) (w : Fin e.k → e.C_orig.Q) :
    e.foldLeft q w ⟨0, by have := e.hk; omega⟩ = e.δ₂ q (w ⟨0, by have := e.hk; omega⟩) := rfl

lemma foldLeft_succ (q : e.C_orig.Q) (w : Fin e.k → e.C_orig.Q)
    (j : Fin e.k) (hj : j.val + 1 < e.k) :
    e.foldLeft q w ⟨j.val + 1, hj⟩ = e.δ₂ (e.foldLeft q w j) (w ⟨j.val + 1, hj⟩) := rfl

private lemma foldLeftAux_border (m : ℕ) (hm : m ≤ e.k) :
    e.foldLeftAux e.C_orig.border (fun _ => e.C_orig.border) m hm = e.C_orig.border := by
  induction m with
  | zero => rfl
  | succ m ih => show e.δ₂ _ _ = _; rw [ih]; exact e.δ₂_border

lemma foldLeft_border :
    e.foldLeft e.C_orig.border (fun _ => e.C_orig.border) = fun _ => e.C_orig.border := by
  funext j; exact e.foldLeftAux_border (j.val + 1) (by have := j.isLt; omega)

/-- Key linking lemma: left fold applied to original CA states advances time.

    If `q = C_orig.nextt w T i` and `w_fn[m] = C_orig.nextt w (T + m) (i + 1)`,
    then `foldLeft q w_fn j = C_orig.nextt w (T + j + 1) i`. -/
lemma foldLeft_nextt (w : Word e.α) (i : ℤ) (T : ℕ)
    (q : e.C_orig.Q) (hq : q = e.C_orig.nextt (↑w) T i)
    (w_fn : Fin e.k → e.C_orig.Q)
    (hw_fn : ∀ m : Fin e.k, w_fn m = e.C_orig.nextt (↑w) (T + m.val) (i + 1))
    (j : Fin e.k) :
    e.foldLeft q w_fn j = e.C_orig.nextt (↑w) (T + j.val + 1) i := by
  -- Auxiliary: foldLeftAux q w_fn m gives nextt (T + m) at i
  suffices h : ∀ m (hm : m ≤ e.k),
      e.foldLeftAux q w_fn m hm = e.C_orig.nextt (↑w) (T + m) i by
    have := h (j.val + 1) (by have := j.isLt; omega)
    simp only [foldLeft]
    convert this using 2 <;> omega
  intro m hm
  induction m with
  | zero => simpa using hq
  | succ m ih =>
    simp only [foldLeftAux]
    rw [ih (by omega), hw_fn ⟨m, by omega⟩]
    have h_step : T + (m + 1) = (T + m) + 1 := by omega
    rw [h_step, CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    exact (e.δ₂_eq _ _ _).symm

/-! ## Transition function and compressed CA -/

/-- Transition function for the compressed automaton.
    Uses `foldLeft` for all compressed transitions (temporal compression). -/
def δ' (_a b c : SingleOrCompressed e.C_orig.Q e.k) : SingleOrCompressed e.C_orig.Q e.k :=
  match b, c with
  | single q_b, single q_c => single (e.δ₂ q_b q_c)
  | single q_b, compressed w_c => compressed (e.foldLeft q_b w_c)
  | compressed w_b, compressed w_c =>
      -- Advance from last component of current cell using neighbor's tuple
      compressed (e.foldLeft (w_b ⟨e.k - 1, by have := e.hk; omega⟩) w_c)
  | compressed w_b, single q_c =>
      -- Doesn't occur in valid computation; must be total
      compressed (e.foldLeft (w_b ⟨e.k - 1, by have := e.hk; omega⟩) (fun _ => q_c))

/-- The border state: all-border compressed tuple -/
def border' : SingleOrCompressed e.C_orig.Q e.k := compressed (fun _ => e.C_orig.border)

/-- The compressed CA -/
def C : CellAutomaton e.α？ (SingleOrCompressed e.β e.k) := {
  Q := SingleOrCompressed e.C_orig.Q e.k
  δ := e.δ'
  embed := fun a => match a with
    | some a' => single (e.C_orig.embed (some a'))
    | none    => e.border'
  project := fun q => match q with
    | single s => single (e.C_orig.project s)
    | compressed w => compressed (fun j => e.C_orig.project (w j))
}

@[simp] lemma C_border : e.C.border = e.border' := rfl

lemma C_left_indep : e.C.left_independent := by
  intro q1 q2 q3 q1'
  simp only [C, δ']

lemma C_quiescent : e.C.quiescent e.C.border := by
  unfold CellAutomaton.quiescent CellAutomaton.quiescent_set
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  simp only [Set.mem_singleton_iff] at ha hb hc
  subst ha hb hc
  show e.δ' e.border' e.border' e.border' = e.border'
  simp only [δ', border']
  congr 1
  exact e.foldLeft_border

/-! ## Time mapping and arithmetic -/

/-- General time mapping: at word position i, compressed time t, component j.
    `origTimeAt t n i j = k·t − (k−1)·(n−i) + j` -/
def origTimeAt (t : ℕ) (n : ℕ) (i : ℕ) (j : Fin e.k) : ℤ :=
  (e.k : ℤ) * t - ((e.k - 1 : ℕ) : ℤ) * ((n : ℤ) - i) + j

/-- Position-0 specialisation. -/
def origTime (t : ℕ) (n : ℕ) (j : Fin e.k) : ℤ :=
  e.k * t - (e.k - 1 : ℕ) * n + j

lemma origTimeAt_zero (t n : ℕ) (j : Fin e.k) :
    e.origTimeAt t n 0 j = e.origTime t n j := by simp [origTimeAt, origTime]

lemma origTimeAt_nonneg (t n i : ℕ) (hi : i < n) (ht : t + i ≥ n) (j : Fin e.k) :
    0 ≤ e.origTimeAt t n i j := by
  simp only [origTimeAt]
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  rw [hk1]; nlinarith [e.hk, j.isLt]

lemma origTimeAt_step (t n i : ℕ) (j : Fin e.k) :
    e.origTimeAt (t + 1) n i j = e.origTimeAt t n i j + e.k := by
  simp only [origTimeAt]; push_cast; ring

lemma origTimeAt_succ_j (t n i : ℕ) (j : Fin e.k) (hj : j.val + 1 < e.k) :
    e.origTimeAt t n i ⟨j.val + 1, hj⟩ = e.origTimeAt t n i j + 1 := by
  simp only [origTimeAt]; push_cast; ring

/-- Last component at i equals first component at i+1 -/
lemma origTimeAt_last_eq_neighbor_zero (t n i : ℕ) (hi : i + 1 ≤ n) :
    e.origTimeAt t n i ⟨e.k - 1, by have := e.hk; omega⟩ =
    e.origTimeAt t n (i + 1) ⟨0, by have := e.hk; omega⟩ := by
  simp only [origTimeAt]; push_cast
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  rw [hk1]; ring

lemma origTime_step (t n : ℕ) (j : Fin e.k) :
    e.origTime (t + 1) n j = e.origTime t n j + e.k := by
  simp only [origTime]; push_cast; ring

lemma origTime_succ_j (t n : ℕ) (j : Fin e.k) (hj : j.val + 1 < e.k) :
    e.origTime t n ⟨j.val + 1, hj⟩ = e.origTime t n j + 1 := by
  simp only [origTime]; push_cast; ring

/-! ## Border and single-phase lemmas -/

lemma C_orig_border_stays (w : Word e.α) (i : ℤ) (hi : i ≥ w.length) (t : ℕ) :
    e.C_orig.nextt (↑w) t i = e.C_orig.border :=
  CellAutomaton.border_stays_right e.C_orig e.h_left_indep e.h_quiescent w i hi t

theorem border_stays (w : Word e.α) (i : ℤ) (hi : i ≥ w.length) (t : ℕ) :
    e.C.nextt (↑w) t i = e.border' := by
  rw [← e.C_border]
  exact CellAutomaton.border_stays_right e.C e.C_left_indep e.C_quiescent w i hi t

/-- Single phase: for t + i < n, position i tracks the original CA. -/
theorem spec_single (w : Word e.α) (i : ℕ) (hi : i < w.length)
    (t : ℕ) (ht : t + i < w.length) :
    e.C.nextt (↑w) t (↑i) = single (e.C_orig.nextt (↑w) t (↑i)) := by
  induction t with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, word_to_config, C]
    split_ifs with h
    · rfl
    · exfalso; apply h; constructor <;> omega
  | succ t iht =>
    have ht_prev : t + i < w.length := by omega
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply, iht ht_prev]
    by_cases hr : i + 1 < w.length
    · -- right neighbor also single
      have : t + (i + 1) < w.length := by omega
      have h_r := spec_single w (i + 1) hr t this
      rw [show (↑i + 1 : ℤ) = ↑(i + 1) from by push_cast; ring] at *
      rw [h_r]
      -- LHS: δ'(_, single(s_i), single(s_{i+1})) = single(δ₂ s_i s_{i+1})
      simp only [C, δ']
      congr 1
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      exact (e.δ₂_eq _ _ _).symm
    · -- right neighbor is border: unreachable (t+1 + i < n and i+1 ≥ n implies t < 0)
      omega

/-! ## Compressed phase: the main specification

State-level invariant: for 0 ≤ i < n and t ≥ n − i, the state is `compressed v`
where `v j = C_orig.nextt w (origTimeAt t n i j).toNat i`.

Proved by induction on d = n − i (distance from border), then on time. -/

theorem spec_compressed_nextt (w : Word e.α) (hw : w.length > 0)
    (i : ℕ) (hi : i < w.length) (t : ℕ) (ht : t + i ≥ w.length) :
    ∃ v : Fin e.k → e.C_orig.Q,
      e.C.nextt (↑w) t (↑i) = compressed v ∧
      ∀ j : Fin e.k, v j = e.C_orig.nextt (↑w) (e.origTimeAt t w.length i j).toNat (↑i) := by
  /-
  Proof strategy: double induction on (d, t) where d = w.length - i.
  - Base (d = 0): impossible since i < w.length.
  - d → d+1: fix position i with w.length - i = d + 1.
    Inner induction on t:
    - t = 0: impossible since 0 + i ≥ n and i < n.
    - t → t+1:
      Case 1 (t + i ≥ n, steady state):
        Position i at time t is compressed (inner IH).
        Position i+1 at time t is compressed (outer IH on d, any time).
        Apply foldLeft_nextt to advance k steps.
      Case 2 (t + i < n, first compression):
        Position i at time t is single (spec_single).
        Position i+1 at time t is compressed (outer IH on d).
        Apply foldLeft_nextt with T = t.
  Each case uses origTimeAt arithmetic and foldLeft_nextt to connect
  the fold output to C_orig.nextt at the correct time.
  -/
  sorry

/-! ## Main Specification -/

theorem spec (w : Word e.α) (hw : w.length > 0) (t : ℕ) (ht : t ≥ w.length) (j : Fin e.k) :
    (e.C.comp (↑w) t 0).getComponent j =
    e.C_orig.comp (↑w) (e.k * t - (e.k - 1 : ℕ) * w.length + j : ℤ).toNat 0 := by
  obtain ⟨v, hv_eq, hv_all⟩ := e.spec_compressed_nextt w hw 0 hw t (by omega)
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold, Function.comp_apply]
  simp only [Nat.cast_zero] at hv_eq
  rw [hv_eq]; show e.C_orig.project (v j) = _
  rw [hv_all j]; congr 1 <;> simp [origTimeAt]

/-! ## Time arithmetic for the speedup result -/

theorem origTime_at_2n_1 (n : ℕ) (hn : n ≥ 1) :
    e.origTime (2 * (n - 1)) n ⟨0, by have := e.hk; omega⟩ = (e.k + 1) * n - 2 * e.k := by
  simp only [origTime, Nat.cast_zero, add_zero]
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  have h2 : ((2 * (n - 1) : ℕ) : ℤ) = 2 * n - 2 := by omega
  rw [hk1, h2]; ring

theorem speedup_sufficient (n : ℕ) (hn : n ≥ e.k) :
    (e.k + 1 : ℤ) * n - 2 * e.k ≥ e.k * (n - 1) := by
  nlinarith [e.hk]

theorem speedup_small_n (n : ℕ) (hn : 1 ≤ n) (hn' : n < e.k) :
    e.origTime (2 * (n - 1)) n ⟨e.k - n, by omega⟩ = e.k * (n - 1) := by
  simp only [origTime]
  have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by have := e.hk1; omega
  have hkn : ((e.k - n : ℕ) : ℤ) = (e.k : ℤ) - n := by omega
  have h2 : ((2 * (n - 1) : ℕ) : ℤ) = 2 * n - 2 := by omega
  rw [hk1, hkn, h2]; ring

end RightBorderSpeedupOCA

/-!
## RightBorderSpeedup (without quiescence requirement)

Composes with `QuiescentBorderLeftIndep` internally.
-/

structure RightBorderSpeedup where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β
  k : ℕ
  hk : k ≥ 2
  h_left_indep : C_orig.left_independent

attribute [instance] RightBorderSpeedup._inst_α
attribute [instance] RightBorderSpeedup._inst_β

namespace RightBorderSpeedup

variable (e : RightBorderSpeedup)

def pb : QuiescentBorderLeftIndep :=
  { C_orig := e.C_orig, h_left_indep := e.h_left_indep }

def speedup : RightBorderSpeedupOCA :=
  { C_orig := e.pb.C
    k := e.k
    hk := e.hk
    h_left_indep := e.pb.C_left_indep
    h_quiescent := e.pb.C_border_quiescent }

def C := e.speedup.C

lemma C_left_indep : e.C.left_independent := e.speedup.C_left_indep

theorem spec (w : Word e.α) (hw : w.length > 0) (t : ℕ) (ht : t ≥ w.length) (j : Fin e.k) :
    (e.C.comp (↑w) t 0).getComponent j =
    e.C_orig.comp (↑w) (e.k * t - (e.k - 1 : ℕ) * w.length + j : ℤ).toNat 0 := by
  -- e.C = e.speedup.C by definition
  show (e.speedup.C.comp (↑w) t 0).getComponent j = _
  have h := e.speedup.spec w hw t ht j
  set T := (e.k * t - (e.k - 1 : ℕ) * w.length + j : ℤ).toNat
  have h_pb := e.pb.spec w hw T (0 : ℤ)
  have h_in_cone : (0 : ℤ) ∈ WordConeLeftIndep w T := by
    rw [WordConeLeftIndep_mem]; constructor <;> omega
  rw [if_pos h_in_cone] at h_pb
  -- h : getComponent (speedup.C.comp w t 0) j = speedup.C_orig.comp w T 0
  --   = pb.C.comp w T 0  (by definition)
  -- h_pb : pb.C.comp w T 0 = C_orig.comp w T 0
  exact h.trans h_pb

end RightBorderSpeedup

/-!
## Speedup from k·(n−1) to 2·(n−1)

**Note:** The language-equality proof requires acceptance stability (the original CA's
output at position 0 doesn't change after the acceptance time). This property is left
as `sorry`; it is a separate concern from the compression construction.
-/

lemma speedup_k_to_2 {α : Type} [Alphabet α] {k : ℕ} (hk : k ≥ 2)
    (C : tCellAutomaton (.lt_center k) α) (hLI : C.left_independent) :
    ∃ C' : tCellAutomaton .time_2n_center α, C'.left_independent ∧ C'.L = C.L := by
  let e : RightBorderSpeedup := {
    C_orig := C.toCellAutomaton
    k := k
    hk := hk
    h_left_indep := hLI
  }
  let project_bool : SingleOrCompressed Bool k → Bool := fun s => match s with
    | .single b => b
    | .compressed w => w ⟨0, by omega⟩
  let C'_CA : CellAutomaton (Option α) Bool := {
    Q := e.C.Q
    δ := e.C.δ
    embed := e.C.embed
    project := project_bool ∘ e.C.project
  }
  let C' : tCellAutomaton .time_2n_center α := { toCellAutomaton := C'_CA }
  exact ⟨C', e.C_left_indep, by sorry⟩

/-!
## Main Result: OCA_2n = OCA_lt
-/

section OCA_2n_eq_lt

variable (α : Type) [Alphabet α]

lemma OCA_2n_subset_OCA_lt : ℒ (OCA_2n α) ⊆ ℒ (OCA_lt α) := by
  intro L ⟨⟨C, hLI⟩, hCL⟩
  exact ⟨⟨2, C, hLI⟩, hCL⟩

lemma OCA_rt_subset_OCA_2n : ℒ (OCA_rt α) ⊆ ℒ (OCA_2n α) := by sorry

lemma OCA_lt_subset_OCA_2n : ℒ (OCA_lt α) ⊆ ℒ (OCA_2n α) := by
  intro L ⟨⟨c, ⟨C, hLI⟩⟩, hCL⟩
  rcases Nat.lt_or_ge c 2 with hc_small | hc_ge2
  · -- c < 2: real-time or trivial — delegate to OCA_rt ⊆ OCA_2n
    -- For c = 0 or c = 1, the OCA accepts in ≤ (n-1) time, making it real-time-equivalent
    sorry
  · obtain ⟨C', hC'_LI, hC'_L⟩ := speedup_k_to_2 hc_ge2 C hLI
    exact ⟨⟨C', hC'_LI⟩, by simp only [DefinesLanguage.L] at hCL ⊢; rw [hCL, ← hC'_L]⟩

theorem OCA_2n_eq_OCA_lt : ℒ (OCA_2n α) = ℒ (OCA_lt α) :=
  Set.Subset.antisymm (OCA_2n_subset_OCA_lt α) (OCA_lt_subset_OCA_2n α)

end OCA_2n_eq_lt

end CellularAutomatas
