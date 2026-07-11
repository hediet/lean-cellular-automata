import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.border
import CellularAutomatas.proofs.constructions.basic_ca_id
import CellularAutomatas.proofs.constructions.border_quiescent_left_independent
import CellularAutomatas.proofs.time_constructible.latched_ca

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
inductive RightSingleOrCompressed (β : Type) (k : ℕ) where
  | single (q : β) : RightSingleOrCompressed β k
  | compressed (w : Fin k → β) : RightSingleOrCompressed β k
deriving DecidableEq

namespace RightSingleOrCompressed

variable {β : Type} {k : ℕ}

instance [Fintype β] : Fintype (RightSingleOrCompressed β k) :=
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

instance [Inhabited β] : Inhabited (RightSingleOrCompressed β k) := ⟨single default⟩

instance [Alphabet β] : Alphabet (RightSingleOrCompressed β k) := {}

/-- Get component j from compressed, or the single value broadcast -/
def getComponent (s : RightSingleOrCompressed β k) (j : Fin k) : β :=
  match s with
  | single q => q
  | compressed w => w j

end RightSingleOrCompressed

open RightSingleOrCompressed

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
    simpa only [Nat.add_assoc] using this
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
def δ' (_a b c : RightSingleOrCompressed e.C_orig.Q e.k) : RightSingleOrCompressed e.C_orig.Q e.k :=
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
def border' : RightSingleOrCompressed e.C_orig.Q e.k := compressed (fun _ => e.C_orig.border)

/-- The compressed CA -/
def C : CellAutomaton e.α？ (RightSingleOrCompressed e.β e.k) := {
  Q := RightSingleOrCompressed e.C_orig.Q e.k
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
lemma origTimeAt_last_eq_neighbor_zero (t n i : ℕ) :
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

theorem spec_compressed_nextt (w : Word e.α)
    (i : ℕ) (hi : i < w.length) (t : ℕ) (ht : t + i ≥ w.length) :
    ∃ v : Fin e.k → e.C_orig.Q,
      e.C.nextt (↑w) t (↑i) = compressed v ∧
      ∀ j : Fin e.k, v j = e.C_orig.nextt (↑w) (e.origTimeAt t w.length i j).toNat (↑i) := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    have h_right_ready : t + (i + 1) ≥ w.length := by omega
    have h_right : ∃ rightValues : Fin e.k → e.C_orig.Q,
        e.C.nextt (↑w) t (↑(i + 1)) = compressed rightValues ∧
        ∀ j : Fin e.k,
          rightValues j = e.C_orig.nextt (↑w)
            (e.origTimeAt t w.length (i + 1) j).toNat (↑(i + 1)) := by
      by_cases hi_right : i + 1 < w.length
      · exact ih (i + 1) hi_right h_right_ready
      · have hi_boundary : i + 1 = w.length := by omega
        refine ⟨fun _ => e.C_orig.border, ?_, ?_⟩
        · have h_border := e.border_stays w (i + 1) (by omega) t
          simpa [border'] using h_border
        · intro j
          exact (e.C_orig_border_stays w (i + 1) (by omega)
            (e.origTimeAt t w.length (i + 1) j).toNat).symm
    obtain ⟨rightValues, h_right_state, h_right_values⟩ := h_right
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    rw [show (i : ℤ) + 1 = (i + 1 : ℕ) by omega, h_right_state]
    by_cases h_mid_ready : t + i ≥ w.length
    · obtain ⟨midValues, h_mid_state, h_mid_values⟩ :=
        ih i hi h_mid_ready
      rw [h_mid_state]
      simp only [C, δ']
      refine ⟨e.foldLeft
        (midValues ⟨e.k - 1, by have := e.hk; omega⟩) rightValues, rfl, ?_⟩
      intro j
      let last : Fin e.k := ⟨e.k - 1, by have := e.hk; omega⟩
      let baseTime : ℕ := (e.origTimeAt t w.length i last).toNat
      have h_base_nonneg : 0 ≤ e.origTimeAt t w.length i last :=
        e.origTimeAt_nonneg t w.length i hi h_mid_ready last
      have h_q : midValues last =
          e.C_orig.nextt (↑w) baseTime (↑i) := by
        exact h_mid_values last
      have h_right_time : ∀ m : Fin e.k,
          (e.origTimeAt t w.length (i + 1) m).toNat = baseTime + m.val := by
        intro m
        have h_time : e.origTimeAt t w.length (i + 1) m =
            e.origTimeAt t w.length i last + m.val := by
          simp only [origTimeAt, last]
          push_cast
          have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by
            have := e.hk1
            omega
          rw [hk1]
          ring
        have h_neighbor_nonneg :
            0 ≤ e.origTimeAt t w.length (i + 1) m := by
          rw [h_time]
          positivity
        dsimp only [baseTime]
        omega
      have h_w : ∀ m : Fin e.k, rightValues m =
          e.C_orig.nextt (↑w) (baseTime + m.val) ((i : ℤ) + 1) := by
        intro m
        rw [h_right_values m, h_right_time m]
        congr 1
      have h_fold := e.foldLeft_nextt w (i : ℤ) baseTime
        (midValues last) h_q rightValues h_w j
      have h_target_nonneg :
          0 ≤ e.origTimeAt (t + 1) w.length i j :=
        e.origTimeAt_nonneg (t + 1) w.length i hi (by omega) j
      have h_target_time :
          (e.origTimeAt (t + 1) w.length i j).toNat =
            baseTime + j.val + 1 := by
        have h_time : e.origTimeAt (t + 1) w.length i j =
            e.origTimeAt t w.length i last + j.val + 1 := by
          simp only [origTimeAt, last]
          push_cast
          have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by
            have := e.hk1
            omega
          rw [hk1]
          ring
        dsimp only [baseTime]
        omega
      rw [h_target_time]
      exact h_fold
    · have h_mid_single : t + i < w.length := by omega
      have h_mid_state := e.spec_single w i hi t h_mid_single
      rw [h_mid_state]
      simp only [C, δ']
      refine ⟨e.foldLeft (e.C_orig.nextt (↑w) t (↑i)) rightValues,
        rfl, ?_⟩
      intro j
      have h_boundary_time : t + i + 1 = w.length := by omega
      have h_right_time : ∀ m : Fin e.k,
          (e.origTimeAt t w.length (i + 1) m).toNat = t + m.val := by
        intro m
        have h_time : e.origTimeAt t w.length (i + 1) m = t + m.val := by
          simp only [origTimeAt]
          push_cast
          have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by
            have := e.hk1
            omega
          rw [hk1]
          nlinarith
        have h_neighbor_nonneg :
            0 ≤ e.origTimeAt t w.length (i + 1) m := by
          rw [h_time]
          positivity
        omega
      have h_w : ∀ m : Fin e.k, rightValues m =
          e.C_orig.nextt (↑w) (t + m.val) ((i : ℤ) + 1) := by
        intro m
        rw [h_right_values m, h_right_time m]
        congr 1
      have h_fold := e.foldLeft_nextt w (i : ℤ) t
        (e.C_orig.nextt (↑w) t (↑i)) rfl rightValues h_w j
      have h_target_nonneg :
          0 ≤ e.origTimeAt (t + 1) w.length i j :=
        e.origTimeAt_nonneg (t + 1) w.length i hi (by omega) j
      have h_target_time :
          (e.origTimeAt (t + 1) w.length i j).toNat = t + j.val + 1 := by
        have h_time : e.origTimeAt (t + 1) w.length i j = t + j.val + 1 := by
          simp only [origTimeAt]
          push_cast
          have hk1 : ((e.k - 1 : ℕ) : ℤ) = (e.k : ℤ) - 1 := by
            have := e.hk1
            omega
          rw [hk1]
          nlinarith
        omega
      rw [h_target_time]
      exact h_fold

/-! ## Main Specification -/

theorem spec (w : Word e.α) (hw : w.length > 0) (t : ℕ) (ht : t ≥ w.length) (j : Fin e.k) :
    (e.C.comp (↑w) t 0).getComponent j =
    e.C_orig.comp (↑w) (e.k * t - (e.k - 1 : ℕ) * w.length + j : ℤ).toNat 0 := by
  obtain ⟨v, hv_eq, hv_all⟩ := e.spec_compressed_nextt w 0 hw t (by omega)
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold]
  simp only [Nat.cast_zero] at hv_eq
  rw [hv_eq]; show e.C_orig.project (v j) = _
  rw [hv_all j]
  congr 1

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

/-! ## Left-independent time extension -/

private lemma identityTimerCA_left_independent :
    identityTimerCA.left_independent := by
  intro _ _ _ _
  rfl

private def holdInitialOCA {α : Type} [Alphabet α]
    (C : LCellAutomaton α) : LCellAutomaton α :=
  ((CellAutomaton.idCA C.Q).map_embed C.embed).map_project C.project

private lemma holdInitialOCA_spec {α : Type} [Alphabet α]
    (C : LCellAutomaton α) (w : Word α) (t : ℕ) :
    (holdInitialOCA C).comp ⦋⟬w⟭⦌ t 0 = C.comp ⦋⟬w⟭⦌ 0 0 := by
  change C.project ((CellAutomaton.idCA C.Q).comp
      (CellAutomaton.embed_config
        (C := (CellAutomaton.idCA C.Q).map_embed C.embed) ⟬w⟭) t 0) = _
  rw [CellAutomaton.idCA.comp_spec]
  rfl

private lemma holdInitialOCA_left_independent
    {α : Type} [Alphabet α] (C : LCellAutomaton α) :
    (holdInitialOCA C).left_independent := by
  intro _ _ _ _
  rfl

private lemma TraceKx.C_left_independent_of
    (trace : TraceKx) (h : trace.C_orig.left_independent) :
    trace.C.left_independent := by
  unfold TraceKx.C
  change ∀ (left center right left' : Fin (trace.k + 1) → trace.C_orig.Q),
    @Fin.snoc trace.k (fun _ => trace.C_orig.Q) (Fin.tail center)
        (trace.C_orig.δ (left (Fin.last trace.k))
          (center (Fin.last trace.k)) (right (Fin.last trace.k))) =
      @Fin.snoc trace.k (fun _ => trace.C_orig.Q) (Fin.tail center)
        (trace.C_orig.δ (left' (Fin.last trace.k))
          (center (Fin.last trace.k)) (right (Fin.last trace.k)))
  intro left center right left'
  rw [h]

private lemma latchedCA_left_independent
    {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (time : ℕ → ℕ) (tc : TimeConstructible time)
    (hC : C.left_independent) (hTimer : tc.timer.left_independent) :
    (latchedCA C time tc).left_independent := by
  intro left center right left'
  unfold latchedCA
  have h_ca := hC left.ca_state center.ca_state right.ca_state left'.ca_state
  have h_timer := hTimer left.timer_state center.timer_state right.timer_state
    left'.timer_state
  simp only [h_ca, h_timer]

private lemma latchedCA_one_left_independent
    {α : Type} [Alphabet α] (C : LCellAutomaton α)
    (hC : C.left_independent) :
    (latchedCA_k C id identityTimeConstructible 1).left_independent := by
  let trace : TraceKx := {
    k := 1
    α := Option α
    β := Bool
    C_orig := C
  }
  have h_trace : trace.C.left_independent :=
    TraceKx.C_left_independent_of trace hC
  have h_latched :
      (latchedCA trace.C id identityTimeConstructible).left_independent :=
    latchedCA_left_independent trace.C id identityTimeConstructible h_trace
      identityTimerCA_left_independent
  change (latchedCA trace.C id identityTimeConstructible).left_independent
  exact h_latched

/-!
## Speedup from k·(n−1) to 2·(n−1)

For coefficient `k ≥ 3`, compress by `k - 1` and read component `k - 2`.
At time `2(n - 1)`, that component represents exactly original time `k(n - 1)`:

`(k - 1) · 2(n - 1) - (k - 2)n + (k - 2) = k(n - 1)`.
-/

lemma speedup_k_to_2 {α : Type} [Alphabet α] {k : ℕ} (hk : k ≥ 3)
  (C : tCellAutomaton (.lt_left k) α) (hLI : C.left_independent) :
  ∃ C' : tCellAutomaton .time_2n_left α, C'.left_independent ∧ C'.L = C.L := by
  let e : RightBorderSpeedup := {
    C_orig := C.toCellAutomaton
    k := k - 1
    hk := by omega
    h_left_indep := hLI
  }
  let outputIndex : Fin (k - 1) := ⟨k - 2, by omega⟩
  let C'_CA : CellAutomaton (Option α) Bool := {
    Q := e.C.Q
    δ := e.C.δ
    embed := e.C.embed
    project := fun state => (e.C.project state).getComponent outputIndex
  }
  let C' : tCellAutomaton .time_2n_left α := { toCellAutomaton := C'_CA }
  refine ⟨C', e.C_left_indep, ?_⟩
  ext w
  show C'.accepts w = true ↔ C.accepts w = true
  change C'_CA.comp (↑w) (2 * (w.length - 1)) 0 = true ↔
    C.toCellAutomaton.comp (↑w) (k * (w.length - 1)) 0 = true
  by_cases hw : 2 ≤ w.length
  · have h_spec := e.spec w (by omega) (2 * (w.length - 1)) (by omega) outputIndex
    change (e.C.comp (↑w) (2 * (w.length - 1)) 0).getComponent outputIndex = true ↔
      C.toCellAutomaton.comp (↑w) (k * (w.length - 1)) 0 = true
    rw [h_spec]
    have h_time :
        (((e.k : ℤ) * (2 * (w.length - 1) : ℕ) -
          ((e.k - 1 : ℕ) : ℤ) * w.length + (outputIndex : ℤ)).toNat) =
          k * (w.length - 1) := by
      dsimp only [e, outputIndex]
      change ((((k - 1 : ℕ) : ℤ) * ((2 * (w.length - 1) : ℕ) : ℤ) -
        (((k - 1 : ℕ) - 1 : ℕ) : ℤ) * w.length +
        ((k - 2 : ℕ) : ℤ)).toNat) = k * (w.length - 1)
      have h_int : ((k - 1 : ℕ) : ℤ) * ((2 * (w.length - 1) : ℕ) : ℤ) -
          (((k - 1 : ℕ) - 1 : ℕ) : ℤ) * w.length +
          ((k - 2 : ℕ) : ℤ) = (k * (w.length - 1) : ℕ) := by
        push_cast
        have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
        have hk2 : (((k - 1 : ℕ) - 1 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
        have hk3 : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
        have hn1 : ((w.length - 1 : ℕ) : ℤ) = (w.length : ℤ) - 1 := by omega
        rw [hk1, hk2, hk3, hn1]
        ring
      rw [h_int, Int.toNat_natCast]
    rw [h_time]
  · have hw_small : w.length ≤ 1 := by omega
    have hn_sub : w.length - 1 = 0 := by omega
    rw [hn_sub]
    simp only [mul_zero]
    change (e.C.comp (↑w) 0 0).getComponent outputIndex = true ↔
      C.toCellAutomaton.comp (↑w) 0 0 = true
    have h_zero : (e.C.comp (↑w) 0 0).getComponent outputIndex =
        C.toCellAutomaton.comp (↑w) 0 0 := by
      simp only [CellAutomaton.comp_apply, CellAutomaton.nextt_zero,
        CellAutomaton.embed_config_apply]
      unfold RightBorderSpeedup.C RightBorderSpeedup.speedup
        RightBorderSpeedup.pb RightBorderSpeedupOCA.C
      cases word_to_config w 0 <;> rfl
    rw [h_zero]

/-!
## Main Result: OCA_2n = OCA_lt
-/

section OCA_2n_eq_lt

variable (α : Type) [Alphabet α]

lemma OCA_2n_subset_OCA_lt : ℒ (OCA_2n α) ⊆ ℒ (OCA_lt α) := by
  intro L ⟨⟨C, hLI⟩, hCL⟩
  exact ⟨⟨2, C, hLI⟩, hCL⟩

lemma OCA_rt_subset_OCA_2n : ℒ (OCA_rt α) ⊆ ℒ (OCA_2n α) := by
  intro L ⟨⟨C, hLI⟩, hCL⟩
  let delayedCA : CA_2n α := {
    toCellAutomaton :=
      latchedCA_k C.toCellAutomaton id identityTimeConstructible 1
  }
  refine ⟨⟨delayedCA, latchedCA_one_left_independent C.toCellAutomaton hLI⟩, ?_⟩
  rw [hCL]
  ext w
  show C.toCellAutomaton.comp ⦋⟬w⟭⦌ (w.length - 1) 0 = true ↔
    (latchedCA_k C.toCellAutomaton id identityTimeConstructible 1).comp
      ⦋⟬w⟭⦌ (2 * (w.length - 1)) 0 = true
  by_cases hn : w.length ≥ 2
  · have h_spec := latchedCA_k_spec C.toCellAutomaton id
      identityTimeConstructible 1 w (w.length - 2)
    simp only [id_eq] at h_spec
    have h_time : w.length + (w.length - 2) = 2 * (w.length - 1) := by
      omega
    rw [h_time] at h_spec
    rw [h_spec (by omega) (by omega)]
  · have h_time_2n : 2 * (w.length - 1) = 0 := by omega
    have h_time_rt : w.length - 1 = 0 := by omega
    rw [h_time_2n, h_time_rt]
    simp only [CellAutomaton.comp_apply, CellAutomaton.nextt_zero]
    unfold latchedCA_k CellAutomaton.map_project CellAutomaton.embed_config
    simp only [Function.comp, latchedCA, TraceKx.C]
    by_cases hw : w.length = 0
    · simp only [word_to_config, hw, id_eq]
      split_ifs <;> simp_all
    · have hw_one : w.length = 1 := by omega
      simp only [word_to_config, hw_one, id_eq]
      split_ifs with h_in <;> simp_all [Option.getD_none]

lemma OCA_lt_subset_OCA_2n : ℒ (OCA_lt α) ⊆ ℒ (OCA_2n α) := by
  intro L ⟨⟨c, ⟨C, hLI⟩⟩, hCL⟩
  rcases Nat.lt_or_ge c 2 with hc_small | hc_ge2
  · rcases Nat.eq_zero_or_pos c with hc_zero | hc_pos
    · subst c
      let heldCA : CA_2n α := {
        toCellAutomaton := holdInitialOCA C.toCellAutomaton
      }
      refine ⟨⟨heldCA, holdInitialOCA_left_independent C.toCellAutomaton⟩, ?_⟩
      calc
        L = C.L := hCL
        _ = heldCA.L := by
          ext w
          show C.toCellAutomaton.comp ⦋⟬w⟭⦌ (0 * (w.length - 1)) 0 = true ↔
            (holdInitialOCA C.toCellAutomaton).comp
              ⦋⟬w⟭⦌ (2 * (w.length - 1)) 0 = true
          rw [holdInitialOCA_spec]
          simp
    · have hc_one : c = 1 := by omega
      subst c
      let rtCA : CA_rt α := { toCellAutomaton := C.toCellAutomaton }
      apply OCA_rt_subset_OCA_2n α
      refine ⟨⟨rtCA, hLI⟩, ?_⟩
      calc
        L = C.L := hCL
        _ = rtCA.L := by
          ext w
          show C.toCellAutomaton.comp ⦋⟬w⟭⦌ (1 * (w.length - 1)) 0 = true ↔
            C.toCellAutomaton.comp ⦋⟬w⟭⦌ (w.length - 1) 0 = true
          simp
  · by_cases hc_two : c = 2
    · subst c
      let C' : CA_2n α := { toCellAutomaton := C.toCellAutomaton }
      exact ⟨⟨C', hLI⟩, hCL⟩
    · have hc_ge3 : c ≥ 3 := by omega
      obtain ⟨C', hC'_LI, hC'_L⟩ := speedup_k_to_2 hc_ge3 C hLI
      exact ⟨⟨C', hC'_LI⟩,
        by simp only [DefinesLanguage.L] at hCL ⊢; rw [hCL, ← hC'_L]⟩

theorem OCA_2n_eq_OCA_lt : ℒ (OCA_2n α) = ℒ (OCA_lt α) :=
  Set.Subset.antisymm (OCA_2n_subset_OCA_lt α) (OCA_lt_subset_OCA_2n α)

end OCA_2n_eq_lt

end CellularAutomatas
