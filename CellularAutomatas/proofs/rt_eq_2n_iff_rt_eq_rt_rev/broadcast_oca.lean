import CellularAutomatas.defs

namespace CellularAutomatas

open CellAutomaton

/-!
# Broadcast OCA Construction

Given a left-independent LCellAutomaton `C_orig : CellAutomaton τ？ β`, construct CA `C` such that:
  `C.comp c (2*T + r) (-(T : ℤ) - r) = C_orig.comp c (2*T) (-(T : ℤ))`

## Key insight:
- The "main signal" (r=0) is at position -T at time 2T — moves left at speed 1/2
- For fixed T, increasing r traces a left-diagonal from (2T, -T)
- We capture `C_orig.project` at the main signal, then propagate diagonally

## State space: `C_orig.Q × Signal × Option β`
- First component: runs C_orig (using left-independence)
- Signal ∈ {0=waiting, 1=ready, 2=fired}: marks main signal arrival
- Option β: captured result, propagated along left-diagonals

## Signal behavior:
- Inner positions (some x) start with signal=2 (fired) and memo=some(initial projection)
- Border positions (none) start with signal=0 (waiting) and memo=none
- Signal propagates left at speed 1/2: waiting → ready (when right is fired) → fired
- At ready → fired transition: capture C_orig's projected value
- Memo propagates diagonally (left and down) from right neighbor
-/

structure BroadcastOCA where
  {τ β : Type}
  [_inst_τ : Alphabet τ]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton τ？ β
  h_left_indep : C_orig.left_independent

attribute [instance] BroadcastOCA._inst_τ
attribute [instance] BroadcastOCA._inst_β

namespace BroadcastOCA

variable (e : BroadcastOCA)

/-- Signal state: 0=waiting, 1=ready (fires next step), 2=fired -/
abbrev Signal := Fin 3

/-- Signal transition: propagates at speed 1/2 from right to left -/
def signalStep (s_c s_r : Signal) : Signal :=
  if s_c = 2 then 2
  else if s_c = 1 then 2
  else if s_r = 2 then 1
  else 0

/-- Combined state: original state, signal, and memoized result -/
abbrev Q' := e.C_orig.Q × Signal × Option e.β

instance : Fintype e.Q' := inferInstance
instance : DecidableEq e.Q' := inferInstance
instance : Inhabited e.Q' := ⟨(default, 0, none)⟩
instance : Alphabet e.Q' := {}

/-- Since C_orig is left-independent, define two-argument transition -/
def δ₂ (b c : e.C_orig.Q) : e.C_orig.Q := e.C_orig.δ default b c

lemma δ₂_eq (a b c : e.C_orig.Q) : e.C_orig.δ a b c = e.δ₂ b c :=
  e.h_left_indep a b c default

/-- Combined transition function -/
def δ' (_ center right : e.Q') : e.Q' :=
  let (q_c, s_c, m_c) := center
  let (q_r, s_r, m_r) := right
  let new_q := e.δ₂ q_c q_r
  let new_s := signalStep s_c s_r
  -- Capture at main signal (when s_c = 1), otherwise propagate from right
  let new_m := if s_c = 1 then some (e.C_orig.project new_q)
               else if m_r.isSome then m_r
               else m_c
  (new_q, new_s, new_m)

/-- Embed function: border waits, inner fires immediately with initial memo -/
def embed' (a : e.τ？) : e.Q' :=
  match a with
  | none => (e.C_orig.embed none, 0, none)
  | some x => (e.C_orig.embed (some x), 2, some (e.C_orig.project (e.C_orig.embed (some x))))

/-- The constructed CA -/
def C : CellAutomaton e.τ？ e.β where
  Q := e.Q'
  δ := e.δ'
  embed := e.embed'
  project := fun (q, _, m) => m.getD (e.C_orig.project q)

/-- δ' is left-independent (ignores first argument) -/
lemma δ'_left_indep : ∀ a b c a', e.δ' a b c = e.δ' a' b c := by
  intros; rfl

theorem C_left_independent : e.C.left_independent := e.δ'_left_indep

/-! ## Helper definitions and lemmas -/

/-- Helper: extract components from C.nextt -/
def nextt_q (c : Config e.C.Q) (t : ℕ) (p : ℤ) : e.C_orig.Q :=
  (e.C.nextt c t p).1

def nextt_s (c : Config e.C.Q) (t : ℕ) (p : ℤ) : Signal :=
  (e.C.nextt c t p).2.1

def nextt_m (c : Config e.C.Q) (t : ℕ) (p : ℤ) : Option e.β :=
  (e.C.nextt c t p).2.2

/-- The q-component of C tracks C_orig exactly -/
lemma nextt_q_eq (c : Config e.τ？) (t : ℕ) (p : ℤ) :
    e.nextt_q (embed_config (C := e.C) c) t p = e.C_orig.nextt (embed_config c) t p := by
  induction t generalizing p with
  | zero =>
    simp only [nextt_q, nextt_zero, embed_config]
    cases c p <;> rfl
  | succ t ih =>
    -- Unfold definitions to expose the structure
    unfold nextt_q
    simp only [nextt_succ, next, C, δ', δ₂]
    -- LHS: e.C_orig.δ default ((..).1) ((..).1)
    -- RHS: e.C_orig.δ (nextt t (p-1)) (nextt t p) (nextt t (p+1))
    -- By IH, (..).1 = e.C_orig.nextt ... so LHS = e.C_orig.δ default (nextt t p) (nextt t (p+1))
    -- By left-independence, this equals RHS
    have h2 : (e.C.nextt ⦋c⦌ t p).1 = e.C_orig.nextt ⦋c⦌ t p := ih p
    have h3 : (e.C.nextt ⦋c⦌ t (p + 1)).1 = e.C_orig.nextt ⦋c⦌ t (p + 1) := ih (p + 1)
    unfold C at h2 h3
    rw [h2, h3]
    exact e.h_left_indep _ _ _ _

/-! ## Signal behavior lemmas -/

/-- At initial time, border positions have signal=0, inner positions have signal=2 -/
lemma nextt_s_zero (c : Config e.τ？) (p : ℤ) :
    e.nextt_s ⦋c⦌ 0 p = if (c p).isSome then 2 else 0 := by
  simp only [nextt_s, nextt_zero, embed_config, embed', C]
  cases c p <;> rfl

/-- At initial time, inner positions have memo = some (initial projection) -/
lemma nextt_m_zero_inner (c : Config e.τ？) (p : ℤ) (h : (c p).isSome) :
    e.nextt_m ⦋c⦌ 0 p = some (e.C_orig.project (e.C_orig.embed (c p))) := by
  simp only [nextt_m, nextt_zero, embed_config, embed', C]
  cases hcp : c p with
  | none => simp [hcp] at h
  | some x => simp [hcp]

/-- Signal stays at 2 once reached -/
lemma signal_stays_fired (c : Config e.τ？) (t : ℕ) (p : ℤ)
    (h : e.nextt_s ⦋c⦌ t p = 2) : e.nextt_s ⦋c⦌ (t + 1) p = 2 := by
  simp only [nextt_s] at h ⊢
  simp only [nextt_succ, next, C, δ', signalStep]
  simp only [C] at h ⊢
  simp only [h, ite_true]

/-- Signal goes from 1 to 2 in one step -/
lemma signal_ready_to_fired (c : Config e.τ？) (t : ℕ) (p : ℤ)
    (h : e.nextt_s ⦋c⦌ t p = 1) : e.nextt_s ⦋c⦌ (t + 1) p = 2 := by
  simp only [nextt_s] at h ⊢
  simp only [nextt_succ, next, C, δ', signalStep]
  have h_ne2 : (e.C.nextt ⦋c⦌ t p).2.1 ≠ 2 := by
    simp only [C] at h ⊢
    intro heq; rw [heq] at h; exact absurd h (by intro hc; exact absurd (Fin.ext_iff.mp hc) (by omega))
  simp only [C] at h h_ne2 ⊢
  simp only [h_ne2, ite_false, h, ite_true]
  rfl

/-- Signal at position -k before time 2k-1 is 0 (only needs hborder) -/
lemma signal_before_ready (c : Config e.τ？) (k : ℕ) (hk : k ≥ 1) (t : ℕ) (ht : t < 2 * k - 1)
    (hborder : ∀ p : ℤ, p < 0 → (c p) = none) :
    e.nextt_s ⦋c⦌ t (-(k : ℤ)) = 0 := by
  -- Induction on t
  induction t with
  | zero =>
    simp only [nextt_s, nextt_zero, embed_config, embed', C]
    have h : c (-(k : ℤ)) = none := hborder (-(k : ℤ)) (by omega)
    simp [h]
  | succ t' ih =>
    simp only [nextt_s, nextt_succ, next, C, δ', signalStep]
    -- Signal at -k at time t' is 0
    have hs_c : (e.C.nextt ⦋c⦌ t' (-(k : ℤ))).2.1 = 0 := by
      have ht' : t' < 2 * k - 1 := by omega
      exact ih ht'
    -- Signal at -(k-1) at time t' is not 2
    have hs_r_ne_2 : (e.C.nextt ⦋c⦌ t' (-(k : ℤ) + 1)).2.1 ≠ 2 := by
      intro heq
      by_cases hk1 : k = 1
      · omega  -- k=1, need t'+1 < 1, impossible
      · have hkm1 : k - 1 ≥ 1 := by omega
        have h_pos : -(k : ℤ) + 1 = -((k - 1 : ℕ) : ℤ) := by push_cast; omega
        rw [h_pos] at heq
        have ht'_bound : t' ≤ 2 * (k - 1) - 1 := by omega
        by_cases ht'_lt : t' < 2 * (k - 1) - 1
        · have h := signal_before_ready c (k - 1) hkm1 t' ht'_lt hborder
          simp only [nextt_s, C] at h heq
          rw [h] at heq; exact absurd heq (by intro hc; exact absurd (Fin.ext_iff.mp hc) (by omega))
        · have ht'_eq : t' = 2 * (k - 1) - 1 := by omega
          subst ht'_eq
          have h_prev : 2 * (k - 1) - 1 - 1 < 2 * (k - 1) - 1 := by omega
          have h_prev_sig := signal_before_ready c (k - 1) hkm1 (2 * (k - 1) - 1 - 1) h_prev hborder
          simp only [nextt_s, C] at h_prev_sig heq
          have h_time : 2 * (k - 1) - 1 = (2 * (k - 1) - 1 - 1) + 1 := by omega
          rw [h_time, nextt_succ, next] at heq
          simp only [C, δ', signalStep] at heq
          -- Signal at prev time was 0, so signalStep gives 0 or 1, not 2
          simp only [h_prev_sig] at heq
          split at heq
          · contradiction  -- 0 = 2
          · split at heq
            · contradiction  -- 0 = 1
            · split at heq <;> simp at heq
    simp only [C] at hs_c hs_r_ne_2 ⊢
    simp only [hs_c, ↓reduceIte]
    by_cases hr : (e.C.nextt ⦋c⦌ t' (-(k : ℤ) + 1)).2.1 = 2
    · exact absurd hr hs_r_ne_2
    · simp only [C] at hr ⊢; simp [hr]

/-- Signal at position -k (k ≥ 1) is 1 at time 2k-1 and 2 at time 2k -/
lemma signal_ready_and_fires (c : Config e.τ？) (k : ℕ) (hk : k ≥ 1)
    (hborder : ∀ p : ℤ, p < 0 → (c p) = none)
    (h0 : (c 0).isSome) :
    e.nextt_s ⦋c⦌ (2 * k - 1) (-(k : ℤ)) = 1 ∧ e.nextt_s ⦋c⦌ (2 * k) (-(k : ℤ)) = 2 := by
  induction k with
  | zero => omega
  | succ k' ih =>
    match k' with
    | 0 =>
      -- k = 1
      have h_pos : -(((0 : ℕ) + 1 : ℕ) : ℤ) = -1 := by omega
      have h_neg1 : c (-1) = none := hborder (-1) (by omega)
      constructor
      · -- signal at -1 at time 1 is 1
        show e.nextt_s ⦋c⦌ (2 * (0 + 1) - 1) (-(((0 : ℕ) + 1 : ℕ) : ℤ)) = 1
        rw [h_pos]
        simp only [show 2 * (0 + 1) - 1 = 1 by omega]
        unfold nextt_s
        rw [nextt_succ, next]
        simp only [nextt_zero, embed_config, embed', h_neg1]
        -- Unfold C to expose δ', then unfold signalStep
        unfold C δ' signalStep
        -- simplify -1 + 1 = 0
        simp only [show (-1 : ℤ) + 1 = 0 from by omega]
        cases hc0 : c 0 with
        | none => simp [hc0] at h0
        | some x => rfl
      · -- signal at -1 at time 2 is 2
        show e.nextt_s ⦋c⦌ (2 * (0 + 1)) (-(((0 : ℕ) + 1 : ℕ) : ℤ)) = 2
        rw [h_pos]
        simp only [show 2 * (0 + 1) = 2 by omega]
        have h_ready : e.nextt_s ⦋c⦌ 1 (-1) = 1 := by
          unfold nextt_s
          rw [nextt_succ, next]
          simp only [nextt_zero, embed_config, h_neg1]
          unfold C δ' signalStep
          simp only [show (-1 : ℤ) + 1 = 0 from by omega]
          cases hc0 : c 0 with
          | none => simp [hc0] at h0
          | some x => rfl
        exact e.signal_ready_to_fired c 1 (-1) h_ready
    | k'' + 1 =>
      -- k = k'' + 2
      have hk'_ge_1 : k'' + 1 ≥ 1 := by omega
      have ⟨_, h_fires⟩ := ih hk'_ge_1
      have h_before := e.signal_before_ready c (k'' + 2) (by omega) (2 * (k'' + 1)) (by omega) hborder
      have h_pos : -((k'' + 2 : ℕ) : ℤ) + 1 = -(((k'' + 1) : ℕ) : ℤ) := by push_cast; ring
      constructor
      · -- signal at -(k''+2) at time 2(k''+2)-1 is 1
        show e.nextt_s ⦋c⦌ (2 * (k'' + 1 + 1) - 1) (-(((k'' + 1 + 1) : ℕ) : ℤ)) = 1
        have h_time : 2 * (k'' + 1 + 1) - 1 = (2 * (k'' + 1)) + 1 := by omega
        have h_pos2 : -(((k'' + 1 + 1) : ℕ) : ℤ) = -((k'' + 2 : ℕ) : ℤ) := by norm_cast
        rw [h_time, h_pos2]
        -- Express goal and hypotheses in same expanded form
        simp only [nextt_s, nextt_succ, next, C, δ', signalStep] at h_before h_fires ⊢
        rw [h_before, h_pos, h_fires]
        simp [signalStep]
      · -- signal at -(k''+2) at time 2(k''+2) is 2
        show e.nextt_s ⦋c⦌ (2 * (k'' + 1 + 1)) (-(((k'' + 1 + 1) : ℕ) : ℤ)) = 2
        have h_time2 : 2 * (k'' + 1 + 1) = (2 * (k'' + 2) - 1) + 1 := by omega
        have h_pos2 : -(((k'' + 1 + 1) : ℕ) : ℤ) = -((k'' + 2 : ℕ) : ℤ) := by norm_cast
        rw [h_time2, h_pos2]
        have h_ready : e.nextt_s ⦋c⦌ (2 * (k'' + 2) - 1) (-((k'' + 2 : ℕ) : ℤ)) = 1 := by
          have h_time : 2 * (k'' + 2) - 1 = (2 * (k'' + 1)) + 1 := by omega
          rw [h_time]
          simp only [nextt_s, nextt_succ, next, C, δ', signalStep] at h_before h_fires ⊢
          rw [h_before, h_pos, h_fires]
          simp [signalStep]
        exact e.signal_ready_to_fired c (2 * (k'' + 2) - 1) (-((k'' + 2 : ℕ) : ℤ)) h_ready

/-- Signal at position -k (k ≥ 1) is 1 at time 2k-1 -/
lemma signal_ready (c : Config e.τ？) (k : ℕ) (hk : k ≥ 1)
    (hborder : ∀ p : ℤ, p < 0 → (c p) = none)
    (h0 : (c 0).isSome) :
    e.nextt_s ⦋c⦌ (2 * k - 1) (-(k : ℤ)) = 1 :=
  (e.signal_ready_and_fires c k hk hborder h0).1

/-- Signal at position -k (k ≥ 1) is 2 at time 2k -/
lemma signal_fires_at_2k (c : Config e.τ？) (k : ℕ) (hk : k ≥ 1)
    (hborder : ∀ p : ℤ, p < 0 → (c p) = none)
    (h0 : (c 0).isSome) :
    e.nextt_s ⦋c⦌ (2 * k) (-(k : ℤ)) = 2 :=
  (e.signal_ready_and_fires c k hk hborder h0).2

/-! ## Memo behavior lemmas -/

/-- Memo propagates diagonally from right neighbor when signal ≠ 1 -/
lemma memo_propagate (c : Config e.τ？) (t : ℕ) (p : ℤ)
    (h_s_not_1 : e.nextt_s ⦋c⦌ t p ≠ 1)
    (h_m_right : (e.nextt_m ⦋c⦌ t (p + 1)).isSome) :
    e.nextt_m ⦋c⦌ (t + 1) p = e.nextt_m ⦋c⦌ t (p + 1) := by
  simp only [nextt_m, nextt_s] at h_s_not_1 h_m_right ⊢
  rw [nextt_succ, next]
  simp only [C] at h_s_not_1 h_m_right ⊢
  simp only [δ', h_s_not_1, ↓reduceIte, h_m_right, ↓reduceIte]

/-- When signal = 1, memo captures the q-component's projection -/
lemma memo_capture_at_signal (c : Config e.τ？) (t : ℕ) (p : ℤ)
    (h_s_1 : e.nextt_s ⦋c⦌ t p = 1) :
    e.nextt_m ⦋c⦌ (t + 1) p =
    some (e.C_orig.project (e.C.δ (e.C.nextt ⦋c⦌ t (p - 1)) (e.C.nextt ⦋c⦌ t p) (e.C.nextt ⦋c⦌ t (p + 1))).1) := by
  simp only [nextt_m, nextt_s] at h_s_1 ⊢
  rw [nextt_succ, next]
  simp only [C] at h_s_1 ⊢
  simp only [δ', h_s_1, ↓reduceIte]

/-- Main memo diagonal lemma - key for proving the spec -/
lemma memo_diagonal (c : Config e.τ？) (T r : ℕ)
    (hborder : ∀ p : ℤ, p < 0 → (c p) = none)
    (h0 : (c 0).isSome)
    (hT : T ≥ 1) :
    e.nextt_m ⦋c⦌ (2 * T + r) (-(T : ℤ) - r) =
    some (e.C_orig.project (e.C_orig.nextt ⦋c⦌ (2 * T) (-(T : ℤ)))) := by
  -- Induction on r: base case uses signal capture, inductive uses diagonal propagation
  induction r with
  | zero =>
    -- Base case: at time 2T, position -T, signal transitions 1→2 and captures
    simp only [Nat.add_zero, Nat.cast_zero, sub_zero]
    -- At time 2T-1, signal at -T is 1 (ready to fire)
    have h_ready := e.signal_ready c T hT hborder h0
    -- At time 2T, the memo is captured
    have h_time : 2 * T = (2 * T - 1) + 1 := by omega
    -- Rewrite goal to use (2*T-1)+1
    conv_lhs => rw [h_time]
    conv_rhs => rw [h_time]
    -- Use memo_capture_at_signal
    have h_cap := e.memo_capture_at_signal c (2 * T - 1) (-(T : ℤ)) h_ready
    rw [h_cap]
    -- Need to show (e.C.δ ...).1 equals e.C_orig.nextt (2T) (-T)
    -- The key is: (e.C.δ l c r).1 = δ₂ c.1 r.1 = C_orig.δ default c.1 r.1
    -- And by nextt_q_eq: c.1 = C_orig.nextt, r.1 = C_orig.nextt
    -- And by left_indep: C_orig.δ default q_c q_r = C_orig.δ q_l q_c q_r
    congr 1
    -- Show the q-component equals C_orig.nextt
    have hq_c := e.nextt_q_eq c (2 * T - 1) (-(T : ℤ))
    have hq_r := e.nextt_q_eq c (2 * T - 1) (-(T : ℤ) + 1)
    simp only [nextt_q] at hq_c hq_r
    -- (e.C.δ l c r).1 = δ₂ c.1 r.1
    have h_delta_1 : (e.C.δ (e.C.nextt ⦋c⦌ (2 * T - 1) (-(T : ℤ) - 1))
                          (e.C.nextt ⦋c⦌ (2 * T - 1) (-(T : ℤ)))
                          (e.C.nextt ⦋c⦌ (2 * T - 1) (-(T : ℤ) + 1))).1
                  = e.δ₂ (e.C.nextt ⦋c⦌ (2 * T - 1) (-(T : ℤ))).1
                         (e.C.nextt ⦋c⦌ (2 * T - 1) (-(T : ℤ) + 1)).1 := by
      simp only [C, δ']
    rw [h_delta_1, hq_c, hq_r]
    -- δ₂ q_c q_r = C_orig.δ default q_c q_r
    simp only [δ₂]
    -- By left_indep: C_orig.δ default q_c q_r = C_orig.δ q_l q_c q_r for any q_l
    have h_left_indep := e.h_left_indep
    simp only [left_independent] at h_left_indep
    rw [h_left_indep default _ _ (e.C_orig.nextt ⦋c⦌ (2 * T - 1) (-(T : ℤ) - 1))]
    -- Now: C_orig.δ q_l q_c q_r = C_orig.nextt (t+1) p
    -- Expand the RHS with nextt_succ
    conv_rhs => rw [nextt_succ, next]
  | succ r ih =>
    -- Inductive case: memo propagates from right neighbor along diagonal
    -- Position -(T + r + 1) at time 2T + r + 1 gets memo from -(T + r) at time 2T + r
    have h_time : 2 * T + (r + 1) = (2 * T + r) + 1 := by ring
    have h_pos : -(T : ℤ) - ↑(r + 1) = -(T : ℤ) - r - 1 := by push_cast; ring
    rw [h_time, h_pos]
    -- Signal at position -(T+r+1) at time 2T+r is not 1
    -- Signal becomes 1 at time 2(T+r+1) - 1 = 2T + 2r + 1, we're at time 2T + r < 2T + 2r + 1
    have h_s_ne_1 : e.nextt_s ⦋c⦌ (2 * T + r) (-(T : ℤ) - r - 1) ≠ 1 := by
      have h_k_ge_1 : T + r + 1 ≥ 1 := by omega
      have h_t_lt : 2 * T + r < 2 * (T + r + 1) - 1 := by omega
      have h_pos' : -((T + r + 1 : ℕ) : ℤ) = -(T : ℤ) - r - 1 := by push_cast; ring
      have h_eq_0 := e.signal_before_ready c (T + r + 1) h_k_ge_1 (2 * T + r) h_t_lt hborder
      rw [h_pos'] at h_eq_0
      simp [h_eq_0]
    -- Right neighbor at time 2T+r has memo (by IH)
    have h_right_pos : -(T : ℤ) - r - 1 + 1 = -(T : ℤ) - r := by ring
    have h_m_right : (e.nextt_m ⦋c⦌ (2 * T + r) (-(T : ℤ) - r)).isSome := by
      rw [ih]; simp
    rw [← h_right_pos] at h_m_right
    -- Apply propagation lemma
    have h_prop := e.memo_propagate c (2 * T + r) (-(T : ℤ) - r - 1) h_s_ne_1 h_m_right
    rw [h_prop, h_right_pos, ih]

/-! ## Main specification -/

theorem spec (c : Config e.τ？) (T : ℕ) (r : ℕ)
    (hborder : ∀ p : ℤ, p < 0 → (c p) = none)
    (h0 : (c 0).isSome)
    (hT : T ≥ 1) :
    e.C.comp c (2 * T + r) (-(T : ℤ) - r) = e.C_orig.comp c (2 * T) (-(T : ℤ)) := by
  unfold comp project_config C
  simp only [Function.comp_apply]
  have h_memo := e.memo_diagonal c T r hborder h0 hT
  unfold nextt_m C at h_memo
  rw [h_memo, Option.getD_some]

end BroadcastOCA

end CellularAutomatas
