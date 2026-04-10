import CellularAutomatas.proofs.time_constructible
import CellularAutomatas.proofs.constructions.composition.trace_kx

namespace CellularAutomatas

/-!
# Latched CA Construction and Time Extension

Given a CA C and a time-constructible function t, we construct a CA that:
1. Runs C in parallel with the timer
2. Latches C's projected output when the timer fires at t(n)
3. Preserves the latched value afterward

This solves the speedup problem: even if we continue computing past t(n),
we can report the value from exactly time t(n).

Also contains:
- `time_extension`: if L is accepted at time t(n) and t is time-constructible,
  then L can also be accepted at any later time t'(n) ≥ t(n).
-/

/-- State for a CA with latched output at a specific time. -/
structure LatchedState (Q : Type) (T : Type) (β : Type) where
  /-- Original CA state -/
  ca_state : Q
  /-- Timer CA state -/
  timer_state : T
  /-- Latched value (Some once timer fires) -/
  latched : Option β
deriving DecidableEq, Inhabited, Fintype

instance LatchedState.alphabet (Q T β : Type) [Alphabet Q] [Alphabet T] [Alphabet β] :
    Alphabet (LatchedState Q T β) where

/-- Product CA that runs original CA and timer in parallel, latching when timer fires.

    When timer fires at time t(n), we latch C.project of the current state.

    Special case: For border cells (a = none) when t(0) = 0, we pre-latch
    the initial value. This handles empty words where t(0) = 0 means the
    timer "fires" at time 0, but δ hasn't been called yet. -/
def latchedCA {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t)
    : CellAutomaton α？ β where
  Q := LatchedState C.Q tc.timer.Q β
  δ := fun left mid right =>
    let ca_next := C.δ left.ca_state mid.ca_state right.ca_state
    let timer_next := tc.timer.δ left.timer_state mid.timer_state right.timer_state
    let timer_signal := tc.timer.project timer_next
    let new_latched :=
      if mid.latched.isSome then mid.latched
      else if timer_signal then some (C.project ca_next)
      else none
    ⟨ca_next, timer_next, new_latched⟩
  embed := fun a =>
    let ca_emb := C.embed a
    let timer_emb := tc.timer.embed (a.map fun _ => ())
    -- Pre-latch border cells when t(0) = 0 (handles empty word case)
    let initial_latched := if a.isNone ∧ t 0 = 0 then some (C.project ca_emb) else none
    ⟨ca_emb, timer_emb, initial_latched⟩
  project := fun s => s.latched.getD (C.project s.ca_state)

namespace LatchedCA

variable {α β : Type} [Alphabet α] [Alphabet β]
variable (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t)

/-- Key observation: The timer embed sees the same thing for any word of length n.
    For word w of length n, `tc.timer.embed (word_to_config w p).map(fun _ => ())`
    equals `tc.timer.embed (word_to_config (unitWord n) p)`. -/
private lemma timer_embed_eq_unitWord (w : Word α) (p : ℤ) :
    tc.timer.embed ((word_to_config w p).map fun _ => ()) =
    tc.timer.embed (word_to_config (unitWord w.length) p) := by
  simp only [word_to_config, unitWord]
  split_ifs with h1 h2 h2
  · -- Both in range
    simp only [Option.map_some, List.getElem_replicate]
  · -- h1 true, h2 false — impossible since lengths match
    simp only [List.length_replicate] at h2
    omega
  · -- h1 false, h2 true — impossible since lengths match
    simp only [List.length_replicate] at h2
    omega
  · -- Both out of range
    rfl

/-- Initial embed equality: latchedCA's initial timer state matches tc.timer's initial state. -/
private lemma timer_embed_config_eq (w : Word α) (p : ℤ) :
    ((latchedCA C t tc).embed_config (word_to_config w) p).timer_state =
    tc.timer.embed_config (word_to_config (unitWord w.length)) p := by
  simp only [CellAutomaton.embed_config, latchedCA]
  exact timer_embed_eq_unitWord t tc w p

/-- Helper: the CA component of latchedCA evolves as C would.

    Proof by induction on time: the delta function for latchedCA computes
    ca_next = C.δ applied to the ca_state components of neighbors. -/
lemma ca_component_sync (w : Word α) (j : ℕ) (p : ℤ) :
    ((latchedCA C t tc).nextt ⦋w⦌ j p).ca_state = C.nextt ⦋w⦌ j p := by
  induction j generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, latchedCA]
  | succ j ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    show (C.δ ((latchedCA C t tc).nextt ⦋w⦌ j (p - 1)).ca_state
              ((latchedCA C t tc).nextt ⦋w⦌ j p).ca_state
              ((latchedCA C t tc).nextt ⦋w⦌ j (p + 1)).ca_state)
       = C.δ (C.nextt ⦋w⦌ j (p - 1)) (C.nextt ⦋w⦌ j p) (C.nextt ⦋w⦌ j (p + 1))
    rw [ih (p - 1), ih p, ih (p + 1)]

/-- Helper: the timer component of latchedCA evolves as tc.timer would.

    The timer only cares about word length for border detection. -/
lemma timer_component_sync (w : Word α) (j : ℕ) (p : ℤ) :
    ((latchedCA C t tc).nextt ⦋w⦌ j p).timer_state =
    tc.timer.nextt ⦋unitWord w.length⦌ j p := by
  induction j generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero]
    exact timer_embed_config_eq C t tc w p
  | succ j ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    show (tc.timer.δ ((latchedCA C t tc).nextt ⦋w⦌ j (p - 1)).timer_state
                     ((latchedCA C t tc).nextt ⦋w⦌ j p).timer_state
                     ((latchedCA C t tc).nextt ⦋w⦌ j (p + 1)).timer_state)
       = tc.timer.δ (tc.timer.nextt ⦋unitWord w.length⦌ j (p - 1))
                    (tc.timer.nextt ⦋unitWord w.length⦌ j p)
                    (tc.timer.nextt ⦋unitWord w.length⦌ j (p + 1))
    rw [ih (p - 1), ih p, ih (p + 1)]

/-- Initially, latched depends on whether the position is border and t(0) = 0. -/
private lemma latched_init (w : Word α) (p : ℤ) :
    ((latchedCA C t tc).nextt ⦋w⦌ 0 p).latched =
    if (word_to_config w p).isNone ∧ t 0 = 0 then some (C.project (C.embed none)) else none := by
  simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, latchedCA]
  -- The condition involves (word_to_config w p).isNone
  -- When true, word_to_config w p = none, so C.embed (word_to_config w p) = C.embed none
  split_ifs with h
  · -- Condition true: (word_to_config w p).isNone ∧ t 0 = 0
    rw [Option.isNone_iff_eq_none.mp h.1]
  · rfl

/-- At position 0, latched is none initially when t(w.length) > 0.
    This is because either w.length > 0 (so position 0 is not border) or
    w.length = 0 but t(0) > 0 (so pre-latch condition fails). -/
private lemma latched_init_pos0_none (w : Word α) (ht : t w.length > 0) :
    ((latchedCA C t tc).nextt ⦋w⦌ 0 0).latched = none := by
  rw [latched_init]
  simp only [ite_eq_right_iff, and_imp]
  intro h_border h_t0
  -- h_border: (word_to_config w 0).isNone = true
  -- h_t0: t 0 = 0
  -- From h_border, position 0 is border, so w = []
  simp only [word_to_config] at h_border
  split_ifs at h_border with h_in_range
  · simp at h_border
  · -- Position 0 is outside the word, so w.length ≤ 0, hence w = []
    push_neg at h_in_range
    have hw_empty : w.length = 0 := by omega
    -- But then t w.length = t 0 = 0, contradicting ht
    rw [hw_empty] at ht
    omega

/-- Before timer fires, latched stays none at position 0.
    Proof: by induction, showing that while timer_signal is false, latched doesn't change from none. -/
lemma latched_none_before_signal (w : Word α) (j : ℕ) (hj : j < t w.length) :
    ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched = none := by
  induction j with
  | zero => exact latched_init_pos0_none C t tc w (by omega)
  | succ j ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- The new latched value depends on mid.latched and timer_signal
    show (if ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched.isSome
          then ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched
          else if tc.timer.project (tc.timer.δ
                   ((latchedCA C t tc).nextt ⦋w⦌ j (-1)).timer_state
                   ((latchedCA C t tc).nextt ⦋w⦌ j 0).timer_state
                   ((latchedCA C t tc).nextt ⦋w⦌ j 1).timer_state)
               then some _
               else none) = none
    -- By IH, mid.latched = none, so isSome = false
    have ih_none : ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched = none := ih (Nat.lt_of_succ_lt hj)
    simp only [ih_none, Option.isSome_none]
    -- Timer signal is false at time j+1 < t(n)
    have h_timer_sync : tc.timer.δ ((latchedCA C t tc).nextt ⦋w⦌ j (-1)).timer_state
                                   ((latchedCA C t tc).nextt ⦋w⦌ j 0).timer_state
                                   ((latchedCA C t tc).nextt ⦋w⦌ j 1).timer_state
                      = tc.timer.nextt ⦋unitWord w.length⦌ (j + 1) 0 := by
      simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
      rw [timer_component_sync C t tc w j (-1),
          timer_component_sync C t tc w j 0,
          timer_component_sync C t tc w j 1]
      ring_nf
    rw [h_timer_sync]
    have h_no_signal := tc.no_signal_before w.length (j + 1) hj
    -- h_no_signal already in right form
    simp only [CellAutomaton.nextt_succ] at h_no_signal
    simp [h_no_signal]

/-- The latched component of latchedCA.δ. -/
private lemma latchedCA_δ_latched (left mid right : (latchedCA C t tc).Q) :
    ((latchedCA C t tc).δ left mid right).latched =
    if mid.latched.isSome then mid.latched
    else if tc.timer.project (tc.timer.δ left.timer_state mid.timer_state right.timer_state)
         then some (C.project (C.δ left.ca_state mid.ca_state right.ca_state))
         else none := rfl

/-- At time t(n), the latch is triggered with C's projected value.

    Uses: tc.signal_at_t says timer signals at t(n)
    Uses: ca_component_sync says CA state matches C's evolution

    Note: For t(n) = 0, the latch is never triggered via δ (latched stays none),
    but latchedCA.project still returns the correct value via getD fallback. -/
lemma latch_triggered_at_t (w : Word α) (ht_pos : t w.length > 0) :
    ((latchedCA C t tc).nextt ⦋w⦌ (t w.length) 0).latched =
    some (C.project (C.nextt ⦋w⦌ (t w.length) 0)) := by
  -- Since t(n) > 0, we can express t(n) = j + 1 for some j
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t w.length ≠ 0)
  -- t(n) = j + 1: the latch triggers with C's projected value.
  -- Key steps: latched is none before t(n), timer fires at t(n),
  -- CA state is synchronized with C's evolution.
  have h_none : ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched = none :=
    latched_none_before_signal C t tc w j (by rw [hj]; omega)
  -- Timer fires at t(n) = j + 1
  have h_signal := tc.signal_at_t w.length
  rw [hj] at h_signal ⊢
  -- Unfold nextt at time j+1
  simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
  rw [latchedCA_δ_latched]
  -- Since latched was none at time j, isSome = false
  simp only [h_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  -- The timer signal fires at time j+1
  have h_timer_eq : tc.timer.δ ((latchedCA C t tc).nextt ⦋w⦌ j (0 - 1)).timer_state
                               ((latchedCA C t tc).nextt ⦋w⦌ j 0).timer_state
                               ((latchedCA C t tc).nextt ⦋w⦌ j (0 + 1)).timer_state
                  = tc.timer.nextt ⦋unitWord w.length⦌ (j + 1) 0 := by
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    rw [timer_component_sync C t tc w j (0 - 1),
        timer_component_sync C t tc w j 0,
        timer_component_sync C t tc w j (0 + 1)]
  rw [h_timer_eq, h_signal]
  simp only [↓reduceIte]
  -- Now show the CA state is synchronized
  -- Use ca_component_sync to rewrite the ca_state components
  rw [ca_component_sync C t tc w j (0 - 1),
      ca_component_sync C t tc w j 0,
      ca_component_sync C t tc w j (0 + 1)]

/-- For empty word with t(0) = 0, latched is pre-set to the correct value at time 0.

    The embed function pre-latches border cells when t(0) = 0.
    For empty word, all positions are borders, so position 0 is pre-latched. -/
lemma latch_triggered_at_t_zero (ht_zero : t 0 = 0) :
    ((latchedCA C t tc).nextt ⦋([] : Word α)⦌ 0 0).latched =
    some (C.project (C.nextt ⦋([] : Word α)⦌ 0 0)) := by
  rw [latched_init]
  -- word_to_config [] 0 = none (empty word, all positions are border)
  have h_border : word_to_config ([] : Word α) (0 : ℤ) = none := by
    simp only [word_to_config, List.length_nil]
    split_ifs with h <;> simp_all
  simp only [h_border, Option.isNone_none, true_and, ht_zero, ↓reduceIte]
  -- At time 0, C.nextt gives embed_config
  simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config]
  -- C.embed (word_to_config [] 0) = C.embed none by h_border
  rw [h_border]

/-- Once latched has a value, it persists through subsequent steps. -/
private lemma latched_persists_step (w : Word α) (j : ℕ)
    (h_some : ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched.isSome) :
    ((latchedCA C t tc).nextt ⦋w⦌ (j + 1) 0).latched =
    ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched := by
  -- Unfold the definition of nextt at time j+1
  simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
  rw [latchedCA_δ_latched]
  -- Since mid.latched.isSome = true (by h_some), the first branch is taken
  simp only [h_some, ↓reduceIte]

/-- Once latched, the value persists.

    By construction: if mid.latched.isSome then new_latched = mid.latched -/
lemma latch_persists (w : Word α) (j₀ j : ℕ) (hj₀ : j₀ = t w.length) (hj : j ≥ j₀)
    (ht_pos : t w.length > 0) :
    ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched =
    ((latchedCA C t tc).nextt ⦋w⦌ j₀ 0).latched := by
  -- By induction on the difference j - j₀
  induction j with
  | zero =>
    -- j = 0, so j₀ = 0 as well (since j ≥ j₀)
    simp only [Nat.le_zero] at hj
    rw [hj]
  | succ j ih =>
    by_cases hle : j ≥ j₀
    · -- j ≥ j₀: use IH and latched_persists_step
      have h_eq := ih hle
      -- At j₀, latch is triggered, so latched.isSome
      have h_trig := latch_triggered_at_t C t tc w ht_pos
      rw [← hj₀] at h_trig
      have h_some_j₀ : ((latchedCA C t tc).nextt ⦋w⦌ j₀ 0).latched.isSome := by
        rw [h_trig]; simp
      have h_some_j : ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched.isSome := by
        rw [h_eq]; exact h_some_j₀
      rw [latched_persists_step C t tc w j h_some_j, ih hle]
    · -- j < j₀: then j + 1 ≤ j₀, but we have j + 1 ≥ j₀, so j + 1 = j₀
      push_neg at hle
      have h_eq : j + 1 = j₀ := by omega
      rw [h_eq]

/-- For empty word with t(0) = 0, the latched value persists from time 0.

    Since latch is pre-set at embed time for border cells when t(0) = 0,
    it persists through all subsequent steps via latched_persists_step. -/
lemma latch_persists_zero (j : ℕ) (ht_zero : t 0 = 0) :
    ((latchedCA C t tc).nextt ⦋([] : Word α)⦌ j 0).latched =
    ((latchedCA C t tc).nextt ⦋([] : Word α)⦌ 0 0).latched := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h_trig := latch_triggered_at_t_zero C t tc ht_zero
    have h_some_0 : ((latchedCA C t tc).nextt ⦋([] : Word α)⦌ 0 0).latched.isSome := by
      rw [h_trig]; simp
    have h_some_j : ((latchedCA C t tc).nextt ⦋([] : Word α)⦌ j 0).latched.isSome := by
      rw [ih]; exact h_some_0
    rw [latched_persists_step C t tc [] j h_some_j, ih]

end LatchedCA

/-- **Latch Lemma**

    For any CA C and time-constructible t, the latched CA captures C's output
    at time t(n) and preserves it indefinitely.

    At time t(n) + t' for any t' ≥ 0:
      (latchedCA C tc).comp w (t(n) + t') 0 = C.comp w t(n) 0

    **Construction**: latchedCA runs C and timer in parallel. When the timer
    fires at t(n), it latches C.project of the current state.

    **Proof outline**:
    - **Case t(n) > 0**: Latch triggers at t(n) via δ, persists afterward.
    - **Case t(n) = 0 (empty word)**: Pre-latched at embed time, persists.

    The hypothesis `w.length > 0 → t w.length > 0` ensures that when w is non-empty,
    the timer fires at a positive time (so latch triggers via δ). For empty word,
    the embed function pre-latches if t(0) = 0. -/
theorem latchedCA_correct {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t)
    (w : Word α) (t' : ℕ) (ht_pos : w.length > 0 → t w.length > 0) :
    (latchedCA C t tc).comp ⦋⟬w⟭⦌ (t w.length + t') 0 =
    C.comp ⦋⟬w⟭⦌ (t w.length) 0 := by
  by_cases ht : t w.length > 0
  · -- Case: t(n) > 0 — latch triggers via δ at time t(n)
    have h_trig := LatchedCA.latch_triggered_at_t C t tc w ht
    have h_pers := LatchedCA.latch_persists C t tc w (t w.length) (t w.length + t') rfl
                     (Nat.le_add_right _ _) ht
    -- comp is defined as project_config ∘ nextt, so at position 0:
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp]
    -- latchedCA.project s = s.latched.getD (C.project s.ca_state)
    -- By h_pers, latched at time t(n) + t' = latched at time t(n)
    -- By h_trig, latched at time t(n) = some (C.project (C.nextt ⦋⟬w⟭⦌ (t w.length) 0))
    show ((latchedCA C t tc).nextt ⦋⟬w⟭⦌ (t w.length + t') 0).latched.getD
           (C.project ((latchedCA C t tc).nextt ⦋⟬w⟭⦌ (t w.length + t') 0).ca_state) =
         C.project (C.nextt ⦋⟬w⟭⦌ (t w.length) 0)
    rw [h_pers, h_trig]
    simp only [Option.getD_some]
  · -- Case: t(n) = 0 — must be empty word, pre-latched at embed time
    push_neg at ht
    have ht_zero : t w.length = 0 := by omega
    -- By contrapositive of ht_pos: ¬(t w.length > 0) → ¬(w.length > 0)
    have hw_empty : w.length = 0 := by
      by_contra h
      have h_pos : w.length > 0 := Nat.pos_of_ne_zero h
      have : t w.length > 0 := ht_pos h_pos
      omega
    have hw : w = [] := List.eq_nil_of_length_eq_zero hw_empty
    subst hw
    -- Now w = [], t 0 = 0
    simp only [List.length_nil] at ht_zero ⊢
    have h_trig := LatchedCA.latch_triggered_at_t_zero C t tc ht_zero
    have h_pers := LatchedCA.latch_persists_zero C t tc t' ht_zero
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp]
    show ((latchedCA C t tc).nextt ⦋⟬[]⟭⦌ (t 0 + t') 0).latched.getD
           (C.project ((latchedCA C t tc).nextt ⦋⟬[]⟭⦌ (t 0 + t') 0).ca_state) =
         C.project (C.nextt ⦋⟬[]⟭⦌ (t 0) 0)
    rw [ht_zero, Nat.zero_add, h_pers, h_trig]
    simp only [Option.getD_some]

/-!
## Latched CA with k-step lookback

`latchedCA_k C t tc k` latches C's output from `k` steps before the timer fires.
It uses `TraceKx` to track the last `k` outputs of C, then `latchedCA` to latch
the trace when the timer fires at `t(n)`, and finally `map_project` to extract
the oldest value (index 0) corresponding to time `t(n) - k`.
-/

/-- Latched CA with k-step lookback.

    Runs `TraceKx(k, C)` in parallel with the timer. When the timer fires at
    `t(n)`, latches the trace (last `k` projected outputs). The final projection
    extracts index 0 (the oldest value), giving C's output at time `t(n) - k`.

    Uses: `TraceKx` for the shift register, `latchedCA` for the timer+latch. -/
def latchedCA_k {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t) (k : ℕ) [NeZero k]
    : CellAutomaton α？ β :=
  let trace : TraceKx := { k := k, α := α？, β := β, C_orig := C }
  (latchedCA trace.C t tc).map_project (fun f => (f 0).getD default)

/-- `latchedCA_k` captures C's output from `k` steps before the timer fires.

    At time `t(n) + t'` for any `t' ≥ 0`:
      `(latchedCA_k C t tc k).comp ⦋⟬w⟭⦌ (t w.length + t') 0 = C.comp ⦋⟬w⟭⦌ (t w.length - k) 0`

    Requires:
    - `t(n) > k` (so the trace has k previous outputs to look back)
    - `t(n) > 0` (for the latch mechanism to work)

    **Proof idea**:
    1. By `latchedCA_correct`, at time `t(n) + t'` the latched trace equals
       `TraceKx.C.comp` at time `t(n)`.
    2. By `TraceKx.spec`, `TraceKx.C.comp c (t(n)) p` at index 0 gives
       `some (C.comp c (t(n) - k) p)`.
    3. `map_project` extracts `(some v).getD default = v`. -/
@[simp]
theorem latchedCA_k_spec {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t) (k : ℕ) [NeZero k]
    (w : Word α) (t' : ℕ) (ht_pos : t w.length > 0) (ht_k : t w.length > k) :
    (latchedCA_k C t tc k).comp ⦋⟬w⟭⦌ (t w.length + t') 0 =
    C.comp ⦋⟬w⟭⦌ ((t w.length) - k) 0 := by
  -- latchedCA_k C t tc k = (latchedCA trace.C t tc).map_project (fun f => (f 0).getD default)
  -- where trace = { k := k, α := α？, β := β, C_orig := C }

  -- Define trace to match the definition
  let trace : TraceKx := { k := k, α := α？, β := β, C_orig := C }

  -- Use latchedCA_correct: (latchedCA trace.C t tc).comp ⦋w⦌ (t + t') 0 = trace.C.comp ⦋w⦌ t 0
  -- ht_pos : t w.length > 0, which implies (w.length > 0 → t w.length > 0)
  have h_latch := latchedCA_correct trace.C t tc w t' (fun _ => ht_pos)

  -- Use TraceKx.spec': for t > k, trace.C.comp c t p i = some (C.comp c (t - k + i) p)
  -- Note: trace.k = k by definition
  have hk : trace.k = k := rfl
  have h_spec' := trace.spec' ⟬w⟭ (t w.length) 0 (0 : Fin k) (hk ▸ ht_k)

  -- Calculate step by step
  calc (latchedCA_k C t tc k).comp ⦋⟬w⟭⦌ (t w.length + t') 0
      = ((latchedCA trace.C t tc).comp ⦋⟬w⟭⦌ (t w.length + t') 0 0).getD default := rfl
    _ = (trace.C.comp ⦋⟬w⟭⦌ (t w.length) 0 0).getD default := by rw [h_latch]
    _ = (some (trace.C_orig.comp ⦋⟬w⟭⦌ (t w.length - k + 0) 0)).getD default := by
          -- h_spec' : trace.C.comp ⦋⟬w⟭⦌ (t w.length) 0 (0 : Fin k) = some (...)
          -- And 0 : Fin trace.k = 0 : Fin k since trace.k = k
          simp only [hk] at h_spec'
          exact congrArg (fun x => x.getD default) h_spec'
    _ = trace.C_orig.comp ⦋⟬w⟭⦌ (t w.length - k) 0 := by simp
    _ = C.comp ⦋⟬w⟭⦌ (t w.length - k) 0 := rfl

/-!
## Time Extension

If a CA accepts a language at time t(n) and t is time-constructible,
then the language can also be accepted at any later time t'(n) ≥ t(n).

Construction: run C and timer in parallel via `latchedCA`, latch C's
answer when the timer fires at t(n), read the latched value at t'(n).
-/

/-- If a CA accepts at time t(n) and t is time-constructible,
    then there exists a CA accepting the same language at any time t'(n) ≥ t(n).

    **Construction**: Run C and timer in parallel via `latchedCA`. The timer
    fires at t(n), latching C's acceptance value at position 0. At time
    t'(n) ≥ t(n), the latched value is still available.

    Requires t(n) > 0 for all n (satisfied by real-time t(n) = n-1 for n ≥ 2).

    This is the variable-time analogue of `ComposeKSteps`: where `ComposeKSteps`
    switches phases after a fixed `k` steps (using a local countdown), `latchedCA`
    switches after `t(n)` steps using a `TimeConstructible` timer that fires at
    position 0. For language recognition (which only reads position 0), this
    suffices to capture C's answer from time t(n) and replay it at any later time. -/
theorem time_extension {α : Type} [Alphabet α]
    {t : ℕ → ℕ} (tc : TimeConstructible t)
    {C : tCellAutomaton α} (hC : C ∈ CA α) (hT : ∀ n, C.t n = t n)
    (t' : ℕ → ℕ) (ht' : ∀ n, t n ≤ t' n) (ht_pos : ∀ n, t n > 0) :
    ∃ C' : tCellAutomaton α, C' ∈ CA α ∧ (∀ n, C'.t n = t' n) ∧ C'.L = C.L := by
  -- Build C' as latchedCA with time t' and position 0
  refine ⟨{
    toCellAutomaton := latchedCA C.toCellAutomaton t tc
    t := t'
    p := fun _ => 0
  }, ?_, fun _ => rfl, ?_⟩
  · -- C' ∈ CA α: position is always 0
    simp only [CA, tCellAutomata, Set.mem_univ, Set.mem_setOf_eq, true_and]
  · -- C'.L = C.L: latchedCA preserves the language
    ext w
    show (latchedCA C.toCellAutomaton t tc).comp ⦋⟬w⟭⦌ (t' w.length) 0 = true
       ↔ C.toCellAutomaton.comp ⦋⟬w⟭⦌ (C.t w.length) (C.p w.length) = true
    -- Substitute C.p = 0 (from CA membership) and C.t = t (from hypothesis)
    have hp : C.p w.length = 0 := by
      have := hC; simp only [CA, tCellAutomata, Set.mem_univ, true_and] at this
      exact congr_fun this w.length
    rw [hp, hT w.length]
    -- Apply latchedCA_correct: the latched value at time t'(n) equals C's output at t(n)
    have key := latchedCA_correct C.toCellAutomaton t tc w (t' w.length - t w.length)
                  (fun _ => ht_pos w.length)
    rw [show t w.length + (t' w.length - t w.length) = t' w.length
        from Nat.add_sub_cancel' (ht' w.length)] at key
    rw [key]

/-!
## ComposeAtTime: Unifying ComposeKSteps with TimeConstructible

`ComposeKSteps` runs C1 for a fixed k steps, then switches globally to C2.
For variable-time switching at `t(n)`, we need a timer. If we require a
**global** switch (all cells, not just position 0), we need the FSSP:
all cells fire simultaneously at time `t(n)`, then transition to phase 2.

This is the core of PR #4's `rt_with_ntime_advice_subset_2n`:
- Phase 1 (0 to n−1): compute advice (all positions ready at n−1)
- FSSP fires at n−1 → global switch
- Phase 2 (n−1 to 2(n−1)): run original CA on annotated input

### Construction sketch

Given:
- C1 : CellAutomaton α？ β (phase 1)
- C2 : CellAutomaton β γ (phase 2)
- An FSSP that fires all cells at time t(n)

Build a CA that runs C1 + FSSP in parallel for t(n) steps. When the FSSP
fires, every cell projects C1's output, embeds it into C2, and starts
running C2. After t(n) + t₂ steps, the result is:

  `C.comp ⟬w⟭ (t(n) + t₂) p = C2.comp (C1.comp ⟬w⟭ t(n)) t₂ p`

This mirrors `ComposeKSteps.spec` with `k = t(n)`.

### Why latchedCA suffices for time_extension

For language recognition, we only read position 0. The `TimeConstructible`
timer fires at position 0, which is enough to trigger the latch. We don't
need the FSSP's global synchronization — only position 0's output matters.

This is why `time_extension` uses `latchedCA` (position-0 timer) rather
than the full FSSP + global phase switch: it's simpler and sufficient.
-/

end CellularAutomatas
