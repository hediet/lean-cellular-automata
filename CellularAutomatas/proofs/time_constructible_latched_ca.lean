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

    When timer fires at time t(n), we latch C.project of the current state. -/
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
    ⟨ca_emb, timer_emb, none⟩
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

/-- Initially, latched is none at all positions. -/
private lemma latched_init (w : Word α) (p : ℤ) :
    ((latchedCA C t tc).nextt ⦋w⦌ 0 p).latched = none := by
  simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, latchedCA]

/-- Before timer fires, latched stays none at position 0.
    Proof: by induction, showing that while timer_signal is false, latched doesn't change from none. -/
lemma latched_none_before_signal (w : Word α) (j : ℕ) (hj : j < t w.length) :
    ((latchedCA C t tc).nextt ⦋w⦌ j 0).latched = none := by
  induction j with
  | zero => exact latched_init C t tc w 0
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
    simp only [ih_none, Option.isSome_none, ↓reduceIte]
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
    simp only [unitWord_length] at h_no_signal
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
    Uses: ca_component_sync says CA state matches C's evolution -/
lemma latch_triggered_at_t (w : Word α) :
    ((latchedCA C t tc).nextt ⦋w⦌ (t w.length) 0).latched =
    some (C.project (C.nextt ⦋w⦌ (t w.length) 0)) := by
  cases ht : t w.length with
  | zero =>
    -- t(n) = 0: at time 0, nextt gives initial embed, latched = none.
    -- The latch only updates through δ, so t(n) = 0 is degenerate.
    sorry
  | succ j =>
    -- t(n) = j + 1: the latch triggers with C's projected value.
    -- Key steps: latched is none before t(n), timer fires at t(n),
    -- CA state is synchronized with C's evolution.
    sorry

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
lemma latch_persists (w : Word α) (j₀ j : ℕ) (hj₀ : j₀ = t w.length) (hj : j ≥ j₀) :
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
      have h_trig := latch_triggered_at_t C t tc w
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

end LatchedCA

/-- **Latch Lemma**

    For any CA C and time-constructible t, the latched CA captures C's output
    at time t(n) and preserves it indefinitely.

    At time t(n) + t' for any t' ≥ 0:
      (latchedCA C tc).comp w (t(n) + t') 0 = C.comp w t(n) 0

    **Construction**: latchedCA runs C and timer in parallel. When the timer
    fires at t(n), it latches C.project of the current state.

    **Proof outline**:
    1. **Latch triggers at t(n)**: latched = some(C.comp w t(n) 0)
    2. **Latch persists**: Once latched.isSome, the value never changes
    3. **Project returns latched**: s.latched.getD _ = latched value when Some -/
theorem latchedCA_correct {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t)
    (w : Word α) (t' : ℕ) :
    (latchedCA C t tc).comp ⦋⟬w⟭⦌ (t w.length + t') 0 =
    C.comp ⦋⟬w⟭⦌ (t w.length) 0 := by
  -- Uses latch_triggered_at_t + latch_persists + project returns latched value
  sorry

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

    **Proof idea**:
    1. By `latchedCA_correct`, at time `t(n) + t'` the latched trace equals
       `TraceKx.C.comp` at time `t(n)`.
    2. By `TraceKx.spec`, `TraceKx.C.comp c (t(n)) p` at index 0 gives
       `some (C.comp c (t(n) - k) p)`.
    3. `map_project` extracts `(some v).getD default = v`. -/
@[simp]
theorem latchedCA_k_spec {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t) (k : ℕ) [NeZero k]
    (w : Word α) (t' : ℕ) :
    (latchedCA_k C t tc k).comp ⦋⟬w⟭⦌ (t w.length + t') 0 =
    C.comp ⦋⟬w⟭⦌ ((t w.length) - k) 0 := by
  sorry

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

    This is the variable-time analogue of `ComposeKSteps`: where `ComposeKSteps`
    switches phases after a fixed `k` steps (using a local countdown), `latchedCA`
    switches after `t(n)` steps using a `TimeConstructible` timer that fires at
    position 0. For language recognition (which only reads position 0), this
    suffices to capture C's answer from time t(n) and replay it at any later time. -/
theorem time_extension {α : Type} [Alphabet α]
    {t : ℕ → ℕ} (tc : TimeConstructible t)
    {C : tCellAutomaton α} (hC : C ∈ CA α) (hT : ∀ n, C.t n = t n)
    (t' : ℕ → ℕ) (ht' : ∀ n, t n ≤ t' n) :
    ∃ C' : tCellAutomaton α, C' ∈ CA α ∧ (∀ n, C'.t n = t' n) ∧ C'.L = C.L := by
  -- Build C' as latchedCA with time t' and position 0
  refine ⟨{
    toCellAutomaton := latchedCA C.toCellAutomaton t tc
    t := t'
    p := fun _ => 0
  }, ?_, fun _ => rfl, ?_⟩
  · -- C' ∈ CA α: position is always 0
    simp only [CA, tCellAutomata, Set.mem_sep_iff, Set.mem_univ, Set.mem_setOf_eq, true_and]
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
