import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.time_constructible.basic
import CellularAutomatas.proofs.constructions.two_sided_fssp_full

namespace CellularAutomatas

/-!
# Synchronous Time-Constructible Functions

A function `f : ℕ → ℕ` is *synchronously* time-constructible if a CA fires
a `true`-signal at *every interior cell* of an `n`-cell input at time `f n`,
and stays `true` afterwards.

## Two flavours

* `SyncTimeConstructible f` — the basic version. Only constrains interior
  behaviour; the timer may produce arbitrary projections at out-of-range
  positions.

* `SyncTimeConstructibleInner f` — strengthens the spec to require that
  out-of-range cells *never* project `true` and that out-of-range cells
  stay at the border state. There is no generic lift from
  `SyncTimeConstructible`; instances are constructed directly.

The Inner version is what compositions like `Sum` and the
`compose-advices` simulator need: they rely on the timer's projection
being a clean indicator of "is this an interior cell at time ≥ f n".

## Building blocks (current status)

* `Const c : SyncTimeConstructibleInner (fun _ => c)` — sorry-free.
* `Sum` — closure under addition (output is `SyncTimeConstructible`,
  not `Inner`). Built directly on top of `fireThenRun`. Sorry-free.
* `IsTimeAdvice.compose` — composition of time-advices, sorry-free.
* `IdSync : SyncTimeConstructible (fun n => n)` — checked using the
  constructive two-sided FSSP solver.
-/

/-! ## `SyncTimeConstructible` — base spec, interior only -/

structure SyncTimeConstructible (f : ℕ → ℕ) where
  /-- The timer CA, reading just border markers. -/
  timer : CellAutomaton Unit？ Bool
  /-- Spec: at every interior cell `0 ≤ p < n`, the projection at time `k`
      is `true` iff `k ≥ f n`. -/
  fires_iff : ∀ (n : ℕ) (p : ℤ) (k : ℕ), 0 ≤ p → p < n →
    (timer.project (timer.nextt ⦋unitWord n⦌ k p) = true ↔ k ≥ f n)

namespace SyncTimeConstructible

variable {f : ℕ → ℕ}

theorem fires_at (sc : SyncTimeConstructible f) (n : ℕ) (p : ℤ)
    (hp0 : 0 ≤ p) (hpn : p < n) :
    sc.timer.project (sc.timer.nextt ⦋unitWord n⦌ (f n) p) = true :=
  (sc.fires_iff n p (f n) hp0 hpn).mpr le_rfl

theorem no_fire_before (sc : SyncTimeConstructible f) (n : ℕ) (p : ℤ) (k : ℕ)
    (hp0 : 0 ≤ p) (hpn : p < n) (hk : k < f n) :
    sc.timer.project (sc.timer.nextt ⦋unitWord n⦌ k p) = false := by
  have h := sc.fires_iff n p k hp0 hpn
  cases h_eq : sc.timer.project (sc.timer.nextt ⦋unitWord n⦌ k p) with
  | false => rfl
  | true =>
    exfalso
    have : k ≥ f n := h.mp h_eq
    omega

end SyncTimeConstructible

/-! ## `SyncTimeConstructibleInner` — additionally forbids out-of-range firing
                                   and requires a quiescent border state. -/

/-- A strengthened sync timer where:
    * out-of-range cells *never* project `true` (`no_outer_fire`);
    * the border state is quiescent (`border_quiescent`), i.e.
      `δ border border border = border`.

    Both properties are needed for `Sum` (and other compositions): the timer
    that runs in parallel with a "runtime" CA must keep its outer behaviour
    completely passive so that in-range cells reading outer neighbours get a
    predictable value (`timer.embed none = timer.border`). The state-level
    "outer cells stay at border for all time" property is *derivable* from
    quiescence + `no_outer_fire` (see `border_passive` below), so we only
    record the strictly weaker quiescence as a structural axiom. -/
structure SyncTimeConstructibleInner (f : ℕ → ℕ) extends SyncTimeConstructible f where
  /-- For positions outside `[0, n)`, the projection is `false` at all times. -/
  no_outer_fire : ∀ (n : ℕ) (p : ℤ) (k : ℕ), ¬ (0 ≤ p ∧ p < (n : ℤ)) →
    timer.project (timer.nextt ⦋unitWord n⦌ k p) = false
  /-- The border state is quiescent: a border cell with two border neighbours
      stays at the border. (Notably *weaker* than asking outer cells to stay
      at `border` under arbitrary inputs — quiescence only constrains the
      all-border configuration.) -/
  border_quiescent : timer.quiescent timer.border


/-! ## `Const c` — uniform counter that fires at time `c` everywhere

    Even simpler than the original: state `Bool × Fin (c + 1)` carries
    a latched `am_border` bit AND the counter. The transition increments
    only when not on a border; project is `counter = c ∧ ¬ am_border`.

    This directly produces a `SyncTimeConstructibleInner`. -/

private def constInnerTimerCA (c : ℕ) : CellAutomaton Unit？ Bool where
  Q := Bool × Fin (c + 1)
  δ := fun _ q _ =>
    -- `am_border` is latched per-cell; counter saturates at c (only for non-borders).
    let (am_border, counter) := q
    let counter' :=
      if am_border then counter
      else ⟨min (counter.val + 1) c, by
        have : min (counter.val + 1) c ≤ c := min_le_right _ _
        omega⟩
    (am_border, counter')
  embed := fun a => (a.isNone, ⟨0, by omega⟩)
  project := fun (am_border, counter) => decide (counter.val = c ∧ ¬ am_border)

private lemma constInnerTimerCA_embed (c n : ℕ) (p : ℤ) :
    @CellAutomaton.embed_config _ _ (constInnerTimerCA c) (word_to_config (unitWord n)) p =
      ((word_to_config (unitWord n) p).isNone, ⟨0, by omega⟩) := by
  show (constInnerTimerCA c).embed (word_to_config (unitWord n) p) = _
  rfl

/-- The first invariant: `am_border` bit equals input position's `isNone`. -/
private lemma constInnerTimerCA_first_eq (c n t : ℕ) (p : ℤ) :
    ((constInnerTimerCA c).nextt ⦋unitWord n⦌ t p).1 =
      (word_to_config (unitWord n) p).isNone := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero]
    rw [constInnerTimerCA_embed]
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- δ q1 q2 q3 .1 = q2.1 (am_border preserved per cell).
    show (((constInnerTimerCA c).nextt ⦋unitWord n⦌ t p).1) = _
    exact ih p

/-- δ-step lemma: a non-border (q.1 = false) cell increments to `min (q.val + 1) c`. -/
private lemma constInnerTimerCA_step_inner {c : ℕ}
    (q1 q3 : (constInnerTimerCA c).Q) {q2 : (constInnerTimerCA c).Q}
    (h : q2.1 = false) :
    ((constInnerTimerCA c).δ q1 q2 q3).2.val = min (q2.2.val + 1) c := by
  obtain ⟨b, n⟩ := q2
  simp at h
  subst h
  rfl

/-- The second invariant: counter at in-range cells is `min t c`. -/
private lemma constInnerTimerCA_second_eq_inrange (c n t : ℕ) (p : ℤ)
    (hp0 : 0 ≤ p) (hpn : p < n) :
    ((constInnerTimerCA c).nextt ⦋unitWord n⦌ t p).2.val = min t c := by
  -- In-range ⟹ am_border = false at all times.
  have h_border_false : ∀ s : ℕ, ((constInnerTimerCA c).nextt ⦋unitWord n⦌ s p).1 = false := by
    intro s
    rw [constInnerTimerCA_first_eq]
    unfold word_to_config
    simp [hp0, hpn]
  induction t with
  | zero =>
    simp only [CellAutomaton.nextt_zero]
    rw [constInnerTimerCA_embed]
    simp
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next]
    rw [constInnerTimerCA_step_inner _ _ (h_border_false t)]
    rw [ih]
    omega

/-- The constant function `fun _ => c` is sync-time-constructible
    (Inner variant: outer cells never fire). -/
def Const (c : ℕ) : SyncTimeConstructibleInner (fun _ => c) where
  timer := constInnerTimerCA c
  fires_iff n p k hp0 hpn := by
    -- Abbreviate the result.
    set q := (constInnerTimerCA c).nextt ⦋unitWord n⦌ k p with hq
    have h_first : q.1 = false := by
      rw [hq, constInnerTimerCA_first_eq]
      unfold word_to_config; simp [hp0, hpn]
    have h_second : q.2.val = min k c := by
      rw [hq]
      exact constInnerTimerCA_second_eq_inrange c n k p hp0 hpn
    -- Now the goal: project q = true ↔ k ≥ c.
    show decide (q.2.val = c ∧ ¬ q.1) = true ↔ k ≥ c
    rw [h_first, h_second, decide_eq_true_eq]
    constructor
    · rintro ⟨h_cnt, _⟩; omega
    · intro h_k
      refine ⟨?_, by decide⟩
      omega
  no_outer_fire n p k h_outer := by
    set q := (constInnerTimerCA c).nextt ⦋unitWord n⦌ k p with hq
    have h_first : q.1 = true := by
      rw [hq, constInnerTimerCA_first_eq]
      show (word_to_config (unitWord n) p).isNone = true
      unfold word_to_config
      split_ifs with h
      · exfalso; apply h_outer; exact ⟨h.1, by simpa using h.2⟩
      · rfl
    show decide (q.2.val = c ∧ ¬ q.1) = false
    rw [h_first, decide_eq_false_iff_not]
    push_neg
    intro _h
    decide
  border_quiescent := by
    -- Goal: δ border border border = border. With border = (true, ⟨0, _⟩),
    -- the per-cell `am_border` bit is preserved and the counter stays at 0
    -- because am_border = true. Result equals border.
    rw [CellAutomaton.quiescent_iff]
    rfl


/-! ## On lifting `SyncTimeConstructible` to `SyncTimeConstructibleInner`

    The general `QuiescentBorder` construction in
    `CellularAutomatas.proofs.constructions.border_quiescent` makes any CA's
    border state quiescent. Combined with a `Bool × C.Q` "am-I-border" latch
    that turns off the projection at outer cells, this gives a generic lift
    `SyncTimeConstructible.toInner`. (Not implemented yet — instances so far
    are built directly: `Const`, `IdSync`. (`Sum` produces only the base
    `SyncTimeConstructible` — re-Innerizing is currently future work.) -/


/-! ## `IdSync` — `fun n => n` is sync time constructible

    Construction: build a `FireThenRunInput` whose first stage is the marker
    advice (`Advice.fssp_input Unit`, computable in `1` step) and whose
    runtime is the concrete two-sided FSSP solver `TwoSidedFSSP.optimal`.
    With the timer firing `1` step in (so the FSSP
    sees its initial configuration `⟬fssp_both_sides n⟭` at relative time `0`)
    and FSSP firing every interior cell at relative time `n - 1`, the
    composite timer fires every interior cell at absolute time `1 + (n - 1) = n`.

    Defined later in the file — see the bottom for the actual construction.
    The forward-declared placeholder in this section is removed; the real
    definition is below `FireThenRun`. -/


/-! ## `fireThenRun` — generic "advice then runtime" pattern

    Given:
    * `h : Advice α β` with `a : h.IsTimeAdvice t1` — the first stage produces
       advice symbol `(h w)[i]` at cell `i`, time `t1 |w|`.
    * `sc : SyncTimeConstructibleInner t1` — a global firing signal arrives at
       every interior cell at time `t1 |w|`.
    * `runtime : CellAutomaton β？ γ` — the post-firing CA.
    * `h_quiescent : runtime.quiescent runtime.border` — outer cells stay at
       border state under `runtime.δ`.

    Build a CA on `α？ → γ` that
    * runs `a.C` and `sc.timer` in parallel;
    * keeps a third slot at `runtime.border` everywhere;
    * at the timer's firing edge, in-range cells seed the third slot with
      `runtime.embed (some (h w)[i])` (read off `a.C`'s state);
    * thereafter the third slot evolves under `runtime.δ` at every cell.

    `spec_pre` / `spec_post` (below) characterise the projection cleanly:
    pre-firing it is `runtime.project runtime.border`, post-firing it matches
    `runtime`'s standalone trace on `⟬h w⟭`.

    Powers `IsTimeAdvice.compose` directly. -/
section FireThenRun

variable {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]

/-- Bundle of inputs to the `fireThenRun` construction. The advice `h` and
    its time function `t1` are kept implicit: callers usually have `a` and
    `sc` in hand and Lean infers `h`/`t1` from their types. -/
structure FireThenRunInput (α β γ : Type)
    [Alphabet α] [Alphabet β] [Alphabet γ] where
  /-- The first-stage advice. -/
  {h : Advice α β}
  /-- The first-stage running time. -/
  {t1 : ℕ → ℕ}
  /-- Witness that `h` is computable in time `t1`. -/
  a : h.IsTimeAdvice t1
  /-- The synchronous firing signal at time `t1`. -/
  sc : SyncTimeConstructibleInner t1
  /-- The post-firing CA. -/
  runtime : CellAutomaton β？ γ
  /-- The runtime's border state is quiescent. Needed to keep the third slot
      at `runtime.border` everywhere before firing. -/
  h_quiescent : runtime.quiescent runtime.border

namespace FireThenRunInput

/-- The composed three-slot CA: timer, advice, runtime.
    The runtime slot is *always* a real `runtime.Q` value — it sits at
    `runtime.border` until the firing edge, then transitions to
    `runtime.embed (some (a.C.project ...))` at that very tick, and continues
    evolving under `runtime.δ` thereafter (at every cell, in-range or outer). -/
def C (X : FireThenRunInput α β γ) : CellAutomaton α？ γ where
  Q := X.sc.timer.Q × X.a.C.Q × X.runtime.Q
  δ := fun (l1, lA, l2) (m1, mA, m2) (r1, rA, r2) =>
    let m1' := X.sc.timer.δ l1 m1 r1
    let mA' := X.a.C.δ lA mA rA
    let m2' :=
      if X.sc.timer.project m1' && !X.sc.timer.project m1 then
        -- Firing edge: seed the runtime slot from the advice slot.
        X.runtime.embed (some (X.a.C.project mA'))
      else
        -- Otherwise: just step the runtime slot via `runtime.δ`.
        X.runtime.δ l2 m2 r2
    (m1', mA', m2')
  embed := fun a =>
    let timer_state := X.sc.timer.embed (a.map (fun _ => ()))
    let advice_state := X.a.C.embed a
    -- Pre-seed only if `t1 n = 0` (timer fires at embed time).
    let runtime_state : X.runtime.Q :=
      if X.sc.timer.project timer_state then
        X.runtime.embed (some (X.a.C.project advice_state))
      else
        X.runtime.border
    (timer_state, advice_state, runtime_state)
  project := fun (_, _, q) => X.runtime.project q

/-! ### Internal helpers (not for export) -/

/-- Casting: `Option.map (fun _ => ()) (word_to_config w p) =
    word_to_config (unitWord w.length) p`. The `Alphabet α` instance is
    inherited from the surrounding `variable` block but unused here. -/
private lemma word_to_config_unit_map (w : Word α) (p : ℤ) :
    Option.map (fun _ : α => ()) (word_to_config w p) =
      word_to_config (unitWord w.length) p := by
  unfold word_to_config
  split_ifs with h1 h2 h3
  · simp
  · exfalso; apply h2; exact ⟨h1.1, by simpa [unitWord] using h1.2⟩
  · exfalso; apply h1; exact ⟨h3.1, by simpa [unitWord] using h3.2⟩
  · rfl

/-- The timer slot evolves like `sc.timer` on the matching `unitWord`. -/
private lemma first_eq (X : FireThenRunInput α β γ)
    (w : Word α) (t : ℕ) (p : ℤ) :
    (X.C.nextt ⟬w⟭ t p).1 = X.sc.timer.nextt ⟬unitWord w.length⟭ t p := by
  induction t generalizing p with
  | zero =>
    show (X.C.embed (word_to_config w p)).1 =
        X.sc.timer.embed (word_to_config (unitWord w.length) p)
    show X.sc.timer.embed (Option.map (fun _ => ()) (word_to_config w p)) =
        X.sc.timer.embed (word_to_config (unitWord w.length) p)
    rw [word_to_config_unit_map]
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next, CellAutomaton.nextt_succ,
        CellAutomaton.next]
    show X.sc.timer.δ
            (X.C.nextt ⟬w⟭ t (p - 1)).1
            (X.C.nextt ⟬w⟭ t p).1
            (X.C.nextt ⟬w⟭ t (p + 1)).1 = _
    rw [ih (p - 1), ih p, ih (p + 1)]

/-- The advice slot evolves like `a.C` on the original `α？` input. -/
private lemma advice_eq (X : FireThenRunInput α β γ)
    (w : Word α) (t : ℕ) (p : ℤ) :
    (X.C.nextt ⟬w⟭ t p).2.1 = X.a.C.nextt ⟬w⟭ t p := by
  induction t generalizing p with
  | zero =>
    show (X.C.embed _).2.1 = X.a.C.embed _
    rfl
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next, CellAutomaton.nextt_succ,
        CellAutomaton.next]
    show X.a.C.δ
            (X.C.nextt ⟬w⟭ t (p - 1)).2.1
            (X.C.nextt ⟬w⟭ t p).2.1
            (X.C.nextt ⟬w⟭ t (p + 1)).2.1 = _
    rw [ih (p - 1), ih p, ih (p + 1)]

/-- Convenience unfolding of the runtime slot's transition. -/
private lemma unfold_succ (X : FireThenRunInput α β γ)
    (w : Word α) (t : ℕ) (p : ℤ) :
    (X.C.nextt ⟬w⟭ (t + 1) p).2.2 =
      (if X.sc.timer.project (X.C.nextt ⟬w⟭ (t + 1) p).1 &&
          !X.sc.timer.project (X.C.nextt ⟬w⟭ t p).1
        then X.runtime.embed
              (some (X.a.C.project (X.C.nextt ⟬w⟭ (t + 1) p).2.1))
        else X.runtime.δ
              (X.C.nextt ⟬w⟭ t (p - 1)).2.2
              (X.C.nextt ⟬w⟭ t p).2.2
              (X.C.nextt ⟬w⟭ t (p + 1)).2.2) := by
  rw [CellAutomaton.nextt_succ, CellAutomaton.next]
  rfl

/-- Before any cell can fire, the runtime slot is `runtime.border` everywhere.

    The hypothesis is parametric: only requires `t < t1 |w|` *if there is at
    least one in-range cell*. (Vacuously satisfied when `|w| = 0`.) -/
private lemma third_pre_firing (X : FireThenRunInput α β γ)
    (w : Word α) (t : ℕ)
    (ht : ∀ q : ℤ, 0 ≤ q → q < (w.length : ℤ) → t < X.t1 w.length)
    (p : ℤ) :
    (X.C.nextt ⟬w⟭ t p).2.2 = X.runtime.border := by
  -- Timer never fires at any cell at any time `≤ t`.
  have h_no_fire : ∀ k : ℕ, k ≤ t → ∀ q : ℤ,
      X.sc.timer.project (X.C.nextt ⟬w⟭ k q).1 = false := by
    intro k _hk q
    rw [first_eq X]
    by_cases hin : 0 ≤ q ∧ q < (w.length : ℤ)
    · obtain ⟨hp0, hpn⟩ := hin
      have h_t_lt : k < X.t1 w.length := by
        have := ht q hp0 hpn
        omega
      exact X.sc.no_fire_before w.length q k hp0 hpn h_t_lt
    · exact X.sc.no_outer_fire w.length q k hin
  clear ht
  induction t generalizing p with
  | zero =>
    show (X.C.embed _).2.2 = X.runtime.border
    have h_no_fire_0 :
        X.sc.timer.project
          (X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p))) = false := by
      have h_eq : X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p)) =
          X.sc.timer.nextt ⟬unitWord w.length⟭ 0 p := by
        simp only [CellAutomaton.nextt_zero]
        show X.sc.timer.embed (Option.map _ (word_to_config w p)) =
            X.sc.timer.embed (word_to_config (unitWord w.length) p)
        rw [word_to_config_unit_map]
      rw [h_eq]
      have := h_no_fire 0 (Nat.zero_le _) p
      rw [first_eq X] at this
      simp only [CellAutomaton.nextt_zero] at this
      exact this
    show (if X.sc.timer.project
            (X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p))) = true
          then _ else X.runtime.border) = X.runtime.border
    rw [h_no_fire_0]
    rfl
  | succ t ih =>
    have h_no_fire' : ∀ k : ℕ, k ≤ t → ∀ q : ℤ,
        X.sc.timer.project (X.C.nextt ⟬w⟭ k q).1 = false :=
      fun k hk q => h_no_fire k (Nat.le_succ_of_le hk) q
    rw [unfold_succ X w t p]
    have h_now : X.sc.timer.project (X.C.nextt ⟬w⟭ (t + 1) p).1 = false :=
      h_no_fire (t + 1) le_rfl p
    rw [h_now]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [ih (p - 1) h_no_fire', ih p h_no_fire', ih (p + 1) h_no_fire']
    exact X.h_quiescent ⟨X.runtime.border, rfl⟩
            ⟨X.runtime.border, rfl⟩ ⟨X.runtime.border, rfl⟩

/-- After the firing tick, the runtime slot evolves like `runtime` running on
    the advice-annotated input `⟬h w⟭`. -/
private lemma third_after (X : FireThenRunInput α β γ)
    (w : Word α) (s : ℕ) (p : ℤ) :
    (X.C.nextt ⟬w⟭ (X.t1 w.length + s) p).2.2 = X.runtime.nextt ⟬X.h w⟭ s p := by
  induction s generalizing p with
  | zero =>
    rw [Nat.add_zero, CellAutomaton.nextt_zero]
    by_cases ht1 : X.t1 w.length = 0
    · -- t1 = 0: pre-seeded at embed time (or border at outer cells).
      rw [ht1]
      show (X.C.embed (⟬w⟭ p)).2.2 = _
      by_cases hp : 0 ≤ p ∧ p < (w.length : ℤ)
      · -- In-range: pre-seeded.
        obtain ⟨hp0, hpn⟩ := hp
        have h_fire_0 :
            X.sc.timer.project
              (X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p))) = true := by
          have h_eq : X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p)) =
              X.sc.timer.nextt ⟬unitWord w.length⟭ 0 p := by
            simp only [CellAutomaton.nextt_zero]
            show X.sc.timer.embed (Option.map _ (word_to_config w p)) =
                X.sc.timer.embed (word_to_config (unitWord w.length) p)
            rw [word_to_config_unit_map]
          rw [h_eq]
          exact (X.sc.fires_iff w.length p 0 hp0 hpn).mpr (by omega)
        show (if X.sc.timer.project
                (X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p))) = true
              then _ else X.runtime.border) = _
        rw [h_fire_0]
        simp only [↓reduceIte]
        show X.runtime.embed (some (X.a.C.project (X.a.C.embed (word_to_config w p)))) =
            X.runtime.embed_config ⟬X.h w⟭ p
        show X.runtime.embed (some (X.a.C.project (X.a.C.embed (word_to_config w p)))) =
            X.runtime.embed (word_to_config (X.h w) p)
        congr 1
        have h_hw_len : (X.h w).length = w.length := X.h.len w
        have hp_in_hw : 0 ≤ p ∧ p < ((X.h w).length : ℤ) := by
          refine ⟨hp0, ?_⟩; rw [h_hw_len]; exact hpn
        unfold word_to_config
        rw [dif_pos hp_in_hw]
        congr 1
        have hp_toNat_lt : p.toNat < w.length := by
          have h : (p.toNat : ℤ) < (w.length : ℤ) := by
            rw [Int.toNat_of_nonneg hp0]; exact hpn
          exact_mod_cast h
        have hp_toNat_lt_h : p.toNat < (X.h w).length :=
          h_hw_len.symm ▸ hp_toNat_lt
        have h_get : (X.h w)[p.toNat]? =
            some (X.a.C.comp ⟬w⟭ (X.t1 w.length) (p.toNat : ℤ)) := by
          rw [X.a.spec w, List.getElem?_map]
          rw [List.getElem?_range hp_toNat_lt]
          rfl
        have h_some : (X.h w)[p.toNat]? = some ((X.h w)[p.toNat]'hp_toNat_lt_h) :=
          List.getElem?_eq_getElem hp_toNat_lt_h
        have h_eq_get :
            (X.h w)[p.toNat]'hp_toNat_lt_h =
              X.a.C.comp ⟬w⟭ (X.t1 w.length) (p.toNat : ℤ) := by
          rw [h_some] at h_get
          exact Option.some_inj.mp h_get
        rw [h_eq_get, ht1]
        show X.a.C.project (X.a.C.nextt ⟬w⟭ 0 p) =
          X.a.C.project (X.a.C.nextt ⟬w⟭ 0 (p.toNat : ℤ))
        rw [Int.toNat_of_nonneg hp0]
      · -- Outer: pre-seed condition false, slot is border.
        have h_no_fire :
            X.sc.timer.project
              (X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p))) = false := by
          have h_eq : X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p)) =
              X.sc.timer.nextt ⟬unitWord w.length⟭ 0 p := by
            simp only [CellAutomaton.nextt_zero]
            show X.sc.timer.embed (Option.map _ (word_to_config w p)) =
                X.sc.timer.embed (word_to_config (unitWord w.length) p)
            rw [word_to_config_unit_map]
          rw [h_eq]
          exact X.sc.no_outer_fire w.length p 0 hp
        show (if X.sc.timer.project
                (X.sc.timer.embed (Option.map (fun _ : α => ()) (⟬w⟭ p))) = true
              then _ else X.runtime.border) = _
        rw [h_no_fire]
        simp only [Bool.false_eq_true, ↓reduceIte]
        show X.runtime.border = X.runtime.embed (word_to_config (X.h w) p)
        have h_hw_len : (X.h w).length = w.length := X.h.len w
        have hp_out_hw : ¬ (0 ≤ p ∧ p < ((X.h w).length : ℤ)) := by
          rw [h_hw_len]; exact hp
        unfold word_to_config
        rw [dif_neg hp_out_hw]
        rfl
    · -- t1 ≥ 1: seeded at the firing tick.
      have ht1_pos : X.t1 w.length ≥ 1 := Nat.one_le_iff_ne_zero.mpr ht1
      have h_t1_eq : X.t1 w.length = (X.t1 w.length - 1) + 1 := by omega
      rw [h_t1_eq, unfold_succ]
      have h_pre :
          (X.C.nextt ⟬w⟭ (X.t1 w.length - 1) (p - 1)).2.2 = X.runtime.border ∧
          (X.C.nextt ⟬w⟭ (X.t1 w.length - 1) p).2.2 = X.runtime.border ∧
          (X.C.nextt ⟬w⟭ (X.t1 w.length - 1) (p + 1)).2.2 = X.runtime.border := by
        have h_t_bound : ∀ q : ℤ, 0 ≤ q → q < (w.length : ℤ) →
            X.t1 w.length - 1 < X.t1 w.length :=
          fun _ _ _ => by omega
        refine ⟨?_, ?_, ?_⟩
          <;> exact third_pre_firing X w (X.t1 w.length - 1) h_t_bound _
      obtain ⟨h_pre_l, h_pre_m, h_pre_r⟩ := h_pre
      by_cases hp : 0 ≤ p ∧ p < (w.length : ℤ)
      · -- In-range p: timer fires at the firing tick.
        obtain ⟨hp0, hpn⟩ := hp
        have h_no_fire_pred : X.sc.timer.project
            (X.C.nextt ⟬w⟭ (X.t1 w.length - 1) p).1 = false := by
          rw [first_eq X]
          exact X.sc.no_fire_before w.length p (X.t1 w.length - 1) hp0 hpn (by omega)
        have h_fire_now : X.sc.timer.project
            (X.C.nextt ⟬w⟭ ((X.t1 w.length - 1) + 1) p).1 = true := by
          rw [first_eq X]
          have h_pred_succ : (X.t1 w.length - 1) + 1 = X.t1 w.length := by omega
          rw [h_pred_succ]
          exact X.sc.fires_at w.length p hp0 hpn
        rw [h_no_fire_pred, h_fire_now]
        simp only [Bool.true_and, Bool.not_false, ↓reduceIte]
        have h_a_state : (X.C.nextt ⟬w⟭ ((X.t1 w.length - 1) + 1) p).2.1 =
            X.a.C.nextt ⟬w⟭ (X.t1 w.length) p := by
          have h_pred_succ : (X.t1 w.length - 1) + 1 = X.t1 w.length := by omega
          rw [h_pred_succ]
          exact advice_eq X w (X.t1 w.length) p
        rw [h_a_state]
        show X.runtime.embed (some (X.a.C.project (X.a.C.nextt ⟬w⟭ (X.t1 w.length) p))) =
            X.runtime.embed (word_to_config (X.h w) p)
        congr 1
        have h_hw_len : (X.h w).length = w.length := X.h.len w
        have hp_in_hw : 0 ≤ p ∧ p < ((X.h w).length : ℤ) := by
          refine ⟨hp0, ?_⟩; rw [h_hw_len]; exact hpn
        unfold word_to_config
        rw [dif_pos hp_in_hw]
        congr 1
        have hp_toNat_lt : p.toNat < w.length := by
          have h : (p.toNat : ℤ) < (w.length : ℤ) := by
            rw [Int.toNat_of_nonneg hp0]; exact hpn
          exact_mod_cast h
        have hp_toNat_lt_h : p.toNat < (X.h w).length :=
          h_hw_len.symm ▸ hp_toNat_lt
        have h_get : (X.h w)[p.toNat]? =
            some (X.a.C.comp ⟬w⟭ (X.t1 w.length) (p.toNat : ℤ)) := by
          rw [X.a.spec w, List.getElem?_map]
          rw [List.getElem?_range hp_toNat_lt]
          rfl
        have h_some : (X.h w)[p.toNat]? = some ((X.h w)[p.toNat]'hp_toNat_lt_h) :=
          List.getElem?_eq_getElem hp_toNat_lt_h
        have h_eq_get :
            (X.h w)[p.toNat]'hp_toNat_lt_h =
              X.a.C.comp ⟬w⟭ (X.t1 w.length) (p.toNat : ℤ) := by
          rw [h_some] at h_get
          exact Option.some_inj.mp h_get
        rw [h_eq_get]
        show X.a.C.project (X.a.C.nextt ⟬w⟭ (X.t1 w.length) p) =
          X.a.C.project (X.a.C.nextt ⟬w⟭ (X.t1 w.length) (p.toNat : ℤ))
        rw [Int.toNat_of_nonneg hp0]
      · -- Outer p: timer doesn't fire at firing tick either.
        have h_now : X.sc.timer.project
            (X.C.nextt ⟬w⟭ ((X.t1 w.length - 1) + 1) p).1 = false := by
          rw [first_eq X]
          have h_pred_succ : (X.t1 w.length - 1) + 1 = X.t1 w.length := by omega
          rw [h_pred_succ]
          exact X.sc.no_outer_fire w.length p (X.t1 w.length) hp
        rw [h_now]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [h_pre_l, h_pre_m, h_pre_r]
        -- runtime.δ on three borders = border (quiescence); RHS is also border (outer).
        have h_lhs : X.runtime.δ X.runtime.border X.runtime.border X.runtime.border =
            X.runtime.border :=
          X.h_quiescent ⟨X.runtime.border, rfl⟩
            ⟨X.runtime.border, rfl⟩ ⟨X.runtime.border, rfl⟩
        rw [h_lhs]
        show X.runtime.border = X.runtime.embed (word_to_config (X.h w) p)
        have h_hw_len : (X.h w).length = w.length := X.h.len w
        have hp_out_hw : ¬ (0 ≤ p ∧ p < ((X.h w).length : ℤ)) := by
          rw [h_hw_len]; exact hp
        unfold word_to_config
        rw [dif_neg hp_out_hw]
        rfl
  | succ s ih =>
    -- Step from s to s+1: just `runtime.δ` on three IH values.
    have h_step_eq : X.t1 w.length + (s + 1) = (X.t1 w.length + s) + 1 := by omega
    rw [h_step_eq, unfold_succ]
    -- Firing-edge condition is false: at in-range it was already firing one
    -- step earlier; at outer cells it never fires.
    have h_if_false :
        (X.sc.timer.project (X.C.nextt ⟬w⟭ (X.t1 w.length + s + 1) p).1 &&
        !X.sc.timer.project (X.C.nextt ⟬w⟭ (X.t1 w.length + s) p).1) = false := by
      by_cases hp : 0 ≤ p ∧ p < (w.length : ℤ)
      · obtain ⟨hp0, hpn⟩ := hp
        have h_prev_true : X.sc.timer.project
            (X.C.nextt ⟬w⟭ (X.t1 w.length + s) p).1 = true := by
          rw [first_eq X]
          exact (X.sc.fires_iff w.length p (X.t1 w.length + s) hp0 hpn).mpr (by omega)
        rw [h_prev_true]
        simp
      · have h_curr_false : X.sc.timer.project
            (X.C.nextt ⟬w⟭ (X.t1 w.length + s + 1) p).1 = false := by
          rw [first_eq X]
          exact X.sc.no_outer_fire w.length p (X.t1 w.length + s + 1) hp
        rw [h_curr_false]
        simp
    rw [h_if_false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ih (p - 1), ih p, ih (p + 1)]
    rw [CellAutomaton.nextt_succ, CellAutomaton.next]

/-! ### Public spec -/

/-- **Pre-firing.** Before the timer fires, every cell projects to
    `runtime.project runtime.border`. -/
theorem spec_pre (X : FireThenRunInput α β γ)
    (w : Word α) (t : ℕ) (p : ℤ) (ht : t < X.t1 w.length) :
    X.C.comp ⟬w⟭ t p = X.runtime.project X.runtime.border := by
  show X.runtime.project (X.C.nextt ⟬w⟭ t p).2.2 =
       X.runtime.project X.runtime.border
  rw [third_pre_firing X w t (fun _ _ _ => ht) p]

/-- **Post-firing.** From the firing tick onwards, every cell's projection
    matches the standalone runtime trace on the advised input `⟬h w⟭`. -/
theorem spec_post (X : FireThenRunInput α β γ)
    (w : Word α) (s : ℕ) (p : ℤ) :
    X.C.comp ⟬w⟭ (X.t1 w.length + s) p = X.runtime.comp ⟬X.h w⟭ s p := by
  show X.runtime.project (X.C.nextt ⟬w⟭ (X.t1 w.length + s) p).2.2 =
       X.runtime.project (X.runtime.nextt ⟬X.h w⟭ s p)
  rw [third_after X w s p]

end FireThenRunInput

end FireThenRun


/-! ## Trivial identity advice on `Unit`

    Used as the "first stage" of `fireThenRun` when there's no real advice
    to compute (e.g. `Sum`): the advice is the identity `Word Unit → Word Unit`
    and the witness CA does nothing. Its `IsTimeAdvice` witness holds for
    *any* time bound — there's nothing to wait for. -/

/-- The witness CA for `Advice.id_unit`: state = projection = `Unit`,
    `δ` returns `()`. -/
def Advice.id_unit_witnessCA : CellAutomaton Unit？ Unit where
  Q := Unit
  δ := fun _ _ _ => ()
  embed := fun _ => ()
  project := fun _ => ()

/-- The identity advice on `Unit`. -/
def Advice.id_unit : Advice Unit Unit :=
  ⟨id, fun _ => rfl⟩

/-- The identity advice on `Unit` is computable in any time `t`. -/
def Advice.id_unit_isTimeAdvice (t : ℕ → ℕ) : Advice.id_unit.IsTimeAdvice t where
  C := Advice.id_unit_witnessCA
  spec w := by
    -- Both sides are lists of length `w.length` over `Unit`; equal by `Subsingleton`.
    show w = (List.range w.length).map
      (fun (i : ℕ) => Advice.id_unit_witnessCA.comp ⟬w⟭ (t w.length) (i : ℤ))
    apply List.ext_getElem
    · simp
    · intro i _ _; exact Subsingleton.elim _ _


/-! ## `Sum` — sync time is closed under addition (without `Inner` output)

    Direct application of `fireThenRun`:
    * first stage: the trivial identity advice on `Unit`, computable in time `f`;
    * sync timer: `s1`;
    * runtime: `s2.timer`, with `quiescent border` from `s2.border_quiescent`.

    The result is a `SyncTimeConstructible (f + g)`. To recover the
    full `Inner` form (with `no_outer_fire` and `border_quiescent`), apply a
    generic `SyncTimeConstructible.toInner` lift (future work). -/
def Sum {f g : ℕ → ℕ}
    (s1 : SyncTimeConstructibleInner f) (s2 : SyncTimeConstructibleInner g) :
    SyncTimeConstructible (fun n => f n + g n) :=
  let X : FireThenRunInput Unit Unit Bool :=
    { a := Advice.id_unit_isTimeAdvice f
      sc := s1
      runtime := s2.timer
      h_quiescent := s2.border_quiescent }
  { timer := X.C
    fires_iff n p k hp0 hpn := by
      -- `X.h (unitWord n) = unitWord n` because `X.h = id` (id_unit's `f`).
      -- The goal `X.C.project (X.C.nextt …) = true ↔ k ≥ f n + g n` is by
      -- definitional unfolding `X.C.comp … = true ↔ …`.
      show X.C.comp ⦋unitWord n⦌ k p = true ↔ k ≥ f n + g n
      by_cases hk : k < f n
      · -- Pre-firing: projection is `s2.timer.project s2.timer.border = false`.
        rw [X.spec_pre (unitWord n) k p (by simpa using hk)]
        show s2.timer.project s2.timer.border = true ↔ k ≥ f n + g n
        have h_false : s2.timer.project s2.timer.border = false := by
          show s2.timer.project (s2.timer.embed none) = false
          have h_outer0 : ¬ (0 ≤ (0 : ℤ) ∧ (0 : ℤ) < (0 : ℕ)) := by
            intro ⟨_, h⟩; simpa using h
          have := s2.no_outer_fire 0 0 0 h_outer0
          simp only [CellAutomaton.nextt_zero] at this
          have h_eq : (⦋unitWord 0⦌ : Config s2.timer.Q) 0 = s2.timer.embed none := by
            show s2.timer.embed (word_to_config (unitWord 0) 0) = s2.timer.embed none
            unfold word_to_config; simp [unitWord]
          rw [← h_eq]; exact this
        rw [h_false]; simp; omega
      · -- Post-firing: projection equals `s2.timer.comp ⟬unitWord n⟭ (k - f n) p`.
        push_neg at hk
        set s := k - f n with hs
        have hk_eq : k = f n + s := by omega
        rw [hk_eq]
        -- `X.spec_post (unitWord n) s p` gives:
        --   X.C.comp ⦋unitWord n⦌ (X.t1 (unitWord n).length + s) p =
        --   X.runtime.comp ⦋X.h (unitWord n)⦌ s p.
        -- Reduce: `X.t1 = f`, `(unitWord n).length = n`, `X.h = id`,
        -- `X.runtime = s2.timer` — so this becomes
        --   X.C.comp ⦋unitWord n⦌ (f n + s) p = s2.timer.comp ⦋unitWord n⦌ s p.
        have h_post : X.C.comp ⦋unitWord n⦌ (f n + s) p =
            s2.timer.comp ⦋unitWord n⦌ s p := by
          have := X.spec_post (unitWord n) s p
          simpa using this
        rw [h_post, CellAutomaton.comp_apply, s2.fires_iff n p s hp0 hpn]
        omega }



/-! ## Composition of time-advices

    `IsTimeAdvice.compose`: given `a1 : h1.IsTimeAdvice t1`,
    `a2 : h2.IsTimeAdvice t2`, a sync timer `sc1` for `t1`, and a quiescent
    `a2.C.border`, the composed advice `h1.compose h2 = h2 ∘ h1` is a
    `(t1 + t2)`-time advice.

    The proof packages the inputs into a `FireThenRunInput` and reads off the
    spec via `spec_post` at `s = t2 |w|`. -/
section ComposeIsTimeAdvice

variable {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]

/-- The composition `h1 ▷ h2 = (h2 ∘ h1)` is a `(t1 + t2)`-time advice on
    `α → γ`, given that `t1` is sync and `a2.C` has a quiescent border.

    Built directly on `FireThenRun`: package the inputs, then read off the
    spec via `spec_post` at `s = t2 |w|`. -/
def IsTimeAdvice.compose
    {h1 : Advice α β} {h2 : Advice β γ} {t1 t2 : ℕ → ℕ}
    (sc1 : SyncTimeConstructibleInner t1)
    (a1 : h1.IsTimeAdvice t1) (a2 : h2.IsTimeAdvice t2)
    (h_quiescent : a2.C.quiescent a2.C.border) :
    (h1.compose h2).IsTimeAdvice (fun n => t1 n + t2 n) :=
  let X : FireThenRunInput α β γ :=
    { a := a1, sc := sc1, runtime := a2.C, h_quiescent := h_quiescent }
  { C := X.C
    spec := fun w => by
      show h2 (h1 w) = (List.range w.length).map
        (fun (i : ℕ) => X.C.comp ⟬w⟭ (t1 w.length + t2 w.length) (i : ℤ))
      have h_h1w_len : (h1 w).length = w.length := h1.len w
      rw [a2.spec (h1 w)]
      apply List.ext_getElem
      · simp [h_h1w_len]
      · intro i hi_lhs _
        have hi : i < w.length := by
          rw [h_h1w_len] at hi_lhs; simpa using hi_lhs
        simp only [List.getElem_map, List.getElem_range]
        -- `X.spec_post w (t2 |w|) i` :
        --   X.C.comp ⟬w⟭ (t1 |w| + t2 |w|) i = a2.C.comp ⟬h1 w⟭ (t2 |w|) i
        -- (using X.runtime = a2.C, X.h = h1, X.t1 = t1 by reduction).
        have h_post := X.spec_post w (t2 w.length) (i : ℤ)
        show a2.C.comp ⟬h1 w⟭ (t2 (h1 w).length) (i : ℤ) =
          X.C.comp ⟬w⟭ (t1 w.length + t2 w.length) (i : ℤ)
        rw [h_h1w_len, ← h_post] }

end ComposeIsTimeAdvice


/-! ## `IdSync` — `fun n => n` is sync time constructible

    Build a `FireThenRunInput` over `Unit → Bool × Bool → Bool`:
    * first stage: `Advice.fssp_input Unit` with witness
      `fssp_input_is_const_time_1`, a 1-step advice;
    * sync timer for `t1 = fun _ => 1`: `Const 1`;
    * runtime: the checked two-sided FSSP solver `TwoSidedFSSP.optimal`.

    Then for `unitWord n` and an interior cell `p`:
    * `k = 0`: `spec_pre` gives `C.project C.border = false` ✓;
    * `k ≥ 1`: `spec_post` at `s = k - 1` gives
      `C.comp ⟬fssp_both_sides n⟭ (k - 1) p = true ↔ k - 1 ≥ n - 1 ↔ k ≥ n`. -/

/-- The concrete optimal two-sided FSSP solver used by `IdSync`. -/
private def idSyncFsspCA : CellAutomaton (Bool × Bool)？ Bool :=
  TwoSidedFSSP.optimal

private theorem idSyncFsspCA_spec : SolvesTwoSidedFSSPOptimal idSyncFsspCA :=
  TwoSidedFSSP.optimal_solves

/-- The `FireThenRunInput` underlying `IdSync`: marker advice (1 step) + FSSP. -/
private def idSyncInput :
    FireThenRunInput Unit (Bool × Bool) Bool :=
  { a := fssp_input_is_const_time_1
    sc := Const 1
    runtime := idSyncFsspCA
    h_quiescent := idSyncFsspCA_spec.quiescent_border }

private lemma idSyncInput_t1 (n : ℕ) : idSyncInput.t1 n = 1 := rfl

private lemma idSyncInput_runtime : idSyncInput.runtime = idSyncFsspCA := rfl

private lemma idSyncInput_h_f (n : ℕ) :
    idSyncInput.h.f (unitWord n) = fssp_both_sides n := by
  show fssp_both_sides (unitWord n).length = fssp_both_sides n
  rw [unitWord_length]

def IdSync : SyncTimeConstructible (fun n => n) where
  timer := idSyncInput.C
  fires_iff := fun n p k hp0 hpn => by
    show idSyncInput.C.comp ⦋unitWord n⦌ k p = true ↔ k ≥ n
    have hn_pos : n ≥ 1 := by
      have : (0 : ℤ) < (n : ℤ) := lt_of_le_of_lt hp0 hpn
      omega
    by_cases hk : k = 0
    · -- Pre-firing: timer.t1 = 1 > k = 0.
      subst hk
      rw [idSyncInput.spec_pre (unitWord n) 0 p (by show 0 < 1; omega)]
      show idSyncFsspCA.project idSyncFsspCA.border = true ↔ 0 ≥ n
      rw [idSyncFsspCA_spec.border_projects_false]
      simp; omega
    · -- Post-firing: k ≥ 1, so k = 1 + (k - 1).
      have hk1 : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
      set s := k - 1 with hs
      have hk_eq : k = 1 + s := by omega
      rw [hk_eq]
      have h_post : idSyncInput.C.comp ⦋unitWord n⦌ (1 + s) p =
          idSyncFsspCA.comp ⦋fssp_both_sides n⦌ s p := by
        have hp := idSyncInput.spec_post (unitWord n) s p
        rw [show (1 : ℕ) = idSyncInput.t1 (unitWord n).length from
              by rw [unitWord_length]; rfl,
            ← idSyncInput_runtime,
            show fssp_both_sides n = idSyncInput.h.f (unitWord n) from
              (idSyncInput_h_f n).symm]
        exact hp
      rw [h_post]
      rw [idSyncFsspCA_spec.fire_iff n hn_pos s p hp0 hpn]
      omega

end CellularAutomatas
