import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.fssp

/-!
# Two-sided simulation from one-sided CA

Given any CA `C` with `quiescent_set {border, inner false}`, we construct CAs
that simulate `C` on half-length input, using a two-sided (`fssp_both_sides`)
initial configuration.

## Overview

The construction has three layers:

1. **Late-border lemma** (generic): A border cell that appears at position `L`
   only from time `L − 1` onward is observationally equivalent to one present
   from `t = 0`, because quiescence ensures no information reaches cell `L − 1`
   before step `L − 1`.

2. **Odd-n simulation**: For odd `n ≥ 3`, scouts at speed 1 from both generals
   coincide on the middle cell at time `⌊n/2⌋`. The middle cell becomes a
   shared border. Each half has length `L = ⌈n/2⌉`, and the half-CA runs
   from `t = 0` with no delay. The simulation projects to `C.comp ⟬fssp_left_side L⟭ t p`.

3. **Even-n simulation**: For even `n ≥ 2`, scouts become adjacent (never
   coincide) at time `n/2 − 1`. Walls are installed on the two adjacent cells.
   Half-FSSPs are **delayed by 1 step** to let the wall arrive in time.
   Each half has length `L = n/2`, and the half-CA at absolute time `t`
   projects to `C.comp ⟬fssp_left_side L⟭ (t − 1) p`.

## Proof ideas

### Late-border lemma

We show by induction on `t` that for `t < L − 1` and `p ∈ [0, L)`, the
configuration `C.nextt` is the same whether cell `L` is `border` or
`inner false`.

**Key invariant**: at time `t`, cells `p` with `p > t` are still in
`{border, inner false}` (quiescent set). This follows from the speed-of-light
principle: cell `p`'s state at time `t` depends only on the initial states of
cells in `[p − t, p + t]`. If all of `[p − t, p + t]` are in the quiescent
set initially, then cell `p` stays in the quiescent set.

Since cell `L` differs between the two runs but cell `L − 1`'s state at
time `t < L − 1` depends only on cells `[L − 1 − t, L − 1 + t]`, and
`L − 1 + t < L + (L − 2) = 2L − 2`, cell `L − 1` only reads cell `L`
starting from `t = L − 1`. Before that, cell `L − 1` only sees cells in
`[0, L − 1]` which are identical in both runs.

More precisely: cells `[0, L − 1]` start identically, and cells outside
`[0, L]` are `border` in both runs. Cell `L` differs, but is only read
by cell `L − 1`, and only at step `t ≥ L − 1`. So for all `t < L − 1`
and `p ∈ [0, L)`, both runs agree.

### Odd-n simulation

**State**: `Q_scout × Q_C × Q_C` (scout track, left-half, right-half).

**Scout track**: 5 states `{quiet, right_scout, left_scout, wall, post_wall}`.
- At `t = 0`, cell 0 emits `right_scout`, cell `n − 1` emits `left_scout`.
- Each scout propagates at speed 1 toward the other end.
- When `right_scout` and `left_scout` meet on the same cell (odd `n`),
  that cell becomes `wall`.
- `wall` is a sink (stays `wall` forever).

**Left-half component**: runs `C`'s transition rule. Reads the scout track:
when its right neighbour's scout state is `wall`, it treats that neighbour
as `border`.

**Right-half component**: symmetric (mirrored `C`).

**Simulation claim**: for `p ∈ [0, ⌈n/2⌉)` and all `t`:
  `left_proj(C'.nextt ⟬fssp_both_sides n⟭ t p) = C.nextt ⟬fssp_left_side ⌈n/2⌉⟭ t p`

Uses late-border lemma: the wall at cell `⌈n/2⌉` appears at `t = ⌊n/2⌋ = ⌈n/2⌉ − 1 = L − 1`,
which is exactly in time.

### Even-n simulation

**State**: `Q_scout × Q_C × Q_C` (same structure).

**Scout track**: same 5 states. When scouts are adjacent (cell `k − 1` has
`right_scout` and cell `k` has `left_scout`), both become `wall`.

**Key difference**: half-FSSPs delayed by 1 step.
- At `t = 0`, left-half and right-half components are held in `inner false`
  (not yet started).
- At `t = 1`, the left-half component of cell 0 transitions to `inner true`
  (the general), and the right-half of cell `n − 1` similarly.
- From `t = 1` onward, the half-CA evolves by `C`'s rule.

**Simulation claim**: for `p ∈ [0, n/2)` and all `t ≥ 1`:
  `left_proj(C'.nextt ⟬fssp_both_sides n⟭ t p) = C.nextt ⟬fssp_left_side (n/2)⟭ (t − 1) p`

Uses late-border lemma: the wall at cell `n/2` appears at `t = n/2`,
but the delayed half-FSSP only needs it at relative time `L − 1 = n/2 − 1`,
i.e., absolute time `n/2 − 1 + 1 = n/2`. Just in time.
-/

namespace CellularAutomatas

open CellAutomaton

/-! ## Late-border lemma -/

/-- Speed-of-light principle: if all cells in `[p − t, p + t]` start in the
    quiescent set `S`, then cell `p` at time `t` is still in `S`.

    Proof idea: induction on `t`. Base case trivial. For the step,
    cell `p` at time `t + 1` = `δ(cell_{p−1}^t, cell_p^t, cell_{p+1}^t)`.
    By IH, all three are in `S`. By `quiescent_set`, the result is `cell_p^t ∈ S`.
    But we need the neighbors' ranges `[p−1−t, p−1+t]`, `[p+1−t, p+1+t]` ⊆ the
    initially-quiescent zone, which is `[p−(t+1), p+(t+1)]`. ∎ -/
theorem speed_of_light {α β : Type} (C : CellAutomaton α β)
    (S : Set C.Q) (hS : C.quiescent_set S)
    (c : Config C.Q)
    (p : ℤ) (t : ℕ)
    (h_init : ∀ q : ℤ, p - t ≤ q → q ≤ p + t → c q ∈ S) :
    C.nextt c t p ∈ S := by
  -- Strengthen the IH: at every time `s ≤ t`, every cell in the shrinking
  -- cone `[p − (t − s), p + (t − s)]` is still in `S`.
  suffices h : ∀ s : ℕ, s ≤ t → ∀ q : ℤ,
      p - (t - s : ℤ) ≤ q → q ≤ p + (t - s : ℤ) → C.nextt c s q ∈ S by
    have := h t (le_refl t) p (by simp) (by simp)
    exact this
  intro s hs
  induction s with
  | zero =>
    intro q hL hR
    show c q ∈ S
    exact h_init q (by simpa using hL) (by simpa using hR)
  | succ s ih =>
    intro q hL hR
    -- At time `s + 1`, cell `q` reads cells `q - 1, q, q + 1` at time `s`.
    -- All three must lie in the cone for time `s`, i.e. at distance ≤ t − s.
    have hs' : s ≤ t := Nat.le_of_succ_le hs
    have ih' := ih hs'
    -- Distances at time `s`: `t - s = (t - (s+1)) + 1`.
    have h_dist : (t - s : ℤ) = (t - (s + 1 : ℕ) : ℤ) + 1 := by
      push_cast
      omega
    show C.nextt c (s + 1) q ∈ S
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    -- Each of the three neighbours is in `S` by IH.
    have hL' : C.nextt c s (q - 1) ∈ S := by
      apply ih' (q - 1) <;> rw [h_dist] <;> omega
    have hC' : C.nextt c s q ∈ S := by
      apply ih' q <;> rw [h_dist] <;> omega
    have hR' : C.nextt c s (q + 1) ∈ S := by
      apply ih' (q + 1) <;> rw [h_dist] <;> omega
    -- Quiescence: `δ` of three S-elements (in particular the centre) stays at the centre.
    have := hS ⟨_, hL'⟩ ⟨_, hC'⟩ ⟨_, hR'⟩
    show C.δ _ _ _ ∈ S
    rw [this]
    exact hC'

/-- Late-border lemma: two configurations that agree on `(-∞, L)` produce
    identical trajectories on the left of `L` (within the light cone).

    Concretely, if `c₁ p = c₂ p` for all `p < L`, then for all `t` and `p` with
    `p + t < L`: `C.nextt c₁ t p = C.nextt c₂ t p`.

    The hypotheses about `S` are kept for the docstring narrative (cells beyond
    `L` may differ, but typically lie in a quiescent set), but they are not
    needed for this particular statement — the cone argument suffices.

    Proof idea: induction on `t`. For `t + 1`, cell `p` reads cells
    `p − 1, p, p + 1` at time `t`. Each satisfies `q' + t < L` because
    `(q + 1) + t = q + (t + 1) < L`. -/
theorem late_border {α β : Type} (C : CellAutomaton α β)
    (c₁ c₂ : Config C.Q)
    (L : ℤ)
    (h_agree : ∀ p : ℤ, p < L → c₁ p = c₂ p)
    (t : ℕ) (p : ℤ) (h_cone : p + t < L) :
    C.nextt c₁ t p = C.nextt c₂ t p := by
  induction t generalizing p with
  | zero =>
    show c₁ p = c₂ p
    simp at h_cone
    exact h_agree p h_cone
  | succ t ih =>
    show C.nextt c₁ (t + 1) p = C.nextt c₂ (t + 1) p
    rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ,
        CellAutomaton.next_apply, CellAutomaton.next_apply]
    -- All three neighbours at time `t` satisfy cone bound `< L`.
    have h1 : C.nextt c₁ t (p - 1) = C.nextt c₂ t (p - 1) := by
      apply ih; push_cast at h_cone ⊢; omega
    have h2 : C.nextt c₁ t p = C.nextt c₂ t p := by
      apply ih; push_cast at h_cone ⊢; omega
    have h3 : C.nextt c₁ t (p + 1) = C.nextt c₂ t (p + 1) := by
      apply ih; push_cast at h_cone ⊢; omega
    rw [h1, h2, h3]

/-! ## Odd-n simulation -/

section OddSimulation

variable {β : Type} [Alphabet β]
variable (C : CellAutomaton Bool？ β)
variable (hQ : C.quiescent_set { C.border, C.inner false })

/-! ### Construction of `C'`

The CA `C'` has state `Scout × C.Q` where `Scout` is a 5-state track
(`bord, quiet, R, L, wall`).

* The `Scout` component is independent of the `C` component: it is a
  pure scout-track CA over the input alphabet `(Bool × Bool)？`.
* The `C` component (the **left-half C-component**) runs `C`'s rule, but
  with neighbour reads filtered through the scout track:
  * The left neighbour is read as `C.border` if its scout is `bord` or `wall`.
  * The right neighbour is read as `C.border` if its scout is `bord` or `wall`,
    OR if the centre's scout is `wall` (i.e., the wall cell sees border on its right).

Asymmetry: only the right-side read is blocked by the centre's wall, because
the wall serves as the *right* boundary of the left half. -/

/-- 5-state scout track: `bord` (outside input), `quiet` (interior, no scout
    here), `R` (rightward-moving scout), `L` (leftward-moving scout),
    `wall` (collision point, absorbing). -/
private inductive Scout | bord | quiet | R | L | wall
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Initial scout state from a cell of the input word `fssp_both_sides`. -/
private def initScout : (Bool × Bool)？ → Scout
  | none              => Scout.bord
  | some (true,  false) => Scout.R
  | some (false, true)  => Scout.L
  | some (false, false) => Scout.quiet
  | some (true,  true)  => Scout.wall  -- n = 1 case

/-- Scout-track transition: given `(sL, sC, sR)`, return the next scout state. -/
private def scoutStep : Scout → Scout → Scout → Scout
  | _, Scout.wall, _ => Scout.wall
  | _, Scout.bord, _ => Scout.bord
  | Scout.R, _, Scout.L => Scout.wall
  | Scout.R, _, _       => Scout.R
  | _, _, Scout.L       => Scout.L
  | _, _, _             => Scout.quiet

/-- Effective left-neighbour read: returns `C.border` if the left scout
    indicates a boundary (border or wall), otherwise the actual `C` value. -/
private def qEffLeft (sL : Scout) (qL : C.Q) (_sC : Scout) : C.Q :=
  match sL with
  | Scout.bord | Scout.wall => C.border
  | _ => qL

/-- Effective right-neighbour read: returns `C.border` if the right scout
    is `bord` or `wall`, OR if the centre's scout is `wall`. -/
private def qEffRight (sR : Scout) (qR : C.Q) (sC : Scout) : C.Q :=
  match sR, sC with
  | Scout.bord, _ | Scout.wall, _ | _, Scout.wall => C.border
  | _, _ => qR

/-- The product CA `C'` for the odd-n simulation. -/
private def oddCA : CellAutomaton (Bool × Bool)？ β where
  Q := Scout × C.Q
  δ := fun ⟨sL, qL⟩ ⟨sC, qC⟩ ⟨sR, qR⟩ =>
    ( scoutStep sL sC sR,
      C.δ (qEffLeft (C := C) sL qL sC) qC (qEffRight (C := C) sR qR sC) )
  embed
    | none              => (Scout.bord,  C.border)
    | some (true,  false) => (Scout.R,    C.inner true)
    | some (false, true)  => (Scout.L,    C.inner false)
    | some (false, false) => (Scout.quiet, C.inner false)
    | some (true,  true)  => (Scout.wall,  C.inner true)
  project := fun ⟨_, q⟩ => C.project q

/-! ### Scout-track evolution

We characterize the scout component of `(oddCA C).nextt initial` over time.

Concretely, `scoutAt k t p` is defined by direct recursion mirroring the CA's
own update on the scout component, so the simulation identity
`((oddCA C).nextt initial t p).1 = scoutAt k t p` reduces to `rfl`-style
definitional unfolding.

We then derive the relevant *closed-form* facts:
* outside `[0, 2k]` the scout is always `bord`;
* `scoutAt k t k = wall` iff `t ≥ k` (collision happens exactly at time `k`);
* before time `k`, the cells of interest stay out of `wall`.
-/

/-- Initial scout pattern at `t = 0` for input `fssp_both_sides (2k + 1)`.
    `R` at the leftmost input cell, `L` at the rightmost, `bord` outside,
    `quiet` everywhere in between. -/
private def scoutAt0 (k : ℕ) (p : ℤ) : Scout :=
  if p < 0 ∨ p > 2 * k then Scout.bord
  else if p = 0 then Scout.R
  else if p = 2 * (k : ℤ) then Scout.L
  else Scout.quiet

/-- Recursive scout evolution: directly mimics `(oddCA C).next` on the scout
    component. Defined this way so that `scoutStep_scoutAt` below is by
    definition. -/
private def scoutAt (k : ℕ) : ℕ → ℤ → Scout
  | 0,     p => scoutAt0 k p
  | t + 1, p => scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1))

@[simp] private lemma scoutAt_zero (k : ℕ) (p : ℤ) :
    scoutAt k 0 p = scoutAt0 k p := rfl

@[simp] private lemma scoutAt_succ (k : ℕ) (t : ℕ) (p : ℤ) :
    scoutAt k (t + 1) p =
      scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) := rfl

/-! #### Closed-form properties of `scoutAt` -/

/-- Outside `[0, 2k]` the scout stays `bord` for all time. -/
private lemma scoutAt_bord {k : ℕ} {t : ℕ} {p : ℤ} (h : p < 0 ∨ p > 2 * k) :
    scoutAt k t p = Scout.bord := by
  induction t generalizing p with
  | zero => simp [scoutAt0, h]
  | succ t ih =>
    -- The centre at time `t` is `bord`; `scoutStep _ bord _ = bord`.
    have h_cen : scoutAt k t p = Scout.bord := ih h
    simp [scoutAt_succ, h_cen, scoutStep]

/-- Pre-collision regime: while `t < k`, the scouts have not yet met.
    `R` is at cell `t`, `L` is at cell `2k − t`, everything else in range is `quiet`. -/
private lemma scoutAt_pre {k : ℕ} (hk : k ≥ 1) :
    ∀ {t : ℕ}, t < k → ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) →
      scoutAt k t p =
        (if p = (t : ℤ) then Scout.R
         else if p = 2 * (k : ℤ) - t then Scout.L
         else Scout.quiet) := by
  have hk_pos : (1 : ℤ) ≤ k := by exact_mod_cast hk
  intro t htk
  induction t with
  | zero =>
    intro p hp_nn hp_le
    show scoutAt0 k p = _
    unfold scoutAt0
    have h_in : ¬ (p < 0 ∨ p > 2 * (k : ℤ)) := by push_neg; exact ⟨hp_nn, hp_le⟩
    split_ifs <;> first | rfl | (exfalso; omega)
  | succ t ih =>
    intro p hp_nn hp_le
    have htk' : t < k := Nat.lt_of_succ_lt htk
    have ht_lt_k : (t : ℤ) < k := by exact_mod_cast htk'
    have ht1_lt_k : ((t : ℤ) + 1) < k := by exact_mod_cast htk
    -- Lookup helper: scoutAt at any `q : ℤ`, with `bord` outside range.
    have eval : ∀ q : ℤ, scoutAt k t q =
        (if q < 0 ∨ q > 2 * (k : ℤ) then Scout.bord
         else if q = (t : ℤ) then Scout.R
         else if q = 2 * (k : ℤ) - t then Scout.L
         else Scout.quiet) := by
      intro q
      by_cases hq : q < 0 ∨ q > 2 * (k : ℤ)
      · rw [scoutAt_bord hq]; simp [hq]
      · push_neg at hq
        rw [ih htk' hq.1 hq.2]
        simp [show ¬ (q < 0 ∨ q > 2 * (k : ℤ)) by push_neg; exact hq]
    show scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) = _
    rw [eval (p - 1), eval p, eval (p + 1)]
    -- 3³ = 27 LHS branches × 3 RHS branches; many absurd via `omega`.
    split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; omega)

/-- At time `t = k`, the scouts collide at cell `k` producing `wall`;
    everything else in `[0, 2k]` is `quiet`. -/
private lemma scoutAt_at_k {k : ℕ} (hk : k ≥ 1) :
    ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) →
      scoutAt k k p =
        (if p = (k : ℤ) then Scout.wall else Scout.quiet) := by
  intro p hp_nn hp_le
  -- The boundary case follows from one application of `scoutStep` to the
  -- pre-collision configuration at `t = k − 1`.
  -- Since `k ≥ 1`, write `k = (k - 1) + 1`.
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
  -- Now goal is at time `k' + 1`.
  have hk'_lt : k' < k' + 1 := Nat.lt_succ_self _
  have hk'1_pos : k' + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le _)
  -- Lookup at time `k'` (pre-collision step) using `scoutAt_pre`.
  -- We use the form `2 * (↑k' + 1)` (rather than `2 * ((k'+1:ℕ):ℤ)`)
  -- to match the shape produced by `scoutAt_pre`.
  have eval : ∀ q : ℤ, scoutAt (k' + 1) k' q =
      (if q < 0 ∨ q > 2 * ((k' : ℤ) + 1) then Scout.bord
       else if q = (k' : ℤ) then Scout.R
       else if q = 2 * ((k' : ℤ) + 1) - k' then Scout.L
       else Scout.quiet) := by
    intro q
    by_cases hq : q < 0 ∨ q > 2 * ((k' : ℤ) + 1)
    · have hq' : q < 0 ∨ q > 2 * (k' + 1) := by
        rcases hq with h | h
        · exact Or.inl h
        · exact Or.inr (by exact_mod_cast h)
      rw [scoutAt_bord hq']
      simp [hq]
    · push_neg at hq
      have h1 : (0 : ℤ) ≤ q := hq.1
      have h2 : q ≤ 2 * ((k' + 1 : ℕ) : ℤ) := by push_cast; linarith [hq.2]
      rw [scoutAt_pre hk'1_pos hk'_lt h1 h2]
      have hgoal : ¬ (q < 0 ∨ q > 2 * ((k' : ℤ) + 1)) := by push_neg; exact hq
      simp [hgoal]
  show scoutStep (scoutAt (k' + 1) k' (p - 1)) (scoutAt (k' + 1) k' p)
        (scoutAt (k' + 1) k' (p + 1)) = _
  rw [eval (p - 1), eval p, eval (p + 1)]
  split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; push_cast at *; omega)

/-- Post-collision regime: for `t ≥ k`, the wall stays at cell `k`,
    everything else in `[0, 2k]` is `quiet`. -/
private lemma scoutAt_post {k : ℕ} (hk : k ≥ 1) :
    ∀ {t : ℕ}, t ≥ k → ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) →
      scoutAt k t p =
        (if p = (k : ℤ) then Scout.wall else Scout.quiet) := by
  -- Induction on `t - k`. Base case is `t = k`, handled by `scoutAt_at_k`.
  intro t htk
  induction t with
  | zero =>
    -- t = 0 ≥ k forces k = 0, but k ≥ 1.
    intro p _ _; exfalso; omega
  | succ t ih =>
    intro p hp_nn hp_le
    -- Two subcases: `t + 1 = k` (use `scoutAt_at_k`) or `t ≥ k` (use `ih`).
    by_cases ht_eq : t + 1 = k
    · subst ht_eq
      exact scoutAt_at_k hk hp_nn hp_le
    · have htk' : t ≥ k := by omega
      have eval : ∀ q : ℤ, scoutAt k t q =
          (if q < 0 ∨ q > 2 * (k : ℤ) then Scout.bord
           else if q = (k : ℤ) then Scout.wall
           else Scout.quiet) := by
        intro q
        by_cases hq : q < 0 ∨ q > 2 * (k : ℤ)
        · rw [scoutAt_bord hq]; simp [hq]
        · push_neg at hq
          rw [ih htk' hq.1 hq.2]
          simp [show ¬ (q < 0 ∨ q > 2 * (k : ℤ)) by push_neg; exact hq]
      show scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) = _
      rw [eval (p - 1), eval p, eval (p + 1)]
      split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; omega)

/-! #### Bridge: scout-component of `oddCA` matches `scoutAt`

We show that the scout component of `(oddCA C).nextt` on input
`fssp_both_sides (2k+1)` equals our standalone recursion `scoutAt k`. Since
`scoutAt` was defined to mirror `scoutStep` exactly, this reduces to:

* matching the **initial** values (point-by-point on the input word), and
* a one-step `scoutAt_succ`-rfl for the inductive step.
-/

/-- Initial scout-component of `oddCA` on a `fssp_both_sides (2k+1)` input
    coincides with `scoutAt0 k`, for `k ≥ 1`. -/
private lemma oddCA_embed_scout (k : ℕ) (hk : k ≥ 1) (p : ℤ) :
    ((oddCA C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).1 =
      scoutAt0 k p := by
  -- Split on whether `p` is inside the input range.
  rw [word_to_config_apply]
  by_cases h_range : p ≥ 0 ∧ p < ((fssp_both_sides (2 * k + 1)).length : ℤ)
  · -- Inside: `word_to_config` returns `some (decide (i = 0), decide (i = 2k))`
    -- where `i = p.toNat`.
    rw [dif_pos h_range]
    obtain ⟨h_p_nn, h_p_lt⟩ := h_range
    have h_len : ((fssp_both_sides (2 * k + 1)).length : ℤ) = 2 * k + 1 := by
      simp [fssp_both_sides_length]
    rw [h_len] at h_p_lt
    -- Reduce to a `getElem` evaluation.
    have h_i_lt : p.toNat < 2 * k + 1 := by
      have := Int.toNat_lt h_p_nn |>.mpr h_p_lt
      exact_mod_cast this
    rw [fssp_both_sides_getElem_eq _ _ h_i_lt]
    -- Now: `((oddCA C).embed (some (decide (i = 0), decide (i = 2k)))).1 = scoutAt0 k p`.
    -- Sub-cases based on which scout state.
    show ((oddCA C).embed (some (decide (p.toNat = 0), decide (p.toNat = 2 * k + 1 - 1)))).1 = _
    have h_2k : (2 * k + 1 - 1 : ℕ) = 2 * k := by omega
    rw [h_2k]
    -- Compute scoutAt0.
    show _ = scoutAt0 k p
    unfold scoutAt0
    have h_in : ¬ (p < 0 ∨ p > 2 * (k : ℤ)) := by push_neg; refine ⟨h_p_nn, ?_⟩; omega
    rw [if_neg h_in]
    -- Three sub-cases: `p = 0` (R), `p = 2k` (L), or interior (quiet).
    -- In each, both `decide`s reduce to literal `true`/`false`,
    -- and `(oddCA C).embed` then unfolds to a literal `(scout, q)` pair.
    by_cases hp0 : p = 0
    · subst hp0
      have h_tn0 : (0 : ℤ).toNat = 0 := rfl
      have h_dec0 : decide ((0 : ℤ).toNat = 0) = true := by rw [h_tn0]; exact decide_eq_true rfl
      have h_dec2k : decide ((0 : ℤ).toNat = 2 * k) = false := by
        rw [h_tn0]; exact decide_eq_false (by omega)
      rw [h_dec0, h_dec2k]
      show Scout.R = (if (0 : ℤ) = 0 then Scout.R else _)
      rw [if_pos rfl]
    · by_cases hp2k : p = 2 * (k : ℤ)
      · subst hp2k
        have h_tn : (2 * (k : ℤ)).toNat = 2 * k := by
          rw [show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) from by push_cast; ring]
          exact Int.toNat_natCast _
        have h_dec0 : decide ((2 * (k : ℤ)).toNat = 0) = false := by
          rw [h_tn]; exact decide_eq_false (by omega)
        have h_dec2k : decide ((2 * (k : ℤ)).toNat = 2 * k) = true := by
          rw [h_tn]; exact decide_eq_true rfl
        rw [h_dec0, h_dec2k]
        show Scout.L = _
        have hne0 : (2 * (k : ℤ)) ≠ 0 := by omega
        rw [if_neg hne0, if_pos rfl]
      · -- Interior: both decides are false → `quiet`.
        have h_tn : (p.toNat : ℤ) = p := Int.toNat_of_nonneg h_p_nn
        have h_dec0 : decide (p.toNat = 0) = false := by
          apply decide_eq_false; intro h
          apply hp0; have : (p.toNat : ℤ) = ((0 : ℕ) : ℤ) := by exact_mod_cast h
          rw [h_tn] at this; exact_mod_cast this
        have h_dec2k : decide (p.toNat = 2 * k) = false := by
          apply decide_eq_false; intro h
          apply hp2k; have : (p.toNat : ℤ) = ((2 * k : ℕ) : ℤ) := by exact_mod_cast h
          rw [h_tn] at this; push_cast at this; exact this
        rw [h_dec0, h_dec2k]
        show Scout.quiet = _
        rw [if_neg hp0, if_neg hp2k]
  · -- Outside: `word_to_config` returns `none`, embed gives `(bord, border)`.
    rw [dif_neg h_range]
    show Scout.bord = scoutAt0 k p
    unfold scoutAt0
    have h_out : p < 0 ∨ p > 2 * (k : ℤ) := by
      push_neg at h_range
      have h_len : ((fssp_both_sides (2 * k + 1)).length : ℤ) = 2 * k + 1 := by
        simp [fssp_both_sides_length]
      by_cases hp_nn : p ≥ 0
      · right; have := h_range hp_nn; rw [h_len] at this; omega
      · left; omega
    rw [if_pos h_out]

/-- The scout component of `(oddCA C).nextt` on the both-sides FSSP input
    coincides with `scoutAt k` at every time and position. -/
private lemma oddCA_scout_eq (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ) :
    ((oddCA C).nextt (⟬fssp_both_sides (2 * k + 1)⟭ : Config (oddCA C).Q) t p).1 =
      scoutAt k t p := by
  induction t generalizing p with
  | zero =>
    show (((⟬fssp_both_sides (2 * k + 1)⟭ : Config (oddCA C).Q)) p).1 = scoutAt0 k p
    show ((oddCA C).embed (word_to_config _ p)).1 = _
    exact oddCA_embed_scout C k hk p
  | succ t ih =>
    -- Step: invoke `nextt_succ` and `next_apply`; the scout component evolves
    -- as `scoutStep` of the three neighbours, matching `scoutAt_succ` definitionally.
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    -- Destructure the three neighbours into `(scout, qC)` pairs to expose
    -- `(oddCA C).δ`'s componentwise behaviour on the scout coordinate.
    set cL := (oddCA C).nextt _ t (p - 1) with hL
    set cC := (oddCA C).nextt _ t p with hC
    set cR := (oddCA C).nextt _ t (p + 1) with hR
    obtain ⟨sL, qL⟩ := cL
    obtain ⟨sC, qC⟩ := cC
    obtain ⟨sR, qR⟩ := cR
    show scoutStep sL sC sR = scoutAt k (t + 1) p
    rw [scoutAt_succ]
    -- Use IH to identify each scout component with `scoutAt k t (·)`.
    have hL' : sL = scoutAt k t (p - 1) := by
      have := ih (p - 1); rw [← hL] at this; exact this
    have hC' : sC = scoutAt k t p := by
      have := ih p; rw [← hC] at this; exact this
    have hR' : sR = scoutAt k t (p + 1) := by
      have := ih (p + 1); rw [← hR] at this; exact this
    rw [hL', hC', hR']

/-- For odd `n = 2k + 1` with `k ≥ 1`, there exists a CA `C'` over
    `(Bool × Bool)？` that, on input `fssp_both_sides n`, simulates `C`
    on `fssp_left_side (k + 1)` in the left half (cells `0..k`).

    The simulation is exact: for all `t` and `p ∈ [0, k + 1)`:
      `left_proj (C'.comp ⟬fssp_both_sides (2*k+1)⟭ t p) = C.comp ⟬fssp_left_side (k+1)⟭ t p`

    Proof idea:
    1. Construct `C'` as a product CA with a scout track + two copies of `C`.
    2. Show scouts from cell 0 and cell `2k` coincide on cell `k` at time `k`.
    3. From time `k` onward, cell `k + 1`'s left-half component is `border`.
    4. Apply `late_border` with `L = k + 1`: the wall appears at time `k = L − 1`,
       so the trajectory on `[0, k + 1)` matches `C` on `fssp_left_side (k + 1)`.
    5. The right half is symmetric (via mirroring). -/
theorem odd_simulation (k : ℕ) (hk : k ≥ 1) :
    ∃ (C' : CellAutomaton (Bool × Bool)？ β),
      C'.quiescent_set { C'.border, C'.inner (false, false) } ∧
      ∀ t : ℕ, ∀ p : ℤ, 0 ≤ p → p < (k + 1 : ℤ) →
        C'.comp ⟬fssp_both_sides (2 * k + 1)⟭ t p =
          C.comp ⟬fssp_left_side (k + 1)⟭ t p := by
  sorry

end OddSimulation

/-! ## Even-n simulation -/

section EvenSimulation

variable {β : Type} [Alphabet β]
variable (C : CellAutomaton Bool？ β)
variable (hQ : C.quiescent_set { C.border, C.inner false })

/-- For even `n = 2k` with `k ≥ 1`, there exists a CA `C'` over
    `(Bool × Bool)？` that, on input `fssp_both_sides n`, simulates `C`
    on `fssp_left_side k` in the left half — with a 1-step delay.

    The simulation is exact: for all `t ≥ 1` and `p ∈ [0, k)`:
      `left_proj (C'.comp ⟬fssp_both_sides (2*k)⟭ t p) = C.comp ⟬fssp_left_side k⟭ (t − 1) p`

    Proof idea:
    1. Construct `C'` as a product CA with a scout track + two copies of `C`.
       The half-FSSP components start quiescent and are activated 1 step late.
    2. Show scouts from cell 0 and cell `2k − 1` become adjacent (at cells
       `k − 1` and `k`) at time `k − 1`.
    3. Both cells `k − 1` and `k` install wall in the scout track at time `k − 1`.
       This makes cell `k`'s left-half component = `border` from time `k` onward.
    4. The delayed half-FSSP starts at absolute `t = 1`, so relative time
       `L − 1 = k − 1` corresponds to absolute `t = k`. The wall appears at
       absolute `t = k`. Just in time.
    5. Apply `late_border`: trajectories match for `t − 1 < k`, and from
       `t − 1 = k − 1` onward the wall is present. So all times work.
    6. The right half is symmetric (via mirroring). -/
theorem even_simulation (k : ℕ) (hk : k ≥ 1) :
    ∃ (C' : CellAutomaton (Bool × Bool)？ β),
      C'.quiescent_set { C'.border, C'.inner (false, false) } ∧
      ∀ t : ℕ, t ≥ 1 → ∀ p : ℤ, 0 ≤ p → p < (k : ℤ) →
        C'.comp ⟬fssp_both_sides (2 * k)⟭ t p =
          C.comp ⟬fssp_left_side k⟭ (t - 1) p := by
  sorry

end EvenSimulation

/-! ## Application to FSSP -/

section FSSPApplication

/-- Two-sided FSSP from one-sided FSSP.

    Given `SolvesFSSPOptimal C₁`, we construct `C₂` satisfying
    `SolvesTwoSidedFSSPOptimal C₂`.

    Proof idea:
    1. Build `C_odd` via `odd_simulation C₁` and `C_even` via `even_simulation C₁`.
    2. Run both in parallel (product CA). Project via OR.
    3. For odd `n = 2k + 1`:
       - `C_odd` fires at `2(k+1) − 2 = 2k = n − 1`. ✓
       - `C_even` has no wall installed (scouts coincide, not adjacent),
         so it simulates on full length and fires at `≥ 2n − 2 ≥ n − 1`.
       - OR gives: fires ↔ t ≥ n − 1. ✓
    4. For even `n = 2k`:
       - `C_even` fires at `1 + (2k − 2) = 2k − 1 = n − 1`. ✓
       - `C_odd` has no wall installed (scouts cross, don't coincide),
         so it simulates on full length and fires at `≥ 2n − 2 ≥ n − 1`.
       - OR gives: fires ↔ t ≥ n − 1. ✓
    5. Base cases: `n = 1` fires at `t = 0`, `n = 2` fires at `t = 1`.
       Handle separately (small finite CAs). -/
theorem two_sided_fssp_of_one_sided :
    (∃ C : CellAutomaton Bool？ Bool, SolvesFSSPOptimal C) →
    ∃ C' : CellAutomaton (Bool × Bool)？ Bool, SolvesTwoSidedFSSPOptimal C' := by
  sorry

end FSSPApplication

end CellularAutomatas
