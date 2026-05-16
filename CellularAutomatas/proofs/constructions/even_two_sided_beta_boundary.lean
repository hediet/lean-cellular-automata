import CellularAutomatas.defs
import CellularAutomatas.proofs.fssp
import CellularAutomatas.proofs.constructions.odd_two_sided_beta_boundary

/-!
# Even two-sided simulation with a moving beta boundary, delay 1

Companion to `odd_two_sided_beta_boundary.lean`. This file records the even-
length construction suggested by the `n = 8` space-time diagram in
`docs/two-sided-simulation-n8.md`.

Only simulation is considered: from the input shapes
`fssp_left_side k` and `fssp_both_sides (2 * k)`. No firing-squad correctness
is used here.

For even length `2k`, the simulated one-sided input has length `k`, with
ordinary cells `0, ..., k - 1` and first right-border cell `p = k`. The `L`
scout carries / installs `C.border` at that moving boundary.

The construction differs from the odd case in three structural ways:

1. **Adjacent collision.** `R` and `L` become adjacent (cells `k - 1` and `k`
   at simulation time `τ = k - 1`) instead of meeting on a shared middle
   cell. Both sides become a one-step `wall`.

2. **Delayed start.** The active wave from cell `0` is started one tick late
   by an *ignition rule* in the local rule. At `τ = 0` the C-component at
   `p = 0` holds `C.inner false` (`⊥`), even though the scout is `R`. The
   ignition rule fires once: when the centre scout is `R` and the left scout
   is `bord`, the next C-state is `C.embed (some true)` (i.e. `a_0`).

3. **Shifted simulation relation.** Simulation time `τ ≥ 1` corresponds to
   original time `t = τ - 1`.

The end effect, given an optimal one-sided FSSP at `t = 2k - 2`, is firing
at simulation time `τ = 2k - 1 = n - 1`, the optimal two-sided time.
-/

namespace CellularAutomatas

open CellAutomaton

namespace EvenTwoSidedBetaBoundary

variable {β : Type} [Alphabet β]

/-- Scout-control track. Identical state set to the odd construction, but the
collision logic differs. `wall` is again a one-step decay marker. -/
inductive Scout
  | bord
  | quiet
  | R
  | L
  | wall
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Initial scout state induced by a both-sided FSSP input symbol. -/
def initScout : (Bool × Bool)？ → Scout
  | none => Scout.bord
  | some (true, false) => Scout.R
  | some (false, true) => Scout.L
  | some (false, false) => Scout.quiet
  | some (true, true) => Scout.wall

/-- Even scout transition.

Differences from the odd version:
* `_, R, L => wall` (adjacent collision, the R-side becomes wall).
* `R, L, _ => wall` (adjacent collision, the L-side becomes wall).

The `R, _, L => wall` rule from the odd construction is kept as a harmless
fallback; on even inputs the scouts never meet with a single empty cell
between them, so it never fires. -/
def scoutStep : Scout → Scout → Scout → Scout
  | _, Scout.bord, _ => Scout.bord
  | _, Scout.wall, _ => Scout.quiet
  | _, Scout.R, Scout.L => Scout.wall
  | Scout.R, Scout.L, _ => Scout.wall
  | Scout.R, _, Scout.L => Scout.wall
  | Scout.R, _, _ => Scout.R
  | _, _, Scout.L => Scout.L
  | _, _, _ => Scout.quiet

/-- The even simulation CA.

The C-component evolves by `C.δ` on neighbouring C-states, with two
exceptions encoded by the local rule:

* If the *next* scout is `L`, the cell is set to `C.border` (the moving beta
  installer).
* If the centre scout is `R` and the left scout is `bord`, the cell is set
  to `C.embed (some true)` (the *ignition* rule that fires `a_0` at
  simulation time `τ = 1, p = 0`). -/
def ca (C : CellAutomaton Bool？ β) : CellAutomaton (Bool × Bool)？ β where
  Q := Scout × C.Q
  δ := fun ⟨sL, qL⟩ ⟨sC, qC⟩ ⟨sR, qR⟩ =>
    let nextScout := scoutStep sL sC sR
    let nextQ :=
      if nextScout = Scout.L then C.border
      else if sC = Scout.R ∧ sL = Scout.bord then C.embed (some true)
      else C.δ qL qC qR
    (nextScout, nextQ)
  embed
    | none => (Scout.bord, C.border)
    | some (true, false) => (Scout.R, C.inner false)        -- delayed: ⊥, not embed true
    | some (false, true) => (Scout.L, C.border)
    | some (false, false) => (Scout.quiet, C.inner false)
    | some (true, true) => (Scout.wall, C.inner false)
  project := fun ⟨_, q⟩ => C.project q

/-- Standalone scout recursion for the even input of length `2k`. -/
def scoutAt0 (k : ℕ) (p : ℤ) : Scout :=
  if p < 0 ∨ p > 2 * (k : ℤ) - 1 then Scout.bord
  else if p = 0 then Scout.R
  else if p = 2 * (k : ℤ) - 1 then Scout.L
  else Scout.quiet

/-- Standalone scout evolution mirroring the scout component of `ca`. -/
def scoutAt (k : ℕ) : ℕ → ℤ → Scout
  | 0, p => scoutAt0 k p
  | t + 1, p => scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1))

@[simp] lemma scoutAt_zero (k : ℕ) (p : ℤ) :
    scoutAt k 0 p = scoutAt0 k p := rfl

@[simp] lemma scoutAt_succ (k t : ℕ) (p : ℤ) :
    scoutAt k (t + 1) p =
      scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) := rfl

/-! ## First-track invariant (scout)

The scout row evolves through three regimes:

* **Pre-collision** (`τ < k - 1`): `R` is at cell `τ`, `L` is at cell
  `2k - 1 - τ`, and every other in-range cell is quiet.
* **Collision** (`τ = k - 1`): two adjacent walls at cells `k - 1` and `k`,
  every other in-range cell quiet.
* **Post-collision** (`τ > k - 1`): all in-range cells are quiet.
-/

/-- Closed-form row shape for the scout track.

* Pre-collision (`t < k - 1`): `R` at cell `t`, `L` at cell `2k - 1 - t`.
* Adjacent (`t = k - 1`): same as pre-collision but `R` and `L` are now
  adjacent at cells `k - 1` and `k`.
* Collision (`t = k`): two walls at cells `k - 1` and `k`.
* Post-collision (`t > k`): all in-range cells are quiet. -/
def scoutShape (k t : ℕ) (p : ℤ) : Scout :=
  if p < 0 ∨ p > 2 * (k : ℤ) - 1 then Scout.bord
  else if (t : ℤ) ≤ (k : ℤ) - 1 ∧ p = (t : ℤ) then Scout.R
  else if (t : ℤ) ≤ (k : ℤ) - 1 ∧ p = 2 * (k : ℤ) - 1 - (t : ℤ) then Scout.L
  else if (t : ℤ) = (k : ℤ) ∧ (p = (k : ℤ) - 1 ∨ p = (k : ℤ)) then Scout.wall
  else Scout.quiet

/-- Outside `[0, 2k - 1]` the scout track is permanently `bord`. -/
lemma scoutAt_bord {k t : ℕ} {p : ℤ} (h : p < 0 ∨ p > 2 * (k : ℤ) - 1) :
    scoutAt k t p = Scout.bord := by
  induction t generalizing p with
  | zero => simp [scoutAt0, h]
  | succ t ih =>
    have h_cen : scoutAt k t p = Scout.bord := ih h
    simp [scoutAt_succ, h_cen, scoutStep]

/-- Pre-collision: while `t ≤ k - 1` (and `k ≥ 2`), `R` is at cell `t`,
`L` is at cell `2k - 1 - t`, every other in-range cell is quiet. At
`t = k - 1` the two scouts are adjacent (cells `k - 1` and `k`) but neither
becomes `wall` until the *next* step. -/
lemma scoutAt_pre {k : ℕ} (hk : k ≥ 2) :
    ∀ {t : ℕ}, (t : ℤ) ≤ (k : ℤ) - 1 → ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) - 1 →
      scoutAt k t p =
        (if p = (t : ℤ) then Scout.R
         else if p = 2 * (k : ℤ) - 1 - (t : ℤ) then Scout.L
         else Scout.quiet) := by
  intro t htk
  induction t with
  | zero =>
    intro p hp_nn hp_le
    show scoutAt0 k p = _
    unfold scoutAt0
    have h_in : ¬ (p < 0 ∨ p > 2 * (k : ℤ) - 1) := by push_neg; exact ⟨hp_nn, hp_le⟩
    split_ifs <;> first | rfl | (exfalso; omega)
  | succ t ih =>
    intro p hp_nn hp_le
    have htk' : (t : ℤ) ≤ (k : ℤ) - 1 := by push_cast at htk; omega
    have htk'_strict : (t : ℤ) < (k : ℤ) - 1 := by push_cast at htk; omega
    have eval : ∀ q : ℤ, scoutAt k t q =
        (if q < 0 ∨ q > 2 * (k : ℤ) - 1 then Scout.bord
         else if q = (t : ℤ) then Scout.R
         else if q = 2 * (k : ℤ) - 1 - (t : ℤ) then Scout.L
         else Scout.quiet) := by
      intro q
      by_cases hq : q < 0 ∨ q > 2 * (k : ℤ) - 1
      · rw [scoutAt_bord hq]; simp [hq]
      · push_neg at hq
        rw [ih htk' hq.1 hq.2]
        simp [show ¬ (q < 0 ∨ q > 2 * (k : ℤ) - 1) by push_neg; exact hq]
    show scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) = _
    rw [eval (p - 1), eval p, eval (p + 1)]
    -- Prevents R-meets-L collision at this step: R at t, L at 2k-1-t, gap = 2k-1-2t,
    -- and we have t < k - 1 (from t + 1 ≤ k - 1 hypothesis), so gap > 1 strictly,
    -- meaning at p neither (sC=R, sR=L) nor (sL=R, sC=L) can both hold.
    split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; omega)

/-- At collision time `t = k`, the only non-quiet in-range cells are the two
adjacent walls at `k - 1` and `k`. -/
lemma scoutAt_at_collision {k : ℕ} (hk : k ≥ 2) :
    ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) - 1 →
      scoutAt k k p =
        (if p = (k : ℤ) - 1 ∨ p = (k : ℤ) then Scout.wall else Scout.quiet) := by
  intro p hp_nn hp_le
  -- Compute scoutAt k k from scoutAt k (k-1), which is the adjacent pre-collision row.
  rcases Nat.exists_eq_add_of_le hk with ⟨k', hk_eq⟩
  -- hk_eq : 2 + k' = k. So k = k' + 2, k - 1 = k' + 1.
  have hk_eq' : k = k' + 2 := by omega
  have hk1_eq : (k - 1 : ℕ) = k' + 1 := by omega
  have hk1_le : ((k - 1 : ℕ) : ℤ) ≤ (k : ℤ) - 1 := by
    have : k - 1 = k' + 1 := hk1_eq
    push_cast; omega
  have h_kn1_int : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
    have : k - 1 = k' + 1 := hk1_eq
    push_cast; omega
  -- Evaluate scoutAt k (k-1) using scoutAt_pre.
  have eval : ∀ q : ℤ, scoutAt k (k - 1) q =
      (if q < 0 ∨ q > 2 * (k : ℤ) - 1 then Scout.bord
       else if q = (k : ℤ) - 1 then Scout.R
       else if q = (k : ℤ) then Scout.L
       else Scout.quiet) := by
    intro q
    by_cases hq : q < 0 ∨ q > 2 * (k : ℤ) - 1
    · rw [scoutAt_bord hq]; simp [hq]
    · push_neg at hq
      rw [scoutAt_pre hk hk1_le hq.1 hq.2]
      have h_2k_sub : 2 * (k : ℤ) - 1 - ((k - 1 : ℕ) : ℤ) = (k : ℤ) := by
        rw [h_kn1_int]; ring
      rw [h_2k_sub, h_kn1_int]
      simp [show ¬ (q < 0 ∨ q > 2 * (k : ℤ) - 1) by push_neg; exact hq]
  -- Now expand scoutAt k k using scoutAt_succ on (k - 1) + 1 = k.
  have h_succ : scoutAt k k p = scoutStep (scoutAt k (k - 1) (p - 1))
      (scoutAt k (k - 1) p) (scoutAt k (k - 1) (p + 1)) := by
    have : k = (k - 1) + 1 := by omega
    rw [this]; rfl
  rw [h_succ, eval (p - 1), eval p, eval (p + 1)]
  split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; omega)

/-- After collision (`t > k`), all in-range cells are quiet. -/
lemma scoutAt_after {k : ℕ} (hk : k ≥ 2) :
    ∀ {t : ℕ}, k < t → ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) - 1 →
      scoutAt k t p = Scout.quiet := by
  intro t htk
  induction t with
  | zero => omega
  | succ t ih =>
    intro p hp_nn hp_le
    by_cases ht_eq : t = k
    · -- Previous row is the collision row.
      have eval : ∀ q : ℤ, scoutAt k t q =
          (if q < 0 ∨ q > 2 * (k : ℤ) - 1 then Scout.bord
           else if q = (k : ℤ) - 1 ∨ q = (k : ℤ) then Scout.wall
           else Scout.quiet) := by
        intro q
        by_cases hq : q < 0 ∨ q > 2 * (k : ℤ) - 1
        · rw [scoutAt_bord hq]; simp [hq]
        · push_neg at hq
          rw [ht_eq, scoutAt_at_collision hk hq.1 hq.2]
          simp [show ¬ (q < 0 ∨ q > 2 * (k : ℤ) - 1) by push_neg; exact hq]
      show scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) = Scout.quiet
      rw [eval (p - 1), eval p, eval (p + 1)]
      split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; omega)
    · have htk' : k < t := by omega
      have eval : ∀ q : ℤ, scoutAt k t q =
          (if q < 0 ∨ q > 2 * (k : ℤ) - 1 then Scout.bord else Scout.quiet) := by
        intro q
        by_cases hq : q < 0 ∨ q > 2 * (k : ℤ) - 1
        · rw [scoutAt_bord hq]; simp [hq]
        · push_neg at hq
          rw [ih htk' hq.1 hq.2]
          simp [show ¬ (q < 0 ∨ q > 2 * (k : ℤ) - 1) by push_neg; exact hq]
      show scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) = Scout.quiet
      rw [eval (p - 1), eval p, eval (p + 1)]
      split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; omega)

/-- First-track invariant. -/
theorem scout_inv (k : ℕ) (hk : k ≥ 2) (t : ℕ) (p : ℤ) :
    scoutAt k t p = scoutShape k t p := by
  unfold scoutShape
  by_cases h_out : p < 0 ∨ p > 2 * (k : ℤ) - 1
  · rw [scoutAt_bord h_out]
    simp [h_out]
  · push_neg at h_out
    by_cases hle : (t : ℤ) ≤ (k : ℤ) - 1
    · -- Pre-collision (including adjacent at t = k - 1).
      have hne_collision : ¬ ((t : ℤ) = (k : ℤ)) := by omega
      rw [scoutAt_pre hk hle h_out.1 h_out.2]
      simp [h_out, hle, hne_collision]
    · push_neg at hle
      by_cases heq : t = k
      · -- Collision row.
        rw [heq, scoutAt_at_collision hk h_out.1 h_out.2]
        have hk_int : ¬ ((k : ℤ) ≤ (k : ℤ) - 1) := by omega
        have hk_int_eq : ((k : ℕ) : ℤ) = (k : ℤ) := rfl
        simp [h_out, hk_int]
      · have hgt : k < t := by omega
        rw [scoutAt_after hk hgt h_out.1 h_out.2]
        have hnot_le : ¬ ((t : ℤ) ≤ (k : ℤ) - 1) := by omega
        have hnot_eq : ¬ ((t : ℤ) = (k : ℤ)) := by exact_mod_cast (Ne.symm (Nat.ne_of_lt hgt))
        simp [h_out, hnot_le, hnot_eq]

/-! ## Second-track invariant (C-component)

The C-component, in the delayed regime, splits into three regions for `τ ≥ 1`:

* `p ≤ τ - 1`: the right-going cone from cell `0`, equal to the original
  one-sided execution `originalQ` at original time `τ - 1`.
* `τ - 1 < p < 2k - 1 - (τ - 1)`: untouched cells, still `C.inner false`.
* `2k - 1 - (τ - 1) ≤ p ≤ 2k - 1`: the beta region installed by the `L`
  scout, equal to `C.border`.

At `τ = 0`, the row is exactly the embedding of `fssp_both_sides (2k)`.
-/

/-- C-component recursion mirroring the C-component of `ca`. -/
def qAt (C : CellAutomaton Bool？ β) (k : ℕ) : ℕ → ℤ → C.Q
  | 0, p => ((ca C).embed (word_to_config (fssp_both_sides (2 * k)) p)).2
  | t + 1, p =>
      let sL := scoutAt k t (p - 1)
      let sC := scoutAt k t p
      let sR := scoutAt k t (p + 1)
      let nextScout := scoutStep sL sC sR
      if nextScout = Scout.L then C.border
      else if sC = Scout.R ∧ sL = Scout.bord then C.embed (some true)
      else C.δ (qAt C k t (p - 1)) (qAt C k t p) (qAt C k t (p + 1))

@[simp] lemma qAt_zero (C : CellAutomaton Bool？ β) (k : ℕ) (p : ℤ) :
    qAt C k 0 p =
      ((ca C).embed (word_to_config (fssp_both_sides (2 * k)) p)).2 := rfl

@[simp] lemma qAt_succ (C : CellAutomaton Bool？ β) (k t : ℕ) (p : ℤ) :
    qAt C k (t + 1) p =
      (let sL := scoutAt k t (p - 1)
       let sC := scoutAt k t p
       let sR := scoutAt k t (p + 1)
       let nextScout := scoutStep sL sC sR
       if nextScout = Scout.L then C.border
       else if sC = Scout.R ∧ sL = Scout.bord then C.embed (some true)
       else C.δ (qAt C k t (p - 1)) (qAt C k t p) (qAt C k t (p + 1))) := rfl

/-- Original one-sided execution on `fssp_left_side k`. -/
def originalQ (C : CellAutomaton Bool？ β) (k t : ℕ) (p : ℤ) : C.Q :=
  C.nextt (⟬fssp_left_side k⟭ : Config C.Q) t p

/-- In the original one-sided run on `fssp_left_side k`, any cell strictly
to the right of the cone from cell `0` is still equal to its initial value. -/
lemma originalQ_passive (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false })
    (k t : ℕ) {p : ℤ} (hp : (t : ℤ) < p) :
    originalQ C k t p = (⟬fssp_left_side k⟭ : Config C.Q) p := by
  unfold originalQ
  apply OddTwoSidedBetaBoundary.passive_cone_exact C
    { C.border, C.inner false } hQ
  intro q hqL _hqR
  have hq_pos : 0 < q := by omega
  rw [CellAutomaton.embed_config_apply, word_to_config_apply]
  by_cases h_range : q ≥ 0 ∧ q < (fssp_left_side k).length
  · rw [dif_pos h_range]
    have h_i_lt : q.toNat < (fssp_left_side k).length := by
      have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
      have hq_cast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq_nonneg
      rw [← Int.ofNat_lt]
      rw [hq_cast]
      exact h_range.2
    have hq_ne_zero : q.toNat ≠ 0 := by
      intro h
      have : q = 0 := by
        have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
        have hq_cast := Int.toNat_of_nonneg hq_nonneg
        omega
      omega
    right
    change C.embed (some ((fssp_left_side k)[q.toNat])) = C.embed (some false)
    congr
    rw [OddTwoSidedBetaBoundary.fssp_left_side_getElem_eq k q.toNat h_i_lt]
    exact decide_eq_false hq_ne_zero
  · rw [dif_neg h_range]
    left
    rfl

/-- Closed-form row shape for the C-track.

For `τ = 0`, this is just the embedding of `fssp_both_sides (2k)`. For
`τ ≥ 1`, the three regions are:

* `p ≤ τ - 1`: cone from cell `0`, equal to `originalQ C k (τ - 1) p`.
  (This branch also covers `p < 0`, where `originalQ` evolves to whatever
  the original CA would compute on the left of `fssp_left_side`.)
* `τ - 1 < p < 2k - 1 - τ`: untouched, `C.inner false`.
* `2k - 1 - τ ≤ p`: beta region (covers both the installed boundary inside
  `[0, 2k - 1]` and OOB on the right, where `qAt` stays `C.border` by
  quiescence). -/
def qShape (C : CellAutomaton Bool？ β) (k : ℕ) : ℕ → ℤ → C.Q
  | 0, p => ((ca C).embed (word_to_config (fssp_both_sides (2 * k)) p)).2
  | (t + 1), p =>
      if p ≤ (t : ℤ) then originalQ C k t p
      else if 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ p then C.border
      else C.inner false

/-- For nearby cells (`q ≤ t + 2`), the cone branch of `qShape` agrees with
`originalQ`. -/
lemma qShape_eq_originalQ_near (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false })
    (k : ℕ) (hk : k ≥ 2) (t : ℕ) (q : ℤ) (hq : q ≤ (t : ℤ) + 2) :
    qShape C k (t + 1) q = originalQ C k t q := by
  show (if q ≤ (t : ℤ) then originalQ C k t q
        else if 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ q then C.border
        else C.inner false) = originalQ C k t q
  by_cases hqt : q ≤ (t : ℤ)
  · rw [if_pos hqt]
  · rw [if_neg hqt]
    push_neg at hqt
    -- q > t, so by passive cone the original is its initial value.
    have hq_passive := originalQ_passive C hQ k t hqt
    rw [hq_passive]
    rw [CellAutomaton.embed_config_apply, word_to_config_apply]
    have h_len : ((fssp_left_side k).length : ℤ) = k := by
      rw [fssp_left_side_length]
    by_cases h_in_left : q ≥ 0 ∧ q < ((fssp_left_side k).length : ℤ)
    · -- q in valid range: q > 0 and q ≤ k - 1, so symbol = false → ⊥.
      rw [dif_pos h_in_left]
      rw [h_len] at h_in_left
      have hq_le_km1 : q ≤ (k : ℤ) - 1 := by omega
      have h_thresh_int : 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) = 2 * (k : ℤ) - 2 - (t : ℤ) := by
        push_cast; ring
      rw [h_thresh_int]
      by_cases h_beta : 2 * (k : ℤ) - 2 - (t : ℤ) ≤ q
      · -- Beta region AND q ≤ k - 1: forces q ≥ k from t ≥ k - 1, contradiction.
        exfalso
        have ht_ge : (t : ℤ) ≥ (k : ℤ) - 1 := by omega
        have hq_ge_k : q ≥ (k : ℤ) := by omega
        omega
      · rw [if_neg h_beta]
        have hq_pos : 0 < q := by omega
        have hq_toNat_ne0 : q.toNat ≠ 0 := by
          intro h
          have h_cast : (q.toNat : ℤ) = 0 := by exact_mod_cast h
          rw [Int.toNat_of_nonneg (le_of_lt hq_pos)] at h_cast
          omega
        have hi_left : q.toNat < (fssp_left_side k).length := by
          have hq_cast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (le_of_lt hq_pos)
          have hlt : (q.toNat : ℤ) < (k : ℤ) := by rw [hq_cast]; omega
          rw [fssp_left_side_length]
          exact_mod_cast hlt
        change C.inner false = C.embed (some ((fssp_left_side k)[q.toNat]'hi_left))
        rw [OddTwoSidedBetaBoundary.fssp_left_side_getElem_eq k q.toNat hi_left]
        rw [decide_eq_false hq_toNat_ne0]
        rfl
    · -- q out of fssp_left_side range: original = β.
      rw [dif_neg h_in_left]
      push_neg at h_in_left
      have hq_nn : q ≥ 0 := by omega
      have hq_ge : q ≥ k := by
        have := h_in_left hq_nn; rw [h_len] at this; omega
      have ht_ge : (t : ℤ) ≥ (k : ℤ) - 2 := by omega
      have h_beta : 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ q := by push_cast; omega
      rw [if_pos h_beta]
      rfl

/-- Stepping `scoutShape` via `scoutStep` gives the next-time `scoutShape`. -/
lemma scoutStep_scoutShape (k : ℕ) (hk : k ≥ 2) (t : ℕ) (p : ℤ) :
    scoutStep (scoutShape k t (p - 1)) (scoutShape k t p) (scoutShape k t (p + 1)) =
      scoutShape k (t + 1) p := by
  rw [← scout_inv k hk t (p - 1), ← scout_inv k hk t p, ← scout_inv k hk t (p + 1)]
  rw [← scoutAt_succ]
  exact scout_inv k hk (t + 1) p

/-- Initial row of the C-track diagram. -/
lemma q_inv_zero (C : CellAutomaton Bool？ β) (k : ℕ) (p : ℤ) :
    qAt C k 0 p = qShape C k 0 p := rfl

/-- Closed-form for `qShape` at `t + 1` in the cone branch. -/
lemma qShape_succ_cone (C : CellAutomaton Bool？ β) (k t : ℕ) {p : ℤ} (hp : p ≤ (t : ℤ)) :
    qShape C k (t + 1) p = originalQ C k t p := by
  show (if p ≤ (t : ℤ) then originalQ C k t p
        else if 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ p then C.border
        else C.inner false) = originalQ C k t p
  rw [if_pos hp]

/-- Closed-form for `qShape` at `t + 1` in the beta branch. -/
lemma qShape_succ_beta (C : CellAutomaton Bool？ β) (k t : ℕ) {p : ℤ}
    (h_ncone : (t : ℤ) < p) (h_beta : 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ p) :
    qShape C k (t + 1) p = C.border := by
  show (if p ≤ (t : ℤ) then originalQ C k t p
        else if 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ p then C.border
        else C.inner false) = C.border
  rw [if_neg (not_le.mpr h_ncone), if_pos h_beta]

/-- Closed-form for `qShape` at `t + 1` in the interior branch. -/
lemma qShape_succ_interior (C : CellAutomaton Bool？ β) (k t : ℕ) {p : ℤ}
    (h_ncone : (t : ℤ) < p) (h_nbeta : p < 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ)) :
    qShape C k (t + 1) p = C.inner false := by
  show (if p ≤ (t : ℤ) then originalQ C k t p
        else if 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ p then C.border
        else C.inner false) = C.inner false
  rw [if_neg (not_le.mpr h_ncone), if_neg (not_le.mpr h_nbeta)]

/-- `scoutShape (t+1) p = L` only if it's the moving-boundary cell. -/
lemma scoutShape_L_iff (k t : ℕ) (p : ℤ) :
    scoutShape k (t + 1) p = Scout.L ↔
      ¬ (p < 0 ∨ p > 2 * (k : ℤ) - 1) ∧
        ¬ (((t + 1 : ℕ) : ℤ) ≤ (k : ℤ) - 1 ∧ p = ((t + 1 : ℕ) : ℤ)) ∧
        ((t + 1 : ℕ) : ℤ) ≤ (k : ℤ) - 1 ∧
        p = 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) := by
  unfold scoutShape
  by_cases h1 : p < 0 ∨ p > 2 * (k : ℤ) - 1
  · rw [if_pos h1]
    refine ⟨fun h => (Scout.noConfusion h), fun ⟨hn, _, _, _⟩ => absurd h1 hn⟩
  · rw [if_neg h1]
    by_cases h2 : ((t + 1 : ℕ) : ℤ) ≤ (k : ℤ) - 1 ∧ p = ((t + 1 : ℕ) : ℤ)
    · rw [if_pos h2]
      refine ⟨fun h => (Scout.noConfusion h), fun ⟨_, hn, _, _⟩ => absurd h2 hn⟩
    · rw [if_neg h2]
      by_cases h3 : ((t + 1 : ℕ) : ℤ) ≤ (k : ℤ) - 1 ∧ p = 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ)
      · rw [if_pos h3]
        exact ⟨fun _ => ⟨h1, h2, h3.1, h3.2⟩, fun _ => rfl⟩
      · rw [if_neg h3]
        constructor
        · intro h
          by_cases h4 : ((t + 1 : ℕ) : ℤ) = (k : ℤ) ∧
              (p = (k : ℤ) - 1 ∨ p = (k : ℤ))
          · rw [if_pos h4] at h; exact (Scout.noConfusion h)
          · rw [if_neg h4] at h; exact (Scout.noConfusion h)
        · intro ⟨_, _, ha, hb⟩
          exact absurd ⟨ha, hb⟩ h3

/-- The ignition condition (`sC = R ∧ sL = bord`) holds at row `t`, position
`p` only at the unique boot cell `(t, p) = (0, 0)`. -/
lemma scoutShape_ignition_iff (k t : ℕ) (hk : k ≥ 2) (p : ℤ) :
    (scoutShape k t p = Scout.R ∧ scoutShape k t (p - 1) = Scout.bord) ↔
      (t = 0 ∧ p = 0) := by
  constructor
  · intro ⟨hsC, hsL⟩
    -- sC = R forces in-range ∧ t ≤ k-1 ∧ p = t.
    have hR : ¬ (p < 0 ∨ p > 2 * (k : ℤ) - 1) ∧
              (t : ℤ) ≤ (k : ℤ) - 1 ∧ p = (t : ℤ) := by
      unfold scoutShape at hsC
      by_cases h1 : p < 0 ∨ p > 2 * (k : ℤ) - 1
      · rw [if_pos h1] at hsC; exact (Scout.noConfusion hsC)
      · rw [if_neg h1] at hsC
        by_cases h2 : (t : ℤ) ≤ (k : ℤ) - 1 ∧ p = (t : ℤ)
        · exact ⟨h1, h2.1, h2.2⟩
        · rw [if_neg h2] at hsC
          by_cases h3 : (t : ℤ) ≤ (k : ℤ) - 1 ∧ p = 2 * (k : ℤ) - 1 - (t : ℤ)
          · rw [if_pos h3] at hsC; exact (Scout.noConfusion hsC)
          · rw [if_neg h3] at hsC
            by_cases h4 : (t : ℤ) = (k : ℤ) ∧ (p = (k : ℤ) - 1 ∨ p = (k : ℤ))
            · rw [if_pos h4] at hsC; exact (Scout.noConfusion hsC)
            · rw [if_neg h4] at hsC; exact (Scout.noConfusion hsC)
    obtain ⟨h_in, ht_le, hp_eq⟩ := hR
    push_neg at h_in
    have hp_nn : (0 : ℤ) ≤ p := h_in.1
    -- sL = bord forces p - 1 OOB.
    have hsL_oob : p - 1 < 0 ∨ p - 1 > 2 * (k : ℤ) - 1 := by
      unfold scoutShape at hsL
      by_cases hL1 : p - 1 < 0 ∨ p - 1 > 2 * (k : ℤ) - 1
      · exact hL1
      · exfalso
        rw [if_neg hL1] at hsL
        split_ifs at hsL <;> exact (Scout.noConfusion hsL)
    have hp1_lt : p - 1 < 0 := by
      rcases hsL_oob with h | h
      · exact h
      · exfalso; have h_le : p ≤ 2 * (k : ℤ) - 1 := h_in.2; omega
    have hp0 : p = 0 := by omega
    have ht0 : t = 0 := by
      have : (t : ℤ) = 0 := by rw [← hp_eq]; exact hp0
      exact_mod_cast this
    exact ⟨ht0, hp0⟩
  · intro ⟨ht, hp⟩
    subst ht; subst hp
    refine ⟨?_, ?_⟩
    · show (if (0 : ℤ) < 0 ∨ (0 : ℤ) > 2 * (k : ℤ) - 1 then Scout.bord
            else if ((0 : ℕ) : ℤ) ≤ (k : ℤ) - 1 ∧ (0 : ℤ) = ((0 : ℕ) : ℤ) then Scout.R
            else if ((0 : ℕ) : ℤ) ≤ (k : ℤ) - 1 ∧
                   (0 : ℤ) = 2 * (k : ℤ) - 1 - ((0 : ℕ) : ℤ) then Scout.L
            else if ((0 : ℕ) : ℤ) = (k : ℤ) ∧
                   ((0 : ℤ) = (k : ℤ) - 1 ∨ (0 : ℤ) = (k : ℤ)) then Scout.wall
            else Scout.quiet) = Scout.R
      have hk' : (k : ℤ) ≥ 2 := by exact_mod_cast hk
      have h1 : ¬ ((0 : ℤ) < 0 ∨ (0 : ℤ) > 2 * (k : ℤ) - 1) := by
        push_neg; refine ⟨le_refl _, by omega⟩
      have h2 : ((0 : ℕ) : ℤ) ≤ (k : ℤ) - 1 ∧ (0 : ℤ) = ((0 : ℕ) : ℤ) := by
        refine ⟨by push_cast; omega, by push_cast⟩
      rw [if_neg h1, if_pos h2]
    · show (if (0 - 1 : ℤ) < 0 ∨ (0 - 1 : ℤ) > 2 * (k : ℤ) - 1 then Scout.bord
            else _) = Scout.bord
      rw [if_pos (Or.inl (by norm_num))]

/-- The C-component projection of `(ca C).embed` is always quiescent. -/
lemma ca_embed_q_in_quiescent (C : CellAutomaton Bool？ β) (x : (Bool × Bool)？) :
    ((ca C).embed x).2 ∈ ({C.border, C.inner false} : Set C.Q) := by
  rcases x with _ | ⟨a, b⟩
  · left; rfl
  · cases a <;> cases b
    · right; rfl
    · left; rfl
    · right; rfl
    · right; rfl

/-- The right neighbour at row 0 is in `{β, ⊥}` (in the quiescent set). -/
lemma qShape_zero_in_quiescent (C : CellAutomaton Bool？ β) (k : ℕ) (p : ℤ) :
    qShape C k 0 p ∈ ({C.border, C.inner false} : Set C.Q) :=
  ca_embed_q_in_quiescent C _

/-- The C-track value at row `0` of the `fssp_both_sides` input. -/
lemma qShape_zero_eq (C : CellAutomaton Bool？ β) (k : ℕ) (hk : k ≥ 2) (p : ℤ) :
    qShape C k 0 p =
      if p = 2 * (k : ℤ) - 1 ∨ ¬ (0 ≤ p ∧ p < 2 * (k : ℤ)) then C.border
      else C.inner false := by
  show ((ca C).embed (word_to_config (fssp_both_sides (2 * k)) p)).2 = _
  rw [word_to_config_apply]
  have h_len : ((fssp_both_sides (2 * k)).length : ℤ) = 2 * (k : ℤ) := by
    rw [fssp_both_sides_length]; push_cast; ring
  by_cases h_in : p ≥ 0 ∧ p < ((fssp_both_sides (2 * k)).length : ℤ)
  · rw [dif_pos h_in]
    rw [h_len] at h_in
    have hp_nn : (0 : ℤ) ≤ p := h_in.1
    have hp_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_nn
    have hi_nat : p.toNat < 2 * k := by
      have h_lt : (p.toNat : ℤ) < 2 * (k : ℤ) := by rw [hp_toNat]; exact h_in.2
      exact_mod_cast h_lt
    rw [CellularAutomatas.fssp_both_sides_getElem_eq _ _ hi_nat]
    by_cases hp_last : p = 2 * (k : ℤ) - 1
    · have h_toNat_eq : p.toNat = 2 * k - 1 := by
        have : (p.toNat : ℤ) = 2 * (k : ℤ) - 1 := by rw [hp_toNat]; exact hp_last
        have h_eq : (p.toNat : ℤ) = ((2 * k - 1 : ℕ) : ℤ) := by
          rw [this]; push_cast; omega
        exact_mod_cast h_eq
      rw [h_toNat_eq]
      have hne : 2 * k - 1 ≠ 0 := by omega
      rw [decide_eq_false hne, decide_eq_true rfl]
      rw [if_pos (Or.inl hp_last)]
      rfl
    · have h_toNat_ne : p.toNat ≠ 2 * k - 1 := by
        intro h
        apply hp_last
        have h_cast : (p.toNat : ℤ) = ((2 * k - 1 : ℕ) : ℤ) := by exact_mod_cast h
        rw [hp_toNat] at h_cast
        rw [h_cast]; push_cast; omega
      rw [decide_eq_false h_toNat_ne]
      have h_not_oob : ¬ (p = 2 * (k : ℤ) - 1 ∨ ¬ (0 ≤ p ∧ p < 2 * (k : ℤ))) := by
        push_neg
        refine ⟨hp_last, hp_nn, h_in.2⟩
      rw [if_neg h_not_oob]
      by_cases hp_zero : p.toNat = 0
      · rw [decide_eq_true hp_zero]; rfl
      · rw [decide_eq_false hp_zero]; rfl
  · rw [dif_neg h_in]
    have h_oob : p = 2 * (k : ℤ) - 1 ∨ ¬ (0 ≤ p ∧ p < 2 * (k : ℤ)) := by
      right; rw [← h_len]; exact h_in
    rw [if_pos h_oob]
    rfl

/-- Second-track invariant. Mirrors the odd version `q_inv` but with the
delayed-time relation, the τ = 0 base case handled by definition, and an
extra ignition case at τ = 0 → τ = 1, p = 0. -/
theorem q_inv (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false })
    (k : ℕ) (hk : k ≥ 2) (t : ℕ) (p : ℤ) :
    qAt C k t p = qShape C k t p := by
  induction t generalizing p with
  | zero => exact q_inv_zero C k p
  | succ t ih =>
    show (let sL := scoutAt k t (p - 1)
          let sC := scoutAt k t p
          let sR := scoutAt k t (p + 1)
          let nextScout := scoutStep sL sC sR
          if nextScout = Scout.L then C.border
          else if sC = Scout.R ∧ sL = Scout.bord then C.embed (some true)
          else C.δ (qAt C k t (p - 1)) (qAt C k t p) (qAt C k t (p + 1))) =
        qShape C k (t + 1) p
    rw [scout_inv k hk t (p - 1), scout_inv k hk t p, scout_inv k hk t (p + 1)]
    rw [ih (p - 1), ih p, ih (p + 1)]
    show (if scoutStep (scoutShape k t (p - 1)) (scoutShape k t p) (scoutShape k t (p + 1)) =
              Scout.L then C.border
          else if scoutShape k t p = Scout.R ∧ scoutShape k t (p - 1) = Scout.bord then
            C.embed (some true)
          else C.δ (qShape C k t (p - 1)) (qShape C k t p) (qShape C k t (p + 1))) =
        qShape C k (t + 1) p
    rw [scoutStep_scoutShape k hk t p]
    by_cases hpA : p ≤ (t : ℤ)
    · -- CASE A: cone. qShape (t+1) p = originalQ k t p.
      rw [qShape_succ_cone C k t hpA]
      -- nextScout ≠ L: in cone p ≤ t, the L-condition would force t ≥ k-1 ∧ t ≤ k-2.
      have h_not_L : scoutShape k (t + 1) p ≠ Scout.L := by
        intro h
        rw [scoutShape_L_iff] at h
        obtain ⟨_, _, h_le, h_eq⟩ := h
        push_cast at h_le h_eq; omega
      rw [if_neg h_not_L]
      -- Sub-case: ignition.
      by_cases h_ign : scoutShape k t p = Scout.R ∧ scoutShape k t (p - 1) = Scout.bord
      · rw [if_pos h_ign]
        -- Ignition forces (t, p) = (0, 0).
        rw [scoutShape_ignition_iff k t hk] at h_ign
        obtain ⟨ht0, hp0⟩ := h_ign
        subst ht0; subst hp0
        -- originalQ k 0 0 = embed of fssp_left_side at index 0 = some true.
        show C.embed (some true) = originalQ C k 0 0
        unfold originalQ
        rw [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply, word_to_config_apply]
        have hk_pos : 0 < k := by omega
        have h_in : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < ((fssp_left_side k).length : ℤ) := by
          refine ⟨le_refl _, ?_⟩
          rw [fssp_left_side_length]; exact_mod_cast hk_pos
        rw [dif_pos h_in]
        have h_idx_lt : (0 : ℤ).toNat < (fssp_left_side k).length := by
          rw [fssp_left_side_length]; exact hk_pos
        change C.embed (some true) =
            C.embed (some ((fssp_left_side k)[(0 : ℤ).toNat]'h_idx_lt))
        congr
        rw [OddTwoSidedBetaBoundary.fssp_left_side_getElem_eq k _ h_idx_lt]
        rfl
      · rw [if_neg h_ign]
        -- δ branch on neighbour qShape values.
        -- For t = 0: neighbours are embed of fssp_both_sides → in {β, ⊥}.
        -- For t ≥ 1: use qShape_eq_originalQ_near to map to originalQ (t-1) (p±1),
        --   then nextt_succ collapses to originalQ t p.
        cases t with
        | zero =>
          -- p ≤ 0. Sub-cases: p = 0 (would be ignition), or p < 0.
          have hp_neg : p < 0 := by
            by_contra hpos
            push_neg at hpos
            have : p = 0 := by omega
            apply h_ign
            rw [this]
            rw [scoutShape_ignition_iff k 0 hk]
            exact ⟨rfl, rfl⟩
          -- p < 0 ⇒ qShape 0 p = β (OOB), neighbours in quiescent set.
          have h_q_eq : qShape C k 0 p = C.border := by
            rw [qShape_zero_eq C k hk p]
            rw [if_pos (Or.inr (fun ⟨h, _⟩ => absurd h (not_le.mpr hp_neg)))]
          have h_qm : qShape C k 0 (p - 1) ∈ ({C.border, C.inner false} : Set C.Q) :=
            qShape_zero_in_quiescent C k _
          have h_qp : qShape C k 0 (p + 1) ∈ ({C.border, C.inner false} : Set C.Q) :=
            qShape_zero_in_quiescent C k _
          have h_q_in : qShape C k 0 p ∈ ({C.border, C.inner false} : Set C.Q) := by
            rw [h_q_eq]; left; rfl
          have h_δ : C.δ (qShape C k 0 (p - 1)) (qShape C k 0 p) (qShape C k 0 (p + 1)) =
              qShape C k 0 p := hQ ⟨_, h_qm⟩ ⟨_, h_q_in⟩ ⟨_, h_qp⟩
          rw [h_δ, h_q_eq]
          -- originalQ k 0 p = β at p < 0.
          show C.border = originalQ C k 0 p
          unfold originalQ
          rw [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply, word_to_config_apply]
          have h_oob : ¬ (p ≥ 0 ∧ p < ((fssp_left_side k).length : ℤ)) := by
            intro ⟨hp_nn, _⟩; omega
          rw [dif_neg h_oob]
          rfl
        | succ t' =>
          -- t = t' + 1 ≥ 1. Apply qShape_eq_originalQ_near (with index t').
          have h_qm : qShape C k (t' + 1) (p - 1) = originalQ C k t' (p - 1) :=
            qShape_eq_originalQ_near C hQ k hk t' (p - 1) (by push_cast at hpA; omega)
          have h_q : qShape C k (t' + 1) p = originalQ C k t' p :=
            qShape_eq_originalQ_near C hQ k hk t' p (by push_cast at hpA; omega)
          have h_qp : qShape C k (t' + 1) (p + 1) = originalQ C k t' (p + 1) :=
            qShape_eq_originalQ_near C hQ k hk t' (p + 1) (by push_cast at hpA; omega)
          rw [h_qm, h_q, h_qp]
          show C.δ (originalQ C k t' (p - 1)) (originalQ C k t' p) (originalQ C k t' (p + 1)) =
              originalQ C k (t' + 1) p
          unfold originalQ
          rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    · push_neg at hpA
      by_cases hpB : 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ p
      · -- CASE B: beta.
        rw [qShape_succ_beta C k t hpA hpB]
        -- Sub-case nextScout = L.
        by_cases h_L : scoutShape k (t + 1) p = Scout.L
        · rw [if_pos h_L]
        · rw [if_neg h_L]
          -- Ignition: scoutShape t p = R requires p = t, but p > t.
          have h_not_ign : ¬ (scoutShape k t p = Scout.R ∧
              scoutShape k t (p - 1) = Scout.bord) := by
            rw [scoutShape_ignition_iff k t hk]
            intro ⟨ht0, hp0⟩
            subst ht0; subst hp0
            omega
          rw [if_neg h_not_ign]
          -- δ branch: all three qShape values are in {β, ⊥}.
          have hpB' : 2 * (k : ℤ) - 2 - (t : ℤ) ≤ p := by
            have := hpB
            push_cast at this
            omega
          -- Strengthen via h_L to push p outside the L-installation cell.
          have hp_ge_t : 2 * (k : ℤ) - 1 - (t : ℤ) ≤ p := by
            by_contra h_lt
            push_neg at h_lt
            -- p = 2k - 2 - t (from hpB' and h_lt).
            have hp_eq : p = 2 * (k : ℤ) - 2 - (t : ℤ) := by omega
            -- If t + 1 ≤ k - 1, scoutShape (t+1) p = L, contradicting h_L.
            by_cases h_tk : (t : ℤ) + 1 ≤ (k : ℤ) - 1
            · apply h_L
              rw [scoutShape_L_iff]
              refine ⟨?_, ?_, ?_, ?_⟩
              · push_neg
                refine ⟨by omega, by omega⟩
              · intro ⟨_, h_eq⟩
                push_cast at h_eq
                omega
              · push_cast
                omega
              · push_cast
                omega
            · push_neg at h_tk
              -- t + 1 > k - 1 means t ≥ k - 1. But hpA: p > t, p = 2k - 2 - t,
              -- so 2k - 2 - t > t, i.e., t < k - 1. Contradiction.
              push_cast at hpA
              omega
          have h_q_eq : qShape C k t p = C.border := by
            cases t with
            | zero =>
              -- t = 0, p ≥ 2k - 1.
              rw [qShape_zero_eq C k hk p]
              by_cases hp_eq : p = 2 * (k : ℤ) - 1
              · rw [if_pos (Or.inl hp_eq)]
              · rw [if_pos (Or.inr (fun ⟨_, h2⟩ => by omega))]
            | succ t'' =>
              have h_ncone : (t'' : ℤ) < p := by push_cast at hpA; omega
              have h_beta : 2 * (k : ℤ) - 1 - ((t'' + 1 : ℕ) : ℤ) ≤ p := by
                have := hp_ge_t
                push_cast at this ⊢
                omega
              exact qShape_succ_beta C k t'' h_ncone h_beta
          have h_qm_in : qShape C k t (p - 1) ∈ ({C.border, C.inner false} : Set C.Q) := by
            cases t with
            | zero => exact qShape_zero_in_quiescent C k _
            | succ t'' =>
              have h_ncone : (t'' : ℤ) < p - 1 := by push_cast at hpA; omega
              by_cases h_beta : 2 * (k : ℤ) - 1 - ((t'' + 1 : ℕ) : ℤ) ≤ p - 1
              · rw [qShape_succ_beta C k t'' h_ncone h_beta]; left; rfl
              · push_neg at h_beta
                rw [qShape_succ_interior C k t'' h_ncone h_beta]; right; rfl
          have h_qp_in : qShape C k t (p + 1) ∈ ({C.border, C.inner false} : Set C.Q) := by
            cases t with
            | zero => exact qShape_zero_in_quiescent C k _
            | succ t'' =>
              have h_ncone : (t'' : ℤ) < p + 1 := by push_cast at hpA; omega
              have h_beta : 2 * (k : ℤ) - 1 - ((t'' + 1 : ℕ) : ℤ) ≤ p + 1 := by
                have := hpB'
                push_cast at this ⊢
                omega
              rw [qShape_succ_beta C k t'' h_ncone h_beta]; left; rfl
          have h_q_in : qShape C k t p ∈ ({C.border, C.inner false} : Set C.Q) := by
            rw [h_q_eq]; left; rfl
          have h_δ : C.δ (qShape C k t (p - 1)) (qShape C k t p) (qShape C k t (p + 1)) =
              qShape C k t p := hQ ⟨_, h_qm_in⟩ ⟨_, h_q_in⟩ ⟨_, h_qp_in⟩
          rw [h_δ, h_q_eq]
      · push_neg at hpB
        -- CASE C: interior.
        rw [qShape_succ_interior C k t hpA hpB]
        -- nextScout ≠ L (p ≠ 2k-1-(t+1) since p < that).
        have h_not_L : scoutShape k (t + 1) p ≠ Scout.L := by
          intro h
          rw [scoutShape_L_iff] at h
          obtain ⟨_, _, _, h_eq⟩ := h
          omega
        rw [if_neg h_not_L]
        have h_not_ign : ¬ (scoutShape k t p = Scout.R ∧
            scoutShape k t (p - 1) = Scout.bord) := by
          rw [scoutShape_ignition_iff k t hk]
          intro ⟨ht0, hp0⟩
          subst ht0; subst hp0
          omega
        rw [if_neg h_not_ign]
        -- All three neighbours are interior ⊥.
        have h_qm : qShape C k t (p - 1) = C.inner false := by
          cases t with
          | zero =>
            -- t = 0: p > 0 and p < 2k - 2, so p - 1 ∈ [0, 2k - 3]; never the last marker.
            rw [qShape_zero_eq C k hk (p - 1)]
            have h_neq_last : ¬ (p - 1 = 2 * (k : ℤ) - 1) := by
              push_cast at hpB; omega
            have h_in : (0 : ℤ) ≤ p - 1 ∧ p - 1 < 2 * (k : ℤ) := by
              push_cast at hpA hpB; omega
            have h_neither : ¬ (p - 1 = 2 * (k : ℤ) - 1 ∨ ¬ (0 ≤ p - 1 ∧ p - 1 < 2 * (k : ℤ))) := by
              push_neg; exact ⟨h_neq_last, h_in.1, h_in.2⟩
            rw [if_neg h_neither]
          | succ t'' =>
            have h_ncone : (t'' : ℤ) < p - 1 := by push_cast at hpA; omega
            have h_nbeta : p - 1 < 2 * (k : ℤ) - 1 - ((t'' + 1 : ℕ) : ℤ) := by
              push_cast at hpB ⊢; omega
            exact qShape_succ_interior C k t'' h_ncone h_nbeta
        have h_q : qShape C k t p = C.inner false := by
          cases t with
          | zero =>
            rw [qShape_zero_eq C k hk p]
            have h_neq_last : ¬ (p = 2 * (k : ℤ) - 1) := by push_cast at hpB; omega
            have h_in : (0 : ℤ) ≤ p ∧ p < 2 * (k : ℤ) := by
              push_cast at hpA hpB; omega
            have h_neither : ¬ (p = 2 * (k : ℤ) - 1 ∨ ¬ (0 ≤ p ∧ p < 2 * (k : ℤ))) := by
              push_neg; exact ⟨h_neq_last, h_in.1, h_in.2⟩
            rw [if_neg h_neither]
          | succ t'' =>
            have h_ncone : (t'' : ℤ) < p := by push_cast at hpA; omega
            have h_nbeta : p < 2 * (k : ℤ) - 1 - ((t'' + 1 : ℕ) : ℤ) := by
              push_cast at hpB ⊢; omega
            exact qShape_succ_interior C k t'' h_ncone h_nbeta
        have h_qp : qShape C k t (p + 1) = C.inner false := by
          cases t with
          | zero =>
            rw [qShape_zero_eq C k hk (p + 1)]
            have h_neq_last : ¬ (p + 1 = 2 * (k : ℤ) - 1) := by push_cast at hpB; omega
            have h_in : (0 : ℤ) ≤ p + 1 ∧ p + 1 < 2 * (k : ℤ) := by
              push_cast at hpA hpB; omega
            have h_neither : ¬ (p + 1 = 2 * (k : ℤ) - 1 ∨ ¬ (0 ≤ p + 1 ∧ p + 1 < 2 * (k : ℤ))) := by
              push_neg; exact ⟨h_neq_last, h_in.1, h_in.2⟩
            rw [if_neg h_neither]
          | succ t'' =>
            have h_ncone : (t'' : ℤ) < p + 1 := by push_cast at hpA; omega
            have h_nbeta : p + 1 < 2 * (k : ℤ) - 1 - ((t'' + 1 : ℕ) : ℤ) := by
              push_cast at hpB ⊢; omega
            exact qShape_succ_interior C k t'' h_ncone h_nbeta
        rw [h_qm, h_q, h_qp]
        have h_mem : (C.inner false : C.Q) ∈ ({C.border, C.inner false} : Set C.Q) := Or.inr rfl
        exact hQ ⟨_, h_mem⟩ ⟨_, h_mem⟩ ⟨_, h_mem⟩

/-! ## Bridging back to the actual CA evolution -/

/-- The simulation CA's full state at time `τ`, position `p`, equals
`(scoutAt k τ p, qAt C k τ p)`. -/
lemma ca_nextt_eq (C : CellAutomaton Bool？ β) (k : ℕ) (hk : k ≥ 2) (t : ℕ) (p : ℤ) :
    (ca C).nextt (⟬fssp_both_sides (2 * k)⟭ : Config (ca C).Q) t p =
      (scoutAt k t p, qAt C k t p) := by
  induction t generalizing p with
  | zero =>
    show ((ca C).embed (word_to_config (fssp_both_sides (2 * k)) p)) =
         (scoutAt0 k p, qAt C k 0 p)
    have h2 : qAt C k 0 p =
        ((ca C).embed (word_to_config (fssp_both_sides (2 * k)) p)).2 := rfl
    apply Prod.ext
    · -- .1 case: scout component
      show ((ca C).embed (word_to_config (fssp_both_sides (2 * k)) p)).1 = scoutAt0 k p
      rw [word_to_config_apply]
      by_cases hp_range : p ≥ 0 ∧ p < ((fssp_both_sides (2 * k)).length : ℤ)
      · rw [dif_pos hp_range]
        have h_len : ((fssp_both_sides (2 * k)).length : ℤ) = 2 * k := by
          simp [fssp_both_sides_length]
        have hp_pos : 0 ≤ p := hp_range.1
        have hp_lt : p < 2 * (k : ℤ) := by rw [h_len] at hp_range; exact hp_range.2
        have hi : p.toNat < 2 * k := by
          have hp_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_pos
          have : (p.toNat : ℤ) < ((2 * k : ℕ) : ℤ) := by rw [hp_toNat]; push_cast; omega
          exact_mod_cast this
        have hi' : p.toNat < (fssp_both_sides (2 * k)).length := by
          rw [fssp_both_sides_length]; exact hi
        rw [fssp_both_sides_getElem_eq _ _ hi]
        unfold scoutAt0
        have h_in : ¬ (p < 0 ∨ p > 2 * (k : ℤ) - 1) := by push_neg; refine ⟨hp_pos, by omega⟩
        rw [if_neg h_in]
        by_cases hp0 : p = 0
        · subst hp0
          have h_tn0 : ((0 : ℤ).toNat : ℕ) = 0 := rfl
          rw [h_tn0]
          have h_dec0 : decide ((0 : ℕ) = 0) = true := decide_eq_true rfl
          have h_2k_ne : (0 : ℕ) ≠ 2 * k - 1 := by omega
          have h_dec_ne : decide ((0 : ℕ) = 2 * k - 1) = false := decide_eq_false h_2k_ne
          rw [h_dec0, h_dec_ne]
          rfl
        · by_cases hp_last : p = 2 * (k : ℤ) - 1
          · -- p = 2k - 1: rightmost cell, scout is L.
            have hp_last_nat : p.toNat = 2 * k - 1 := by
              have hp_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_pos
              have h_eq : (p.toNat : ℤ) = ((2 * k - 1 : ℕ) : ℤ) := by
                rw [hp_toNat, hp_last]; push_cast; omega
              exact_mod_cast h_eq
            rw [hp_last_nat]
            have h_ne0 : 2 * k - 1 ≠ 0 := by omega
            have h_dec0 : decide (2 * k - 1 = 0) = false := decide_eq_false h_ne0
            have h_dec_eq : decide (2 * k - 1 = 2 * k - 1) = true := decide_eq_true rfl
            rw [h_dec0, h_dec_eq]
            rw [if_neg hp0, if_pos hp_last]
            rfl
          · -- Interior: 0 < p < 2k - 1.
            have h_p_pos : 0 < p := lt_of_le_of_ne hp_pos (Ne.symm hp0)
            have h_p_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_pos
            have h_toNat_ne0 : p.toNat ≠ 0 := by
              intro h; have : (p.toNat : ℤ) = 0 := by exact_mod_cast h
              omega
            have h_toNat_ne_last : p.toNat ≠ 2 * k - 1 := by
              intro h
              have : (p.toNat : ℤ) = ((2 * k - 1 : ℕ) : ℤ) := by exact_mod_cast h
              rw [h_p_toNat] at this
              have h_2k_eq : ((2 * k - 1 : ℕ) : ℤ) = 2 * (k : ℤ) - 1 := by push_cast; omega
              rw [h_2k_eq] at this
              exact hp_last this
            have h_dec0 : decide (p.toNat = 0) = false := decide_eq_false h_toNat_ne0
            have h_dec_ne : decide (p.toNat = 2 * k - 1) = false :=
              decide_eq_false h_toNat_ne_last
            rw [h_dec0, h_dec_ne]
            rw [if_neg hp0, if_neg hp_last]
            rfl
      · -- Out of range
        rw [dif_neg hp_range]
        show (Scout.bord) = scoutAt0 k p
        unfold scoutAt0
        have h_len : ((fssp_both_sides (2 * k)).length : ℤ) = 2 * k := by
          simp [fssp_both_sides_length]
        have h_out : p < 0 ∨ p > 2 * (k : ℤ) - 1 := by
          push_neg at hp_range
          by_cases hp_nn : p ≥ 0
          · right
            have := hp_range hp_nn
            rw [h_len] at this; omega
          · left; omega
        rw [if_pos h_out]
    · -- .2 case
      show ((ca C).embed (word_to_config (fssp_both_sides (2 * k)) p)).2 = qAt C k 0 p
      rw [h2]
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    rw [ih (p - 1), ih p, ih (p + 1)]
    show ((ca C).δ ⟨scoutAt k t (p - 1), qAt C k t (p - 1)⟩
                    ⟨scoutAt k t p, qAt C k t p⟩
                    ⟨scoutAt k t (p + 1), qAt C k t (p + 1)⟩) =
        (scoutAt k (t + 1) p, qAt C k (t + 1) p)
    rfl

/-! ## Spec -/

/-- The simulation CA's quiescent set is `{ (ca C).border, (ca C).inner (false, false) }`. -/
theorem spec_quiescent_set (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false }) :
    (ca C).quiescent_set { (ca C).border, (ca C).inner (false, false) } := by
  -- Quiescent set: { (Scout.bord, C.border), (Scout.quiet, C.inner false) }
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  obtain ⟨sa, qa⟩ := a
  obtain ⟨sb, qb⟩ := b
  obtain ⟨sc, qc⟩ := c
  show (ca C).δ ⟨sa, qa⟩ ⟨sb, qb⟩ ⟨sc, qc⟩ = ⟨sb, qb⟩
  have h_decompose : ∀ {s : Scout} {q : C.Q},
      (s, q) ∈ ({(ca C).border, (ca C).inner (false, false)} : Set ((ca C).Q)) →
      (s = Scout.bord ∧ q = C.border) ∨
      (s = Scout.quiet ∧ q = C.inner false) := by
    intro s q h
    rcases h with h | h
    · left
      have h1 : ((ca C).border : (ca C).Q) = (Scout.bord, C.border) := rfl
      rw [h1] at h
      injection h with h1 h2
      exact ⟨h1, h2⟩
    · right
      have h1 : ((ca C).inner (false, false) : (ca C).Q) = (Scout.quiet, C.inner false) := rfl
      rw [h1] at h
      injection h with h1 h2
      exact ⟨h1, h2⟩
  have ha' := h_decompose ha
  have hb' := h_decompose hb
  have hc' := h_decompose hc
  have h_qa : qa ∈ ({C.border, C.inner false} : Set C.Q) := by
    rcases ha' with ⟨_, h⟩ | ⟨_, h⟩
    · left; exact h
    · right; exact h
  have h_qb : qb ∈ ({C.border, C.inner false} : Set C.Q) := by
    rcases hb' with ⟨_, h⟩ | ⟨_, h⟩
    · left; exact h
    · right; exact h
  have h_qc : qc ∈ ({C.border, C.inner false} : Set C.Q) := by
    rcases hc' with ⟨_, h⟩ | ⟨_, h⟩
    · left; exact h
    · right; exact h
  apply Prod.ext
  · -- .1: scoutStep sa sb sc = sb
    show scoutStep sa sb sc = sb
    rcases hb' with ⟨hb1, _⟩ | ⟨hb1, _⟩ <;>
      rcases ha' with ⟨ha1, _⟩ | ⟨ha1, _⟩ <;>
      rcases hc' with ⟨hc1, _⟩ | ⟨hc1, _⟩ <;>
      subst_vars <;> rfl
  · -- .2: ignition does not fire (sb ∈ {bord, quiet}), nextScout ≠ L,
    -- and δ on the quiescent set returns sb's C-state.
    show (if scoutStep sa sb sc = Scout.L then C.border
          else if sb = Scout.R ∧ sa = Scout.bord then C.embed (some true)
          else C.δ qa qb qc) = qb
    have h_not_L : scoutStep sa sb sc ≠ Scout.L := by
      rcases hb' with ⟨hb1, _⟩ | ⟨hb1, _⟩ <;>
        rcases ha' with ⟨ha1, _⟩ | ⟨ha1, _⟩ <;>
        rcases hc' with ⟨hc1, _⟩ | ⟨hc1, _⟩ <;>
        subst_vars <;> decide
    have h_not_ignite : ¬ (sb = Scout.R ∧ sa = Scout.bord) := by
      rcases hb' with ⟨hb1, _⟩ | ⟨hb1, _⟩ <;>
        subst_vars <;> intro ⟨h, _⟩ <;> exact (Scout.noConfusion h)
    rw [if_neg h_not_L, if_neg h_not_ignite]
    exact hQ ⟨qa, h_qa⟩ ⟨qb, h_qb⟩ ⟨qc, h_qc⟩

/-- The even construction simulates `C` on `fssp_left_side k` with a one-step delay.

For `k ≥ 2`, the constructed CA on `fssp_both_sides (2k)` simulates `C` on
`fssp_left_side k` with a one-step delay, inside the right-going light cone
from cell `0`. The simulated boundary cell is `p = k`.

`τ ≥ 1` is essential: at `τ = 0` the C-track has not been ignited yet, and
the cone is empty. The relation `original time = τ - 1` reflects the delay. -/
theorem spec_comp (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false })
    (k : ℕ) (hk : k ≥ 2) (τ : ℕ) (p : ℤ)
    (hτ : 1 ≤ τ) (hp_nn : 0 ≤ p) (hp_k : p ≤ (k : ℤ))
    (hp_cone : p ≤ ((τ : ℤ) - 1)) :
    (ca C).comp ⟬fssp_both_sides (2 * k)⟭ τ p =
      C.comp ⟬fssp_left_side k⟭ (τ - 1) p := by
  -- Simulation. Reduces, via ca_nextt_eq and q_inv, to a qShape lookup.
  rw [CellAutomaton.comp_apply, CellAutomaton.comp_apply]
  show (ca C).project ((ca C).nextt _ τ p) = C.project (C.nextt _ (τ - 1) p)
  have h_proj :
      (ca C).project ((ca C).nextt ⟬fssp_both_sides (2 * k)⟭ τ p) =
        C.project ((ca C).nextt ⟬fssp_both_sides (2 * k)⟭ τ p).2 := rfl
  rw [h_proj, ca_nextt_eq C k hk τ p]
  show C.project (qAt C k τ p) = C.project (C.nextt _ (τ - 1) p)
  rw [q_inv C hQ k hk τ p]
  -- For τ ≥ 1, the cone case of qShape returns originalQ k (τ - 1) p.
  obtain ⟨τ', rfl⟩ : ∃ τ', τ = τ' + 1 :=
    ⟨τ - 1, by omega⟩
  show C.project (qShape C k (τ' + 1) p) = C.project (C.nextt _ ((τ' + 1 : ℕ) - 1) p)
  have h_τ_sub : ((τ' + 1 : ℕ) : ℤ) - 1 = (τ' : ℤ) := by push_cast; ring
  have hp_le_τ' : p ≤ (τ' : ℤ) := by rw [← h_τ_sub]; exact hp_cone
  show C.project (qShape C k (τ' + 1) p) = C.project (C.nextt _ τ' p)
  have h_qshape : qShape C k (τ' + 1) p = originalQ C k τ' p := by
    show (if p ≤ (τ' : ℤ) then originalQ C k τ' p
          else if 2 * (k : ℤ) - 1 - ((τ' + 1 : ℕ) : ℤ) ≤ p then C.border
          else C.inner false) = originalQ C k τ' p
    rw [if_pos hp_le_τ']
  rw [h_qshape]
  rfl

end EvenTwoSidedBetaBoundary

end CellularAutomatas
