import CellularAutomatas.defs
import CellularAutomatas.proofs.fssp

/-!
# Odd two-sided simulation with a moving beta boundary

This file records the corrected odd-length construction suggested by the
`n = 7` space-time diagram in `docs/two-sided-simulation-n7.md`.

The point of the construction is only simulation from the input shapes
`fssp_left_side (k + 1)` and `fssp_both_sides (2 * k + 1)`. No firing-squad
correctness is used here.

For odd length `2k + 1`, the left half has cells `0, ..., k`. We also track
cell `k + 1`, the first right-border cell of the one-sided input. The `L`
scout carries/install the actual CA border state at that moving boundary.
After the scouts meet, the collision marker is transient; the deposited border
state is what continues the simulation.
-/

namespace CellularAutomatas

open CellAutomaton

namespace OddTwoSidedBetaBoundary

variable {β : Type} [Alphabet β]

/-- Scout-control track for the odd simulation.

`wall` is only a one-step collision marker/stopping signal. It is not an
absorbing boundary marker. The real simulated boundary is carried by the
`C.border` value installed by the `L` scout in the C-component. -/
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

/-- Odd scout transition.

The moving scouts disappear after passing. When `R` and `L` meet with one empty
cell between them in the previous row, the middle cell becomes `wall` for one
step. On the next step, `wall` decays to `quiet`. -/
def scoutStep : Scout → Scout → Scout → Scout
  | _, Scout.bord, _ => Scout.bord
  | _, Scout.wall, _ => Scout.quiet
  | Scout.R, _, Scout.L => Scout.wall
  | Scout.R, _, _ => Scout.R
  | _, _, Scout.L => Scout.L
  | _, _, _ => Scout.quiet

/-- The corrected odd simulation CA.

The C-component normally evolves by `C.δ` on the actual neighbouring
C-components. The single exception is the cell whose *next* scout state is `L`:
that cell is assigned `C.border`, making `L` a moving installer of the beta
boundary. -/
def ca (C : CellAutomaton Bool？ β) : CellAutomaton (Bool × Bool)？ β where
  Q := Scout × C.Q
  δ := fun ⟨sL, qL⟩ ⟨sC, qC⟩ ⟨sR, qR⟩ =>
    let nextScout := scoutStep sL sC sR
    let nextQ := if nextScout = Scout.L then C.border else C.δ qL qC qR
    (nextScout, nextQ)
  embed
    | none => (Scout.bord, C.border)
    | some (true, false) => (Scout.R, C.inner true)
    | some (false, true) => (Scout.L, C.border)
    | some (false, false) => (Scout.quiet, C.inner false)
    | some (true, true) => (Scout.wall, C.inner true)
  project := fun ⟨_, q⟩ => C.project q

/-- Standalone scout recursion for the odd input of length `2k + 1`. -/
def scoutAt0 (k : ℕ) (p : ℤ) : Scout :=
  if p < 0 ∨ p > 2 * (k : ℤ) then Scout.bord
  else if p = 0 then Scout.R
  else if p = 2 * (k : ℤ) then Scout.L
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

/-! ## Two diagram invariants

The corrected diagram is fully described by two row-shape invariants.

* `scoutShape` describes the first track: the `R`/`L` scouts move toward each
  other, collide into a one-step `wall`, and then disappear.
* `qShape` describes the second track: the left cone is the original `C`
  execution, the untouched gap is `C.inner false`, and the right cone is the
  installed beta boundary `C.border`.
-/

/-- Closed-form row shape for the scout track. -/
def scoutShape (k t : ℕ) (p : ℤ) : Scout :=
  if p < 0 ∨ p > 2 * (k : ℤ) then Scout.bord
  else if (t : ℤ) < k ∧ p = (t : ℤ) then Scout.R
  else if (t : ℤ) < k ∧ p = 2 * (k : ℤ) - (t : ℤ) then Scout.L
  else if (t : ℤ) = k ∧ p = (k : ℤ) then Scout.wall
  else Scout.quiet

/-- Outside `[0, 2k]` the scout track is permanently `bord`. -/
lemma scoutAt_bord {k t : ℕ} {p : ℤ} (h : p < 0 ∨ p > 2 * (k : ℤ)) :
    scoutAt k t p = Scout.bord := by
  induction t generalizing p with
  | zero => simp [scoutAt0, h]
  | succ t ih =>
    have h_cen : scoutAt k t p = Scout.bord := ih h
    simp [scoutAt_succ, h_cen, scoutStep]

/-- Before collision, `R` is at `t`, `L` is at `2k - t`, and every other
in-range cell is quiet. -/
lemma scoutAt_pre {k : ℕ} (hk : k ≥ 1) :
    ∀ {t : ℕ}, t < k → ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) →
      scoutAt k t p =
        (if p = (t : ℤ) then Scout.R
         else if p = 2 * (k : ℤ) - (t : ℤ) then Scout.L
         else Scout.quiet) := by
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
    have eval : ∀ q : ℤ, scoutAt k t q =
        (if q < 0 ∨ q > 2 * (k : ℤ) then Scout.bord
         else if q = (t : ℤ) then Scout.R
         else if q = 2 * (k : ℤ) - (t : ℤ) then Scout.L
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

/-- At collision time, the only non-quiet in-range cell is the transient wall
at `k`. -/
lemma scoutAt_at_k {k : ℕ} (hk : k ≥ 1) :
    ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) →
      scoutAt k k p =
        (if p = (k : ℤ) then Scout.wall else Scout.quiet) := by
  intro p hp_nn hp_le
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
  have hk'_lt : k' < k' + 1 := Nat.lt_succ_self _
  have hk'1_pos : k' + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le _)
  have eval : ∀ q : ℤ, scoutAt (k' + 1) k' q =
      (if q < 0 ∨ q > 2 * ((k' : ℤ) + 1) then Scout.bord
       else if q = (k' : ℤ) then Scout.R
       else if q = 2 * ((k' : ℤ) + 1) - (k' : ℤ) then Scout.L
       else Scout.quiet) := by
    intro q
    by_cases hq : q < 0 ∨ q > 2 * ((k' : ℤ) + 1)
    · have hq' : q < 0 ∨ q > 2 * (k' + 1 : ℕ) := by
        rcases hq with h | h
        · exact Or.inl h
        · exact Or.inr (by exact_mod_cast h)
      rw [scoutAt_bord hq']
      simp [hq]
    · push_neg at hq
      have h1 : 0 ≤ q := hq.1
      have h2 : q ≤ 2 * (((k' + 1 : ℕ) : ℤ)) := by push_cast; linarith [hq.2]
      rw [scoutAt_pre hk'1_pos hk'_lt h1 h2]
      simp [show ¬ (q < 0 ∨ q > 2 * ((k' : ℤ) + 1)) by push_neg; exact hq]
  show scoutStep (scoutAt (k' + 1) k' (p - 1)) (scoutAt (k' + 1) k' p)
      (scoutAt (k' + 1) k' (p + 1)) = _
  rw [eval (p - 1), eval p, eval (p + 1)]
  split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; push_cast at *; omega)

/-- After collision, the transient wall has disappeared; all in-range cells are
quiet. -/
lemma scoutAt_after {k : ℕ} (hk : k ≥ 1) :
    ∀ {t : ℕ}, k < t → ∀ {p : ℤ}, 0 ≤ p → p ≤ 2 * (k : ℤ) →
      scoutAt k t p = Scout.quiet := by
  intro t htk
  induction t with
  | zero =>
    omega
  | succ t ih =>
    intro p hp_nn hp_le
    by_cases ht_eq : t = k
    · have eval : ∀ q : ℤ, scoutAt k t q =
          (if q < 0 ∨ q > 2 * (k : ℤ) then Scout.bord
           else if q = (k : ℤ) then Scout.wall
           else Scout.quiet) := by
        intro q
        by_cases hq : q < 0 ∨ q > 2 * (k : ℤ)
        · rw [scoutAt_bord hq]; simp [hq]
        · push_neg at hq
          rw [ht_eq, scoutAt_at_k hk hq.1 hq.2]
          simp [show ¬ (q < 0 ∨ q > 2 * (k : ℤ)) by push_neg; exact hq]
      show scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) = Scout.quiet
      rw [eval (p - 1), eval p, eval (p + 1)]
      split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; omega)
    · have htk' : k < t := by omega
      have eval : ∀ q : ℤ, scoutAt k t q =
          (if q < 0 ∨ q > 2 * (k : ℤ) then Scout.bord else Scout.quiet) := by
        intro q
        by_cases hq : q < 0 ∨ q > 2 * (k : ℤ)
        · rw [scoutAt_bord hq]; simp [hq]
        · push_neg at hq
          rw [ih htk' hq.1 hq.2]
          simp [show ¬ (q < 0 ∨ q > 2 * (k : ℤ)) by push_neg; exact hq]
      show scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1)) = Scout.quiet
      rw [eval (p - 1), eval p, eval (p + 1)]
      split_ifs <;> first | rfl | (simp only [scoutStep]; rfl) | (exfalso; omega)

/-- First-track invariant: `scoutAt` is exactly the scout row shown in the
diagram. -/
theorem scout_inv (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ) :
    scoutAt k t p = scoutShape k t p := by
  unfold scoutShape
  by_cases h_out : p < 0 ∨ p > 2 * (k : ℤ)
  · rw [scoutAt_bord h_out]
    simp [h_out]
  · push_neg at h_out
    by_cases hlt : t < k
    · have hltz : (t : ℤ) < (k : ℤ) := by exact_mod_cast hlt
      have hnez : ¬ ((t : ℤ) = (k : ℤ)) := by omega
      rw [scoutAt_pre hk hlt h_out.1 h_out.2]
      simp [h_out, hltz, hnez]
    · by_cases heq : t = k
      · rw [heq, scoutAt_at_k hk h_out.1 h_out.2]
        have hnot_lt : ¬ ((k : ℤ) < (k : ℤ)) := by omega
        simp [h_out, hnot_lt]
      · have hgt : k < t := by omega
        rw [scoutAt_after hk hgt h_out.1 h_out.2]
        have hnot_lt : ¬ ((t : ℤ) < (k : ℤ)) := by exact_mod_cast (not_lt.mpr (Nat.le_of_lt hgt))
        have hnot_eq : ¬ ((t : ℤ) = (k : ℤ)) := by exact_mod_cast (Ne.symm (Nat.ne_of_lt hgt))
        simp [h_out, hnot_lt, hnot_eq]

/-- C-component of the corrected construction, written as a standalone
recursion that uses `scoutAt` for the first track. -/
def qAt (C : CellAutomaton Bool？ β) (k : ℕ) : ℕ → ℤ → C.Q
  | 0, p => ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).2
  | t + 1, p =>
      let nextScout := scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1))
      if nextScout = Scout.L then C.border
      else C.δ (qAt C k t (p - 1)) (qAt C k t p) (qAt C k t (p + 1))

@[simp] lemma qAt_zero (C : CellAutomaton Bool？ β) (k : ℕ) (p : ℤ) :
    qAt C k 0 p =
      ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).2 := rfl

@[simp] lemma qAt_succ (C : CellAutomaton Bool？ β) (k t : ℕ) (p : ℤ) :
    qAt C k (t + 1) p =
      (let nextScout := scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1))
       if nextScout = Scout.L then C.border
       else C.δ (qAt C k t (p - 1)) (qAt C k t p) (qAt C k t (p + 1))) := rfl

/-- Original one-sided execution, used as the `Q` region in the second-track
diagram. This includes border cells outside the one-sided word; e.g. the cell
`k + 1` may evolve to an `e_t` state once the left cone reaches it. -/
def originalQ (C : CellAutomaton Bool？ β) (k t : ℕ) (p : ℤ) : C.Q :=
  C.nextt (⟬fssp_left_side (k + 1)⟭ : Config C.Q) t p

/-- The one-sided input has the left marker at index `0` and `false`
everywhere else in range. -/
lemma fssp_left_side_getElem_eq (n i : ℕ) (hi : i < (fssp_left_side n).length) :
    (fssp_left_side n)[i]'hi = decide (i = 0) := by
  rcases n with _ | m
  · simp [fssp_left_side] at hi
  · show ([true] ++ List.replicate m false)[i]'(by simpa [fssp_left_side] using hi) =
        decide (i = 0)
    cases i with
    | zero => simp
    | succ i => simp

/-- Exact passive-cone principle: if the whole light cone starts inside a
quiescent set, then the centre cell does not merely stay inside the set; it
stays equal to its initial value. -/
lemma passive_cone_exact {α β : Type} (C : CellAutomaton α β)
    (S : Set C.Q) (hS : C.quiescent_set S)
    (c : Config C.Q) (p : ℤ) :
    ∀ t : ℕ,
      (∀ q : ℤ, p - (t : ℤ) ≤ q → q ≤ p + (t : ℤ) → c q ∈ S) →
      C.nextt c t p = c p := by
  intro t
  induction t generalizing p with
  | zero =>
    intro _
    rfl
  | succ t ih =>
    intro h_init
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    have h_left_mem : C.nextt c t (p - 1) ∈ S := by
      have h_cone : ∀ q : ℤ, p - 1 - (t : ℤ) ≤ q → q ≤ p - 1 + (t : ℤ) → c q ∈ S := by
        intro q hqL hqR
        exact h_init q (by omega) (by omega)
      rw [ih (p := p - 1) h_cone]
      exact h_init (p - 1) (by omega) (by omega)
    have h_center_eq : C.nextt c t p = c p := by
      apply ih
      intro q hqL hqR
      exact h_init q (by omega) (by omega)
    have h_center_mem : C.nextt c t p ∈ S := by
      rw [h_center_eq]
      exact h_init p (by omega) (by omega)
    have h_right_mem : C.nextt c t (p + 1) ∈ S := by
      have h_cone : ∀ q : ℤ, p + 1 - (t : ℤ) ≤ q → q ≤ p + 1 + (t : ℤ) → c q ∈ S := by
        intro q hqL hqR
        exact h_init q (by omega) (by omega)
      rw [ih (p := p + 1) h_cone]
      exact h_init (p + 1) (by omega) (by omega)
    have h_delta := hS ⟨_, h_left_mem⟩ ⟨_, h_center_mem⟩ ⟨_, h_right_mem⟩
    exact h_delta.trans h_center_eq

/-- In the original one-sided run, any cell strictly to the right of the cone
from cell `0` is still equal to its initial passive value. -/
lemma originalQ_passive (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false })
    (k t : ℕ) {p : ℤ} (hp : (t : ℤ) < p) :
    originalQ C k t p = (⟬fssp_left_side (k + 1)⟭ : Config C.Q) p := by
  unfold originalQ
  apply passive_cone_exact C { C.border, C.inner false } hQ
  intro q hqL _hqR
  have hq_pos : 0 < q := by omega
  rw [CellAutomaton.embed_config_apply, word_to_config_apply]
  by_cases h_range : q ≥ 0 ∧ q < (fssp_left_side (k + 1)).length
  · rw [dif_pos h_range]
    have h_i_lt : q.toNat < (fssp_left_side (k + 1)).length := by
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
    change C.embed (some ((fssp_left_side (k + 1))[q.toNat])) = C.embed (some false)
    congr
    rw [fssp_left_side_getElem_eq (k + 1) q.toNat h_i_lt]
    exact decide_eq_false hq_ne_zero
  · rw [dif_neg h_range]
    left
    rfl

/-- Closed-form row shape for the C-track.

The shape splits into three regions on the integer line:

* `p ≤ t`: the right-going cone from the first cell. The simulation matches
  the original one-sided execution `originalQ` here (this includes negative
  `p`, where both configurations evolve from `C.border`).
* `t < p < 2k - t`: untouched cells, still `C.inner false`.
* `2k - t ≤ p`: the beta region. Either the `L` scout has installed
  `C.border` here (for `p ≤ 2k`), or we're outside the input and the cell
  was always `C.border`. -/
def qShape (C : CellAutomaton Bool？ β) (k t : ℕ) (p : ℤ) : C.Q :=
  if p ≤ (t : ℤ) then originalQ C k t p
  else if 2 * (k : ℤ) - (t : ℤ) ≤ p then C.border
  else C.inner false

/-- The C-component projection of `(ca C).embed` for each input symbol. -/
@[simp] lemma ca_embed_q_none (C : CellAutomaton Bool？ β) :
    ((ca C).embed (none : (Bool × Bool)？)).2 = C.border := rfl

@[simp] lemma ca_embed_q_first (C : CellAutomaton Bool？ β) :
    ((ca C).embed (some (true, false))).2 = C.inner true := rfl

@[simp] lemma ca_embed_q_last (C : CellAutomaton Bool？ β) :
    ((ca C).embed (some (false, true))).2 = C.border := rfl

@[simp] lemma ca_embed_q_interior (C : CellAutomaton Bool？ β) :
    ((ca C).embed (some (false, false))).2 = C.inner false := rfl

@[simp] lemma ca_embed_q_singleton (C : CellAutomaton Bool？ β) :
    ((ca C).embed (some (true, true))).2 = C.inner true := rfl

/-- Initial row of the C-track diagram. -/
lemma q_inv_zero (C : CellAutomaton Bool？ β) (k : ℕ) (hk : k ≥ 1) (p : ℤ) :
    qAt C k 0 p = qShape C k 0 p := by
  show ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).2 = qShape C k 0 p
  unfold qShape
  by_cases hp_le : p ≤ ((0 : ℕ) : ℤ)
  · -- Region `p ≤ 0`: should equal `originalQ`.
    rw [if_pos hp_le]
    show ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).2 = originalQ C k 0 p
    unfold originalQ
    rw [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply, word_to_config_apply]
    have hp_le' : p ≤ 0 := by exact_mod_cast hp_le
    by_cases hp_eq : p = 0
    · subst hp_eq
      -- Both configurations have inner true at p = 0.
      have h_both_range : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < ((fssp_both_sides (2 * k + 1)).length : ℤ) := by
        refine ⟨le_refl _, ?_⟩
        rw [fssp_both_sides_length]; push_cast; omega
      rw [word_to_config_apply, dif_pos h_both_range]
      have hi_both : ((0 : ℤ).toNat : ℕ) < 2 * k + 1 := by simp
      have h_len_both : (fssp_both_sides (2 * k + 1)).length = 2 * k + 1 :=
        fssp_both_sides_length _
      have hi_both' : ((0 : ℤ).toNat : ℕ) < (fssp_both_sides (2 * k + 1)).length := by
        rw [h_len_both]; exact hi_both
      have h_get_both : (fssp_both_sides (2 * k + 1))[((0 : ℤ).toNat)]'hi_both' = (true, false) := by
        rw [fssp_both_sides_getElem_eq _ _ hi_both]
        have h0_toNat : ((0 : ℤ).toNat : ℕ) = 0 := rfl
        rw [h0_toNat]
        have h_2k_ne : (0 : ℕ) ≠ 2 * k + 1 - 1 := by omega
        have h_dec0 : decide ((0 : ℕ) = 0) = true := decide_eq_true rfl
        have h_dec_ne : decide ((0 : ℕ) = 2 * k + 1 - 1) = false := decide_eq_false h_2k_ne
        rw [h_dec0, h_dec_ne]
      have h_left_range : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < ((fssp_left_side (k + 1)).length : ℤ) := by
        refine ⟨le_refl _, ?_⟩
        rw [fssp_left_side_length]; push_cast; omega
      rw [dif_pos h_left_range]
      have hi_left : ((0 : ℤ).toNat : ℕ) < (fssp_left_side (k + 1)).length := by
        rw [fssp_left_side_length]; simp
      change ((ca C).embed (some ((fssp_both_sides (2 * k + 1))[(0:ℤ).toNat]'hi_both'))).2 =
        C.embed (some ((fssp_left_side (k + 1))[(0:ℤ).toNat]'hi_left))
      rw [h_get_both]
      have h_get_left : (fssp_left_side (k + 1))[((0 : ℤ).toNat)]'hi_left = true := by
        rw [fssp_left_side_getElem_eq _ _ hi_left]; decide
      rw [h_get_left]
      rfl
    · -- p < 0: both word_to_config give none → β.
      have hp_neg : p < 0 := lt_of_le_of_ne hp_le' hp_eq
      have h_not_both : ¬ (p ≥ 0 ∧ p < ((fssp_both_sides (2 * k + 1)).length : ℤ)) := by
        intro ⟨h, _⟩; omega
      have h_not_left : ¬ (p ≥ 0 ∧ p < ((fssp_left_side (k + 1)).length : ℤ)) := by
        intro ⟨h, _⟩; omega
      rw [word_to_config_apply, dif_neg h_not_both]
      rw [dif_neg h_not_left]
      rfl
  · -- Region `0 < p`: split on right cone vs interior.
    rw [if_neg hp_le]
    push_neg at hp_le
    have hp_pos : 0 < p := by exact_mod_cast hp_le
    by_cases h_right : 2 * (k : ℤ) - ((0 : ℕ) : ℤ) ≤ p
    · -- Right region: should equal C.border.
      rw [if_pos h_right]
      have h_p_ge_2k : 2 * (k : ℤ) ≤ p := by push_cast at h_right; exact h_right
      by_cases hp_eq : p = 2 * (k : ℤ)
      · subst hp_eq
        have h_both_range : (2 * (k : ℤ)) ≥ 0 ∧ (2 * (k : ℤ)) < ((fssp_both_sides (2 * k + 1)).length : ℤ) := by
          refine ⟨by omega, ?_⟩
          rw [fssp_both_sides_length]; push_cast; omega
        rw [word_to_config_apply, dif_pos h_both_range]
        have h_2k_toNat : (2 * (k : ℤ)).toNat = 2 * k := by
          rw [show 2 * (k : ℤ) = ((2 * k : ℕ) : ℤ) by push_cast; ring]
          exact Int.toNat_natCast _
        have hi_both : (2 * (k : ℤ)).toNat < 2 * k + 1 := by rw [h_2k_toNat]; omega
        have h_len_both : (fssp_both_sides (2 * k + 1)).length = 2 * k + 1 :=
          fssp_both_sides_length _
        have hi_both' : (2 * (k : ℤ)).toNat < (fssp_both_sides (2 * k + 1)).length := by
          rw [h_len_both]; exact hi_both
        have h_get : (fssp_both_sides (2 * k + 1))[(2 * (k : ℤ)).toNat]'hi_both' = (false, true) := by
          rw [fssp_both_sides_getElem_eq _ _ hi_both]
          rw [h_2k_toNat]
          have h_2k_eq : (2 * k + 1 - 1 : ℕ) = 2 * k := by omega
          rw [h_2k_eq]
          have h_ne0 : 2 * k ≠ 0 := by omega
          have h_dec0 : decide (2 * k = 0) = false := decide_eq_false h_ne0
          have h_dec_eq : decide (2 * k = 2 * k) = true := decide_eq_true rfl
          rw [h_dec0, h_dec_eq]
        change ((ca C).embed (some ((fssp_both_sides (2 * k + 1))[(2 * (k : ℤ)).toNat]'hi_both'))).2 = C.border
        rw [h_get]
        rfl
      · -- p > 2k: out-of-range → β.
        have hp_gt : p > 2 * (k : ℤ) := lt_of_le_of_ne h_p_ge_2k (Ne.symm hp_eq)
        have h_not_both : ¬ (p ≥ 0 ∧ p < ((fssp_both_sides (2 * k + 1)).length : ℤ)) := by
          intro ⟨_, h⟩
          rw [fssp_both_sides_length] at h
          push_cast at h; omega
        rw [word_to_config_apply, dif_neg h_not_both]
        rfl
    · -- Interior: 0 < p < 2k → C.inner false.
      rw [if_neg h_right]
      push_neg at h_right
      have hp_lt : p < 2 * (k : ℤ) := by push_cast at h_right; exact h_right
      have h_both_range : p ≥ 0 ∧ p < ((fssp_both_sides (2 * k + 1)).length : ℤ) := by
        refine ⟨le_of_lt hp_pos, ?_⟩
        rw [fssp_both_sides_length]; push_cast; omega
      rw [word_to_config_apply, dif_pos h_both_range]
      have hp_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (le_of_lt hp_pos)
      have hi_both : p.toNat < 2 * k + 1 := by
        have : (p.toNat : ℤ) < (2 * k + 1 : ℤ) := by rw [hp_toNat]; omega
        exact_mod_cast this
      have hp_toNat_ne0 : p.toNat ≠ 0 := by
        intro h; have : (p.toNat : ℤ) = 0 := by exact_mod_cast h
        omega
      have hp_toNat_ne_2k : p.toNat ≠ 2 * k := by
        intro h
        have h_eq : (p.toNat : ℤ) = ((2 * k : ℕ) : ℤ) := by exact_mod_cast h
        rw [hp_toNat] at h_eq; push_cast at h_eq; omega
      have h_get : (fssp_both_sides (2 * k + 1))[p.toNat]'(by
          rw [fssp_both_sides_length]; exact hi_both) = (false, false) := by
        rw [fssp_both_sides_getElem_eq _ _ hi_both]
        have h_2k_eq : (2 * k + 1 - 1 : ℕ) = 2 * k := by omega
        rw [h_2k_eq]
        congr 1
        · exact decide_eq_false hp_toNat_ne0
        · exact decide_eq_false hp_toNat_ne_2k
      have hi_both' : p.toNat < (fssp_both_sides (2 * k + 1)).length := by
        have h_len_both : (fssp_both_sides (2 * k + 1)).length = 2 * k + 1 :=
          fssp_both_sides_length _
        rw [h_len_both]; exact hi_both
      change ((ca C).embed (some ((fssp_both_sides (2 * k + 1))[p.toNat]'hi_both'))).2 = C.inner false
      rw [h_get]
      rfl

/-- For neighbour cells (`q ≤ t + 2`), the closed-form `qShape` agrees with the
original one-sided execution `originalQ`. This is the key lemma used in the
inductive step of `q_inv`: when computing `qAt(t+1, p)` for `p ≤ t+1`, the
three neighbour positions satisfy `q ≤ t+2`, so we can replace `qShape` with
`originalQ` and reduce to the original CA's update rule. -/
lemma qShape_eq_originalQ_near (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false })
    (k : ℕ) (hk : k ≥ 1) (t : ℕ) (q : ℤ) (hq : q ≤ (t : ℤ) + 2) :
    qShape C k t q = originalQ C k t q := by
  unfold qShape
  by_cases hqt : q ≤ (t : ℤ)
  · rw [if_pos hqt]
  · rw [if_neg hqt]
    push_neg at hqt
    -- q > t, so by passive_cone the original is its initial value.
    have hq_passive := originalQ_passive C hQ k t hqt
    rw [hq_passive]
    rw [CellAutomaton.embed_config_apply, word_to_config_apply]
    have h_len : ((fssp_left_side (k + 1)).length : ℤ) = k + 1 := by
      rw [fssp_left_side_length]; push_cast; rfl
    by_cases h_in_left : q ≥ 0 ∧ q < ((fssp_left_side (k + 1)).length : ℤ)
    · -- q ∈ valid range: original = inner false (since q > 0 and q ≤ k).
      rw [dif_pos h_in_left]
      rw [h_len] at h_in_left
      have hq_le_k : q ≤ (k : ℤ) := by omega
      -- q ∈ {t+1, t+2} and q ≤ k. So 2k - t > q (strictly).
      have h_not_right : ¬ 2 * (k : ℤ) - (t : ℤ) ≤ q := by omega
      rw [if_neg h_not_right]
      have hq_pos : 0 < q := by omega
      have hq_toNat_ne0 : q.toNat ≠ 0 := by
        intro h
        have h_cast : (q.toNat : ℤ) = 0 := by exact_mod_cast h
        rw [Int.toNat_of_nonneg (le_of_lt hq_pos)] at h_cast
        omega
      have hi_left : q.toNat < (fssp_left_side (k + 1)).length := by
        have hq_cast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (le_of_lt hq_pos)
        have hlt : (q.toNat : ℤ) < (k + 1 : ℤ) := by rw [hq_cast]; omega
        rw [fssp_left_side_length]
        exact_mod_cast hlt
      change C.inner false = C.embed (some ((fssp_left_side (k + 1))[q.toNat]'hi_left))
      rw [fssp_left_side_getElem_eq (k + 1) q.toNat hi_left]
      rw [decide_eq_false hq_toNat_ne0]
      rfl
    · -- q out of fssp_left_side range: original = β.
      rw [dif_neg h_in_left]
      -- q > t ≥ 0, q out of range means q < 0 or q ≥ k+1.
      -- Since q > t ≥ 0 (t ≥ 0), and q out of range means q ≥ k+1.
      push_neg at h_in_left
      have hq_nn : q ≥ 0 := by omega
      have hq_ge : q ≥ k + 1 := by
        have := h_in_left hq_nn; rw [h_len] at this; omega
      -- qShape: 2k - t ≤ q? q ∈ {t+1, t+2}, q ≥ k+1.
      have h_right : 2 * (k : ℤ) - (t : ℤ) ≤ q := by omega
      rw [if_pos h_right]
      rfl

/-- Stepping `scoutShape` via `scoutStep` gives the next-time `scoutShape`. -/
lemma scoutStep_scoutShape (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ) :
    scoutStep (scoutShape k t (p - 1)) (scoutShape k t p) (scoutShape k t (p + 1)) =
      scoutShape k (t + 1) p := by
  rw [← scout_inv k hk t (p - 1), ← scout_inv k hk t p, ← scout_inv k hk t (p + 1)]
  rw [← scoutAt_succ]
  exact scout_inv k hk (t + 1) p

/-- Second-track invariant: the C-component has exactly the `Q`/`bottom`/`beta`
row shape shown in the diagram. -/
theorem q_inv (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false })
    (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ) :
    qAt C k t p = qShape C k t p := by
  induction t generalizing p with
  | zero => exact q_inv_zero C k hk p
  | succ t ih =>
    -- Unfold the recursion and rewrite scout/q values via scout_inv and IH.
    show (let nextScout := scoutStep (scoutAt k t (p - 1)) (scoutAt k t p) (scoutAt k t (p + 1))
          if nextScout = Scout.L then C.border
          else C.δ (qAt C k t (p - 1)) (qAt C k t p) (qAt C k t (p + 1))) =
        qShape C k (t + 1) p
    rw [scout_inv k hk t (p - 1), scout_inv k hk t p, scout_inv k hk t (p + 1)]
    rw [ih (p - 1), ih p, ih (p + 1)]
    -- Reduce `scoutStep ...` to `scoutShape (t+1) p`.
    rw [scoutStep_scoutShape k hk t p]
    -- Case-split on the regime of the target `qShape (t+1, p)`.
    by_cases hpA : p ≤ ((t + 1 : ℕ) : ℤ)
    · -- Case A: left cone — qShape = originalQ.
      have h_rhs : qShape C k (t + 1) p = originalQ C k (t + 1) p := by
        unfold qShape; rw [if_pos hpA]
      rw [h_rhs]
      -- nextScout cannot be L: that would require p = 2k-(t+1) AND t+1 < k,
      -- but p ≤ t+1 forces 2k-(t+1) ≥ p, with t+1 < k forcing p ≥ k > t+1, contradiction.
      have h_not_L : scoutShape k (t + 1) p ≠ Scout.L := by
        unfold scoutShape
        intro h
        split_ifs at h <;>
          first | omega | exact (Scout.noConfusion h)
      rw [if_neg h_not_L]
      -- Now use qShape_eq_originalQ_near for each of the three neighbours.
      rw [qShape_eq_originalQ_near C hQ k hk t (p - 1) (by push_cast at hpA; omega),
          qShape_eq_originalQ_near C hQ k hk t p (by push_cast at hpA; omega),
          qShape_eq_originalQ_near C hQ k hk t (p + 1) (by push_cast at hpA; omega)]
      -- LHS = δ originalQ originalQ originalQ; RHS = originalQ(t+1, p) = δ ... by nextt_succ.
      unfold originalQ
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    · -- Case B or C: p > t+1.
      push_neg at hpA
      have hp_gt_t : p > (t : ℤ) := by push_cast at hpA; omega
      by_cases hpB : 2 * (k : ℤ) - ((t + 1 : ℕ) : ℤ) ≤ p
      · -- Case B: right cone — qShape = β.
        have h_rhs : qShape C k (t + 1) p = C.border := by
          unfold qShape
          have h1 : ¬ p ≤ ((t + 1 : ℕ) : ℤ) := not_le.mpr hpA
          rw [if_neg h1, if_pos hpB]
        rw [h_rhs]
        -- Two sub-cases: nextScout = L (build β) or nextScout ≠ L (use quiescence).
        by_cases h_L : scoutShape k (t + 1) p = Scout.L
        · rw [if_pos h_L]
        · rw [if_neg h_L]
          -- nextScout ≠ L. Need δ qq qq qq = β.
          -- All three neighbours have q > t (from p > t + 1).
          -- p ≥ 2k - t (otherwise scoutShape would say L for valid t+1 < k).
          have hp_ge : 2 * (k : ℤ) - (t : ℤ) ≤ p := by
            push_cast at hpB
            by_contra h_lt
            push_neg at h_lt
            have hp_eq : p = 2 * (k : ℤ) - ((t + 1 : ℕ) : ℤ) := by push_cast; omega
            by_cases htk : t + 1 < k
            · apply h_L
              unfold scoutShape
              have h_in : ¬ (p < 0 ∨ p > 2 * (k : ℤ)) := by push_cast at hp_eq; omega
              have h_R_neg : ¬ (((t + 1 : ℕ) : ℤ) < k ∧ p = ((t + 1 : ℕ) : ℤ)) := by
                push_neg; intro _; push_cast at hp_eq; omega
              have h_L_cond : ((t + 1 : ℕ) : ℤ) < k ∧ p = 2 * (k : ℤ) - ((t + 1 : ℕ) : ℤ) := by
                refine ⟨?_, hp_eq⟩
                exact_mod_cast htk
              rw [if_neg h_in, if_neg h_R_neg, if_pos h_L_cond]
            · push_neg at htk
              have htk' : (k : ℤ) ≤ ((t + 1 : ℕ) : ℤ) := by exact_mod_cast htk
              have hp_le_k : p ≤ (k : ℤ) - 1 := by push_cast at hp_eq; omega
              omega
          -- qShape(t, p) = β.
          have h_qq_p : qShape C k t p = C.border := by
            unfold qShape
            have h1 : ¬ p ≤ (t : ℤ) := by omega
            rw [if_neg h1, if_pos hp_ge]
          have h_qq_R : qShape C k t (p + 1) = C.border := by
            unfold qShape
            have h1 : ¬ p + 1 ≤ (t : ℤ) := by omega
            have h2 : 2 * (k : ℤ) - (t : ℤ) ≤ p + 1 := by omega
            rw [if_neg h1, if_pos h2]
          have h_qq_L_in_S : qShape C k t (p - 1) = C.border ∨
              qShape C k t (p - 1) = C.inner false := by
            unfold qShape
            have h1 : ¬ p - 1 ≤ (t : ℤ) := by omega
            rw [if_neg h1]
            by_cases h2 : 2 * (k : ℤ) - (t : ℤ) ≤ p - 1
            · rw [if_pos h2]; left; rfl
            · rw [if_neg h2]; right; rfl
          rw [h_qq_p, h_qq_R]
          have h_left_mem : qShape C k t (p - 1) ∈ ({C.border, C.inner false} : Set C.Q) := by
            rcases h_qq_L_in_S with h | h
            · exact Or.inl h
            · exact Or.inr h
          have h_β_mem : C.border ∈ ({C.border, C.inner false} : Set C.Q) := Or.inl rfl
          exact hQ ⟨_, h_left_mem⟩ ⟨_, h_β_mem⟩ ⟨_, h_β_mem⟩
      · -- Case C: interior — qShape = inner false.
        push_neg at hpB
        have hp_lt : p < 2 * (k : ℤ) - (t : ℤ) := by push_cast at hpB; omega
        have h_rhs : qShape C k (t + 1) p = C.inner false := by
          unfold qShape
          have h1 : ¬ p ≤ ((t + 1 : ℕ) : ℤ) := not_le.mpr hpA
          have h2 : ¬ 2 * (k : ℤ) - ((t + 1 : ℕ) : ℤ) ≤ p := not_le.mpr hpB
          rw [if_neg h1, if_neg h2]
        rw [h_rhs]
        have h_not_L : scoutShape k (t + 1) p ≠ Scout.L := by
          unfold scoutShape
          intro h
          split_ifs at h <;>
            first | (push_cast at *; omega) | exact (Scout.noConfusion h)
        rw [if_neg h_not_L]
        -- All three neighbours are interior: q > t and q < 2k - t.
        have h_qq_L : qShape C k t (p - 1) = C.inner false := by
          unfold qShape
          have h1 : ¬ p - 1 ≤ (t : ℤ) := by omega
          have h2 : ¬ 2 * (k : ℤ) - (t : ℤ) ≤ p - 1 := by omega
          rw [if_neg h1, if_neg h2]
        have h_qq_C : qShape C k t p = C.inner false := by
          unfold qShape
          have h1 : ¬ p ≤ (t : ℤ) := by omega
          have h2 : ¬ 2 * (k : ℤ) - (t : ℤ) ≤ p := by omega
          rw [if_neg h1, if_neg h2]
        have h_qq_R : qShape C k t (p + 1) = C.inner false := by
          unfold qShape
          have h1 : ¬ p + 1 ≤ (t : ℤ) := by omega
          have h2 : ¬ 2 * (k : ℤ) - (t : ℤ) ≤ p + 1 := by omega
          rw [if_neg h1, if_neg h2]
        rw [h_qq_L, h_qq_C, h_qq_R]
        have h_mem : (C.inner false : C.Q) ∈ ({C.border, C.inner false} : Set C.Q) := Or.inr rfl
        exact hQ ⟨_, h_mem⟩ ⟨_, h_mem⟩ ⟨_, h_mem⟩

/-- The initial C-component expected from the corrected odd construction.

It is the left input with an initially distant moving beta boundary at the
rightmost both-sided marker. Inside the both-sided word, the rightmost marker is
embedded as `C.border`; ordinary interior cells are `C.inner false`. -/
def initialQ (C : CellAutomaton Bool？ β) (k : ℕ) (p : ℤ) : C.Q :=
  ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).2

/-- The simulation CA's full state at time `t`, position `p`, on the both-sided
input, equals `(scoutAt, qAt)`. This bridges our standalone recursions back to
the actual `(ca C).nextt` evolution. -/
lemma ca_nextt_eq (C : CellAutomaton Bool？ β) (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ) :
    (ca C).nextt (⟬fssp_both_sides (2 * k + 1)⟭ : Config (ca C).Q) t p =
      (scoutAt k t p, qAt C k t p) := by
  induction t generalizing p with
  | zero =>
    show ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)) =
         (scoutAt0 k p, qAt C k 0 p)
    have h2 : qAt C k 0 p =
        ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).2 := rfl
    apply Prod.ext
    · -- .1 case
      show ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).1 = scoutAt0 k p
      rw [word_to_config_apply]
      by_cases hp_range : p ≥ 0 ∧ p < ((fssp_both_sides (2 * k + 1)).length : ℤ)
      · rw [dif_pos hp_range]
        have h_len : ((fssp_both_sides (2 * k + 1)).length : ℤ) = 2 * k + 1 := by
          simp [fssp_both_sides_length]
        have hp_pos : 0 ≤ p := hp_range.1
        have hp_lt : p < 2 * (k : ℤ) + 1 := by rw [h_len] at hp_range; exact hp_range.2
        have hi : p.toNat < 2 * k + 1 := by
          have hp_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_pos
          have : (p.toNat : ℤ) < ((2 * k + 1 : ℕ) : ℤ) := by rw [hp_toNat]; push_cast; omega
          exact_mod_cast this
        have hi' : p.toNat < (fssp_both_sides (2 * k + 1)).length := by
          rw [fssp_both_sides_length]; exact hi
        rw [fssp_both_sides_getElem_eq _ _ hi]
        unfold scoutAt0
        have h_in : ¬ (p < 0 ∨ p > 2 * (k : ℤ)) := by push_neg; refine ⟨hp_pos, by omega⟩
        rw [if_neg h_in]
        by_cases hp0 : p = 0
        · subst hp0
          have h_tn0 : ((0 : ℤ).toNat : ℕ) = 0 := rfl
          rw [h_tn0]
          have h_dec0 : decide ((0 : ℕ) = 0) = true := decide_eq_true rfl
          have h_2k_ne : (0 : ℕ) ≠ 2 * k + 1 - 1 := by omega
          have h_dec_ne : decide ((0 : ℕ) = 2 * k + 1 - 1) = false := decide_eq_false h_2k_ne
          rw [h_dec0, h_dec_ne]
          rfl
        · by_cases hp2k : p = 2 * (k : ℤ)
          · subst hp2k
            have h_2k_toNat : (2 * (k : ℤ)).toNat = 2 * k := by
              rw [show 2 * (k : ℤ) = ((2 * k : ℕ) : ℤ) by push_cast; ring]
              exact Int.toNat_natCast _
            rw [h_2k_toNat]
            have h_2k_eq : (2 * k + 1 - 1 : ℕ) = 2 * k := by omega
            rw [h_2k_eq]
            have h_ne0 : 2 * k ≠ 0 := by omega
            have h_dec0 : decide (2 * k = 0) = false := decide_eq_false h_ne0
            have h_dec_eq : decide (2 * k = 2 * k) = true := decide_eq_true rfl
            rw [h_dec0, h_dec_eq]
            have h_2k_ne_0 : (2 * (k : ℤ)) ≠ 0 := by omega
            rw [if_neg h_2k_ne_0]
            -- Goal: ((ca C).embed (some (false, true))).1 = (if 2k = 2k then L else quiet)
            rw [if_pos (rfl : (2 * (k : ℤ)) = 2 * (k : ℤ))]
            rfl
          · -- Interior: 0 < p < 2k.
            have h_p_pos : 0 < p := lt_of_le_of_ne hp_pos (Ne.symm hp0)
            have h_p_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_pos
            have h_toNat_ne0 : p.toNat ≠ 0 := by
              intro h; have : (p.toNat : ℤ) = 0 := by exact_mod_cast h
              omega
            have h_toNat_ne_last : p.toNat ≠ 2 * k + 1 - 1 := by
              intro h
              have : (p.toNat : ℤ) = ((2 * k + 1 - 1 : ℕ) : ℤ) := by exact_mod_cast h
              rw [h_p_toNat] at this
              have h_2k_eq : ((2 * k + 1 - 1 : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; omega
              rw [h_2k_eq] at this
              exact hp2k this
            have h_dec0 : decide (p.toNat = 0) = false := decide_eq_false h_toNat_ne0
            have h_dec_ne : decide (p.toNat = 2 * k + 1 - 1) = false :=
              decide_eq_false h_toNat_ne_last
            rw [h_dec0, h_dec_ne]
            rw [if_neg hp0, if_neg hp2k]
            rfl
      · -- Out of range
        rw [dif_neg hp_range]
        show (Scout.bord) = scoutAt0 k p
        unfold scoutAt0
        have h_len : ((fssp_both_sides (2 * k + 1)).length : ℤ) = 2 * k + 1 := by
          simp [fssp_both_sides_length]
        have h_out : p < 0 ∨ p > 2 * (k : ℤ) := by
          push_neg at hp_range
          by_cases hp_nn : p ≥ 0
          · right
            have := hp_range hp_nn
            rw [h_len] at this; omega
          · left; omega
        rw [if_pos h_out]
    · -- .2 case
      show ((ca C).embed (word_to_config (fssp_both_sides (2 * k + 1)) p)).2 = qAt C k 0 p
      rw [h2]
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    rw [ih (p - 1), ih p, ih (p + 1)]
    show ((ca C).δ ⟨scoutAt k t (p - 1), qAt C k t (p - 1)⟩
                    ⟨scoutAt k t p, qAt C k t p⟩
                    ⟨scoutAt k t (p + 1), qAt C k t (p + 1)⟩) =
        (scoutAt k (t + 1) p, qAt C k (t + 1) p)
    rfl

/-- The simulation CA's quiescent set is `{ (ca C).border, (ca C).inner (false, false) }`. -/
theorem spec_quiescent_set (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false }) :
    (ca C).quiescent_set { (ca C).border, (ca C).inner (false, false) } := by
  -- Quiescent set: { (ca C).border, (ca C).inner (false, false) }
  --   = { (Scout.bord, C.border), (Scout.quiet, C.inner false) }
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  obtain ⟨sa, qa⟩ := a
  obtain ⟨sb, qb⟩ := b
  obtain ⟨sc, qc⟩ := c
  show (ca C).δ ⟨sa, qa⟩ ⟨sb, qb⟩ ⟨sc, qc⟩ = ⟨sb, qb⟩
  -- Each (sx, qx) ∈ {(Scout.bord, C.border), (Scout.quiet, C.inner false)}.
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
  -- Compute (ca C).δ via Prod.ext.
  apply Prod.ext
  · -- .1: scoutStep sa sb sc = sb
    show scoutStep sa sb sc = sb
    rcases hb' with ⟨hb1, _⟩ | ⟨hb1, _⟩ <;>
      rcases ha' with ⟨ha1, _⟩ | ⟨ha1, _⟩ <;>
      rcases hc' with ⟨hc1, _⟩ | ⟨hc1, _⟩ <;>
      subst_vars <;> rfl
  · -- .2: if scoutStep sa sb sc = L then β else δ qa qb qc = qb
    show (if scoutStep sa sb sc = Scout.L then C.border else C.δ qa qb qc) = qb
    have h_not_L : scoutStep sa sb sc ≠ Scout.L := by
      rcases hb' with ⟨hb1, _⟩ | ⟨hb1, _⟩ <;>
        rcases ha' with ⟨ha1, _⟩ | ⟨ha1, _⟩ <;>
        rcases hc' with ⟨hc1, _⟩ | ⟨hc1, _⟩ <;>
        subst_vars <;> decide
    rw [if_neg h_not_L]
    exact hQ ⟨qa, h_qa⟩ ⟨qb, h_qb⟩ ⟨qc, h_qc⟩

/-- The corrected odd construction simulates `C` on `fssp_left_side (k + 1)`.

For `k >= 1`, the constructed CA on `fssp_both_sides (2k + 1)` simulates `C` on
`fssp_left_side (k + 1)` inside the right-going light cone from the first cell.

The cone condition `p ≤ t` is important: the moving beta boundary cell
`p = k + 1` does not match the original one-sided border cell at time `0`.
It only needs to match once the signal from cell `0` can have reached it. -/
theorem spec_comp (C : CellAutomaton Bool？ β)
    (hQ : C.quiescent_set { C.border, C.inner false })
    (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ) (hp_t : p ≤ (t : ℤ)) :
    (ca C).comp ⟬fssp_both_sides (2 * k + 1)⟭ t p =
      C.comp ⟬fssp_left_side (k + 1)⟭ t p := by
  -- Simulation: for `p ≤ t`, the projected results match.
  rw [CellAutomaton.comp_apply, CellAutomaton.comp_apply]
  -- The key chain of equalities:
  --   (ca C).comp _ t p = C.project ((ca C).nextt _ t p).2
  --                    = C.project (qAt C k t p)             [by ca_nextt_eq]
  --                    = C.project (qShape C k t p)          [by q_inv]
  --                    = C.project (originalQ C k t p)       [since p ≤ t]
  --                    = C.project (C.nextt _ t p)           [originalQ definition]
  show (ca C).project ((ca C).nextt _ t p) = C.project (C.nextt _ t p)
  have h_proj :
      (ca C).project ((ca C).nextt ⟬fssp_both_sides (2 * k + 1)⟭ t p) =
        C.project ((ca C).nextt ⟬fssp_both_sides (2 * k + 1)⟭ t p).2 := rfl
  rw [h_proj]
  rw [ca_nextt_eq C k hk t p]
  show C.project (qAt C k t p) = C.project (C.nextt _ t p)
  rw [q_inv C hQ k hk t p]
  have h_qshape : qShape C k t p = originalQ C k t p := by
    unfold qShape; rw [if_pos hp_t]
  rw [h_qshape]
  rfl

end OddTwoSidedBetaBoundary

end CellularAutomatas
