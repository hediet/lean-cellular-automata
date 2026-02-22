/-
# Core CA for Exponential Time Marking

This CA, when run on input `[Unit]` (a single cell), marks position 0
at exactly the times τ = 2^(k+1) − 2 for k ≥ 0.

## Specification
  exp_core_spec: exp_core.comp ⟬[()]⟭ τ 0 = true ↔ ∃ k, τ = 2^(k+1) − 2
-/

import CellularAutomatas.defs

namespace CellularAutomatas

/-! ## States -/

inductive SigState | SR | SL | None
  deriving DecidableEq, Repr, Fintype, Inhabited

inductive MirrorState | M1 | M2 | M3 | None
  deriving DecidableEq, Repr, Fintype, Inhabited

abbrev ExpQ := SigState × MirrorState × Bool

/-! ## Transition Function -/

def exp_δ (left center right : ExpQ) : ExpQ :=
  let m' := match center.2.1 with
    | .M1 => MirrorState.None
    | .M2 => MirrorState.M3
    | .M3 => MirrorState.M1
    | .None =>
      match left.2.1 with
      | .M1 => MirrorState.M2
      | _ => MirrorState.None
  let u := center.2.2
  let s' :=
    let incoming :=
      match left.1 with
      | .SR => SigState.SR
      | _ =>
        match right.1 with
        | .SL => SigState.SL
        | _ => SigState.None
    match incoming with
    | .SR => if m' == .M2 then .SL else .SR
    | .SL => if u then .SR else .SL
    | .None => .None
  (s', m', u)

/-! ## The CA -/

def exp_core : CellAutomaton Unit？ Bool := {
  Q := ExpQ,
  δ := exp_δ,
  embed := fun
    | none => (.None, .None, false)
    | some () => (.SR, .M1, true),
  project := fun q => q.1 == .SR || q.1 == .SL,
}

/-! ## Timing Definitions -/

def bounce_time (k : ℕ) : ℕ := 2 ^ (k + 1) - 2
def collision_time (k : ℕ) : ℕ := bounce_time k + 2 ^ k

/-! ## Mirror Definitions -/

def mirror_pos (t : ℕ) : ℤ := ((t : ℤ) + 2) / 3

def mirror_phase (t : ℕ) : MirrorState :=
  match t % 3 with
  | 0 => .M1
  | 1 => .M2
  | _ => .M3

def mirror_config (t : ℕ) (p : ℤ) : MirrorState :=
  if p = mirror_pos t then mirror_phase t else .None

/-! ## Mirror Lemmas -/

lemma mirror_pos_of_mod3_eq_0 (t : ℕ) (h : t % 3 = 0) :
    mirror_pos (t + 1) = mirror_pos t + 1 := by simp only [mirror_pos]; omega

lemma mirror_pos_of_mod3_eq_1 (t : ℕ) (h : t % 3 = 1) :
    mirror_pos (t + 1) = mirror_pos t := by simp only [mirror_pos]; omega

lemma mirror_pos_of_mod3_eq_2 (t : ℕ) (h : t % 3 = 2) :
    mirror_pos (t + 1) = mirror_pos t := by simp only [mirror_pos]; omega

lemma mirror_invariant (t : ℕ) (p : ℤ) :
    mirror_config (t + 1) p =
      match mirror_config t p with
      | .M1 => .None
      | .M2 => .M3
      | .M3 => .M1
      | .None => if mirror_config t (p - 1) == .M1 then .M2 else .None := by
  unfold mirror_config
  have h3 : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases h3 with hmod | hmod | hmod
  · -- t%3=0: M1 phase, mirror shifts right. pos(t+1) = pos(t) + 1
    have h1 : (t + 1) % 3 = 1 := by omega
    simp only [mirror_phase, hmod, h1]
    rw [mirror_pos_of_mod3_eq_0 t hmod]
    by_cases hp : p = mirror_pos t + 1
    <;> by_cases hp2 : p = mirror_pos t
    <;> by_cases hp3 : p - 1 = mirror_pos t
    <;> (simp_all; try omega)
  · -- t%3=1: M2 phase, stays. pos(t+1) = pos(t)
    have h1 : (t + 1) % 3 = 2 := by omega
    simp only [mirror_phase, hmod, h1]
    rw [mirror_pos_of_mod3_eq_1 t hmod]
    by_cases hp : p = mirror_pos t
    <;> by_cases hp3 : p - 1 = mirror_pos t
    <;> (simp_all; try omega)
  · -- t%3=2: M3 phase, stays. pos(t+1) = pos(t)
    have h1 : (t + 1) % 3 = 0 := by omega
    simp only [mirror_phase, hmod, h1]
    rw [mirror_pos_of_mod3_eq_2 t hmod]
    by_cases hp : p = mirror_pos t
    <;> by_cases hp3 : p - 1 = mirror_pos t
    <;> (simp_all; try omega)

/-! ## Phase Arithmetic -/

lemma bounce_time_zero : bounce_time 0 = 0 := by simp [bounce_time]

lemma bounce_time_succ (k : ℕ) : bounce_time (k + 1) = collision_time k + 2 ^ k := by
  simp only [bounce_time, collision_time]
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  have : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  omega

lemma collision_time_eq (k : ℕ) : collision_time k = 3 * 2 ^ k - 2 := by
  simp only [collision_time, bounce_time]
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

/-! ## Signal Position (abstract) -/

def sig_pos (k : ℕ) (t : ℕ) : ℤ :=
  if t ≤ collision_time k then (t : ℤ) - bounce_time k
  else bounce_time (k + 1) - t

/-! ## No-Spurious-Bounce Lemmas -/

lemma no_spurious_bounce_right (k : ℕ) (t : ℕ)
    (ht_lo : bounce_time k ≤ t) (ht_hi : t ≤ collision_time k)
    (h_meet : sig_pos k t = mirror_pos t)
    (h_m2 : mirror_phase t = .M2) :
    t = collision_time k := by
  have hpow : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  have h2k1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hbt : bounce_time k = 2 * 2 ^ k - 2 := by simp only [bounce_time, h2k1]
  have ht_mod : t % 3 = 1 := by
    simp only [mirror_phase] at h_m2
    have h3 : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases h3 with h | h | h <;> simp [h] at h_m2 ⊢
  simp only [sig_pos, ht_hi, ite_true, mirror_pos] at h_meet
  -- h_meet has ℤ division; eliminate using t%3=1
  have ⟨q, hq⟩ : ∃ q, t = 3 * q + 1 := ⟨t / 3, by omega⟩
  subst hq
  simp only [collision_time_eq] at ht_hi ht_lo ⊢
  omega

lemma mirror_phase_at_collision (k : ℕ) :
    mirror_phase (collision_time k) = .M2 := by
  simp only [mirror_phase, collision_time_eq]
  have hk : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  have : (3 * 2 ^ k - 2) % 3 = 1 := by omega
  simp [this]

lemma no_encounter_left (k : ℕ) (t : ℕ)
    (ht_lo : collision_time k < t) (_ht_hi : t ≤ bounce_time (k + 1)) :
    sig_pos k t ≠ mirror_pos t := by
  have hpow : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  have h2k1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have h2k2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  have hbt1 : bounce_time (k + 1) = 4 * 2 ^ k - 2 := by
    simp only [bounce_time, h2k2]
  have hct : collision_time k = 3 * 2 ^ k - 2 := collision_time_eq k
  have h_not_le : ¬(t ≤ collision_time k) := by omega
  simp only [sig_pos, h_not_le, ite_false, mirror_pos]
  omega

lemma signal_at_bounce_time (k : ℕ) :
    sig_pos k (bounce_time (k + 1)) = 0 := by
  have hpow : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  have hbt1 : bounce_time (k + 1) = 4 * 2 ^ k - 2 := by
    simp only [bounce_time]; ring_nf
  have hct : collision_time k = 3 * 2 ^ k - 2 := collision_time_eq k
  have h_not_le : ¬(bounce_time (k + 1) ≤ collision_time k) := by omega
  unfold sig_pos; rw [if_neg h_not_le]; simp only [bounce_time]
  omega

/-! ## Computational Verification -/

def trace_p0 (t : ℕ) : Bool := exp_core.comp ⟬([()] : Word Unit)⟭ t 0

-- #eval! (List.range 8).map trace_p0
-- #eval! trace_p0 14

/-! ## Full CA Invariant

We prove exp_core_spec by defining the expected configuration and showing
the actual CA matches it at every step.
-/

def init_config : Config ExpQ := CellAutomaton.embed_config (C := exp_core) ⟬([()] : Word Unit)⟭

def ca_state (t : ℕ) (p : ℤ) : ExpQ := exp_core.nextt init_config t p

-- Helper: the is_unit component is preserved by exp_δ
lemma exp_δ_preserves_unit (l c r : ExpQ) : (exp_δ l c r).2.2 = c.2.2 := by
  simp [exp_δ]

-- Helper: the mirror component of exp_δ depends only on mirror components
lemma exp_δ_mirror (l c r : ExpQ) :
    (exp_δ l c r).2.1 = match c.2.1 with
      | .M1 => MirrorState.None
      | .M2 => .M3
      | .M3 => .M1
      | .None => if l.2.1 == .M1 then .M2 else .None := by
  unfold exp_δ
  cases c.2.1 <;> simp
  cases l.2.1 <;> simp

-- The is_unit component: true only at p=0, for all t
-- Helper: ca_state unfolds one step
lemma ca_state_succ (t : ℕ) (p : ℤ) :
    ca_state (t + 1) p = exp_δ (ca_state t (p - 1)) (ca_state t p) (ca_state t (p + 1)) := by
  unfold ca_state
  rw [CellAutomaton.nextt_succ]
  rfl

lemma ca_unit_matches (t : ℕ) (p : ℤ) :
    (ca_state t p).2.2 = decide (p = 0) := by
  induction t with
  | zero =>
    unfold ca_state init_config CellAutomaton.embed_config exp_core word_to_config
    simp only [CellAutomaton.nextt_zero, List.length_singleton]
    split <;> simp_all [ge_iff_le] <;> omega
  | succ t ih =>
    rw [ca_state_succ, exp_δ_preserves_unit, ih]

lemma ca_mirror_matches (t : ℕ) (p : ℤ) :
    (ca_state t p).2.1 = mirror_config t p := by
  induction t generalizing p with
  | zero =>
    unfold ca_state init_config CellAutomaton.embed_config exp_core word_to_config
      mirror_config mirror_pos mirror_phase
    simp only [CellAutomaton.nextt_zero, List.length_singleton]
    split <;> simp_all [ge_iff_le] <;> omega
  | succ t ih =>
    rw [ca_state_succ, exp_δ_mirror]
    conv_lhs => rw [show (ca_state t p).2.1 = mirror_config t p from ih p]
    conv_lhs => rw [show (ca_state t (p - 1)).2.1 = mirror_config t (p - 1) from ih (p - 1)]
    simp only [← mirror_invariant]


/-! ## Signal Trajectory -/

def sig_traj : ℕ → ℤ × SigState
  | 0 => (0, .SR)
  | t + 1 =>
    let (pos, dir) := sig_traj t
    let new_pos := if dir == .SR then pos + 1 else pos - 1
    let m := mirror_config (t + 1) new_pos
    let u := decide (new_pos = 0)
    let new_dir := match dir with
      | .SR => if m == .M2 then .SL else .SR
      | .SL => if u then .SR else .SL
      | .None => .None
    (new_pos, new_dir)

def expected_sig (t : ℕ) (p : ℤ) : SigState :=
  if p = (sig_traj t).1 then (sig_traj t).2 else .None

lemma sig_traj_dir_ne_none (t : ℕ) : (sig_traj t).2 ≠ .None := by
  induction t with
  | zero => simp [sig_traj]
  | succ t ih =>
    simp only [sig_traj]
    cases hd : (sig_traj t).2 <;> simp_all <;> split <;> simp

/-! ## exp_δ Signal Helpers -/

-- When no signal arrives (left not SR, right not SL), output signal is None
lemma exp_δ_sig_none (l c r : ExpQ) (hl : l.1 ≠ .SR) (hr : r.1 ≠ .SL) :
    (exp_δ l c r).1 = .None := by
  rcases l with ⟨sl, ml, ul⟩; rcases c with ⟨sc, mc, uc⟩; rcases r with ⟨sr, mr, ur⟩
  simp only at hl hr; unfold exp_δ; cases sl <;> cases sr <;> simp_all

-- When SR arrives from left, output depends on new mirror state
lemma exp_δ_sig_of_sr (l c r : ExpQ) (hl : l.1 = .SR) :
    (exp_δ l c r).1 = if (exp_δ l c r).2.1 == .M2 then .SL else .SR := by
  rcases l with ⟨sl, ml, ul⟩; rcases c with ⟨sc, mc, uc⟩; rcases r with ⟨sr, mr, ur⟩
  simp only at hl; subst hl; unfold exp_δ; cases mc <;> cases ml <;> simp

-- When SL arrives from right (no SR from left), output depends on is_unit
lemma exp_δ_sig_of_sl (l c r : ExpQ) (hl : l.1 ≠ .SR) (hr : r.1 = .SL) :
    (exp_δ l c r).1 = if c.2.2 then .SR else .SL := by
  rcases l with ⟨sl, ml, ul⟩; rcases c with ⟨sc, mc, uc⟩; rcases r with ⟨sr, mr, ur⟩
  simp only at hl hr; subst hr; unfold exp_δ; cases sl <;> simp_all

/-! ## sig_traj Component Lemmas -/

lemma sig_traj_pos_succ (t : ℕ) :
    (sig_traj (t + 1)).1 =
      if (sig_traj t).2 == .SR then (sig_traj t).1 + 1 else (sig_traj t).1 - 1 := by
  simp [sig_traj]

lemma sig_traj_dir_succ_of_sr (t : ℕ) (h : (sig_traj t).2 = .SR) :
    (sig_traj (t + 1)).2 =
      if mirror_config (t + 1) ((sig_traj t).1 + 1) == .M2 then .SL else .SR := by
  simp [sig_traj, h]

lemma sig_traj_dir_succ_of_sl (t : ℕ) (h : (sig_traj t).2 = .SL) :
    (sig_traj (t + 1)).2 =
      if decide ((sig_traj t).1 - 1 = (0 : ℤ)) then .SR else .SL := by
  simp [sig_traj, h]

/-! ## Mirror at Next Step -/

lemma mirror_at_succ (t : ℕ) (p : ℤ) :
    (exp_δ (ca_state t (p - 1)) (ca_state t p) (ca_state t (p + 1))).2.1 =
      mirror_config (t + 1) p := by
  have := ca_mirror_matches (t + 1) p
  rwa [ca_state_succ] at this

/-! ## Signal Invariant -/

theorem signal_invariant (t : ℕ) (p : ℤ) :
    (ca_state t p).1 = expected_sig t p := by
  induction t generalizing p with
  | zero =>
    unfold ca_state init_config CellAutomaton.embed_config exp_core word_to_config
      expected_sig sig_traj
    simp only [CellAutomaton.nextt_zero, List.length_singleton]
    split <;> simp_all [ge_iff_le] <;> omega
  | succ t ih =>
    rw [ca_state_succ]
    have h_ne := sig_traj_dir_ne_none t
    rcases hdir : (sig_traj t).2 with _ | _ | _
    · -- dir = SR: signal moves right to pos + 1
      have h_pos : (sig_traj (t + 1)).1 = (sig_traj t).1 + 1 := by
        rw [sig_traj_pos_succ]; simp [hdir]
      have h_dir := sig_traj_dir_succ_of_sr t hdir
      by_cases hp : p = (sig_traj t).1 + 1
      · -- p = pos + 1: signal arrives from left
        subst hp
        have h_l : (ca_state t (sig_traj t).1).1 = .SR := by
          rw [ih]; simp [expected_sig, hdir]
        rw [show (sig_traj t).1 + 1 - 1 = (sig_traj t).1 from by ring]
        rw [exp_δ_sig_of_sr _ _ _ h_l]
        have hm := mirror_at_succ t ((sig_traj t).1 + 1)
        rw [show (sig_traj t).1 + 1 - 1 = (sig_traj t).1 from by ring] at hm
        rw [hm]
        simp [expected_sig, h_pos, h_dir]
      · -- p ≠ pos + 1: no signal arrives
        have h_l : (ca_state t (p - 1)).1 ≠ .SR := by
          rw [ih]; unfold expected_sig
          split <;> (simp_all; try omega)
        have h_r : (ca_state t (p + 1)).1 ≠ .SL := by
          rw [ih]; unfold expected_sig
          split <;> simp_all
        rw [exp_δ_sig_none _ _ _ h_l h_r]
        simp only [expected_sig, h_pos]
        split <;> simp_all
    · -- dir = SL: signal moves left to pos - 1
      have h_pos : (sig_traj (t + 1)).1 = (sig_traj t).1 - 1 := by
        rw [sig_traj_pos_succ]; simp [hdir]
      have h_dir := sig_traj_dir_succ_of_sl t hdir
      by_cases hp : p = (sig_traj t).1 - 1
      · -- p = pos - 1: signal arrives from right
        subst hp
        have h_r : (ca_state t (sig_traj t).1).1 = .SL := by
          rw [ih]; simp [expected_sig, hdir]
        have h_l_ne : (ca_state t ((sig_traj t).1 - 1 - 1)).1 ≠ .SR := by
          rw [ih]; unfold expected_sig
          split <;> (simp_all; try omega)
        rw [show (sig_traj t).1 - 1 + 1 = (sig_traj t).1 from by ring]
        rw [exp_δ_sig_of_sl _ _ _ h_l_ne h_r, ca_unit_matches]
        simp [expected_sig, h_pos, h_dir]
      · -- p ≠ pos - 1: no signal arrives
        have h_l : (ca_state t (p - 1)).1 ≠ .SR := by
          rw [ih]; unfold expected_sig
          split <;> simp_all
        have h_r : (ca_state t (p + 1)).1 ≠ .SL := by
          rw [ih]; unfold expected_sig
          split <;> (simp_all; try omega)
        rw [exp_δ_sig_none _ _ _ h_l h_r]
        simp only [expected_sig, h_pos]
        split <;> simp_all
    · -- dir = None: impossible
      exact absurd hdir h_ne

/-! ## Remaining Specifications -/

-- mirror_config is M2 iff position matches mirror_pos and phase is M2
lemma mirror_config_eq_M2 (t : ℕ) (p : ℤ) :
    mirror_config t p = .M2 ↔ p = mirror_pos t ∧ mirror_phase t = .M2 := by
  unfold mirror_config
  split <;> simp_all

-- mirror_config is not M2 when position differs from mirror_pos
lemma mirror_config_ne_M2_of_ne_pos (t : ℕ) (p : ℤ) (h : p ≠ mirror_pos t) :
    mirror_config t p ≠ .M2 := by
  intro heq; exact h ((mirror_config_eq_M2 t p).mp heq).1

-- During right phase, no spurious M2 encounter for sig_traj
-- At time t+1 with position j+1, mirror_config is not M2 when j+1 < 2^k
lemma no_M2_during_right_phase (k : ℕ) (j : ℕ) (hj : j + 1 < 2 ^ k) :
    mirror_config (bounce_time k + j + 1) (↑(j + 1)) ≠ .M2 := by
  intro heq
  have ⟨h_pos, h_phase⟩ := (mirror_config_eq_M2 _ _).mp heq
  have hpow : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  have h2k1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hbt : bounce_time k = 2 * 2 ^ k - 2 := by simp only [bounce_time, h2k1]
  -- From h_phase: (bounce_time k + j + 1) % 3 = 1
  simp only [mirror_phase] at h_phase
  have h3 := (bounce_time k + j + 1) % 3
  have hmod3 : (bounce_time k + j + 1) % 3 = 0 ∨ (bounce_time k + j + 1) % 3 = 1 ∨ (bounce_time k + j + 1) % 3 = 2 := by omega
  rcases hmod3 with hm | hm | hm <;> simp [hm] at h_phase
  -- Now hm: (bounce_time k + j + 1) % 3 = 1
  -- h_pos: ↑(j + 1) = mirror_pos (bounce_time k + j + 1) = ((bounce_time k + j + 1 : ℤ) + 2) / 3
  simp only [mirror_pos] at h_pos
  -- Substitute bounce_time k = 2 * 2^k - 2
  have ⟨q, hq⟩ : ∃ q, bounce_time k + j + 1 = 3 * q + 1 := ⟨(bounce_time k + j + 1) / 3, by omega⟩
  rw [hq] at h_pos
  push_cast at h_pos
  have hq_nat : q = j := by omega
  -- bounce_time k + j + 1 = 3 * j + 1
  -- So bounce_time k = 2 * j, i.e., j = 2^k - 1 (from hbt)
  rw [hbt] at hq; omega

-- At collision time, mirror IS M2 at the signal position
lemma M2_at_collision (k : ℕ) :
    mirror_config (collision_time k) (↑(2 ^ k)) = .M2 := by
  rw [mirror_config_eq_M2]
  refine ⟨?_, mirror_phase_at_collision k⟩
  simp only [mirror_pos, collision_time_eq]
  have hsub : 2 ≤ 3 * 2 ^ k := by nlinarith [Nat.one_le_pow k 2 (by omega)]
  rw [Nat.cast_sub hsub]
  push_cast; omega

-- During left phase, signal position ≠ 0 (so no unit-bounce)
-- sig_traj position during left phase is 2^k - j where j goes from 1 to 2^k
lemma left_phase_pos_ne_zero (k : ℕ) (j : ℕ) (_hj : 0 < j) (hj2 : j < 2 ^ k) :
    (↑(2 ^ k) : ℤ) - ↑j ≠ 0 := by
  have : (↑j : ℤ) < ↑(2 ^ k) := Nat.cast_lt.mpr hj2
  omega

/-! ## Phase Invariants

The proofs are structured by induction on k (phase number).
Given that sig_traj at bounce_time k is (0, SR), we show:
1. Right phase: sig_traj(bounce_time k + j) = (j, SR) for j < 2^k
2. Collision: sig_traj(collision_time k) = (2^k, SL)
3. Left phase: sig_traj(collision_time k + j) = (2^k - j, SL) for j < 2^k
4. End of left phase: sig_traj(bounce_time(k+1)) = (0, SR)
-/

-- Stepping lemma: if sig_traj t = (p, SR) and mirror_config (t+1) (p+1) ≠ M2,
-- then sig_traj (t+1) = (p+1, SR)
lemma sig_traj_step_sr (t : ℕ) (p : ℤ) (h : sig_traj t = (p, .SR))
    (hm : mirror_config (t + 1) (p + 1) ≠ .M2) :
    sig_traj (t + 1) = (p + 1, .SR) := by
  have h1 := sig_traj_pos_succ t
  have h2 := sig_traj_dir_succ_of_sr t (by rw [h])
  rw [h] at h1
  simp at h1 h2
  ext <;> simp_all

-- Stepping lemma: if sig_traj t = (p, SR) and mirror_config (t+1) (p+1) = M2,
-- then sig_traj (t+1) = (p+1, SL)
lemma sig_traj_step_sr_bounce (t : ℕ) (p : ℤ) (h : sig_traj t = (p, .SR))
    (hm : mirror_config (t + 1) (p + 1) = .M2) :
    sig_traj (t + 1) = (p + 1, .SL) := by
  have h1 := sig_traj_pos_succ t
  have h2 := sig_traj_dir_succ_of_sr t (by rw [h])
  rw [h] at h1
  simp at h1 h2
  ext <;> simp_all

-- Stepping lemma: if sig_traj t = (p, SL) and p - 1 ≠ 0,
-- then sig_traj (t+1) = (p-1, SL)
lemma sig_traj_step_sl (t : ℕ) (p : ℤ) (h : sig_traj t = (p, .SL))
    (hp : p - 1 ≠ 0) :
    sig_traj (t + 1) = (p - 1, .SL) := by
  have h1 := sig_traj_pos_succ t
  have h2 := sig_traj_dir_succ_of_sl t (by rw [h])
  rw [h] at h1
  simp at h1 h2
  ext <;> simp_all

-- Stepping lemma: if sig_traj t = (p, SL) and p - 1 = 0,
-- then sig_traj (t+1) = (p - 1, SR)
lemma sig_traj_step_sl_bounce (t : ℕ) (p : ℤ) (h : sig_traj t = (p, .SL))
    (hp : p - 1 = 0) :
    sig_traj (t + 1) = (p - 1, .SR) := by
  have h1 := sig_traj_pos_succ t
  have h2 := sig_traj_dir_succ_of_sl t (by rw [h])
  rw [h] at h1
  simp at h1 h2
  ext <;> simp_all

-- Right phase: given base, induction on j
private lemma sig_traj_right_phase' (k : ℕ) (j : ℕ) (hj : j < 2 ^ k)
    (h_base : sig_traj (bounce_time k) = (0, .SR)) :
    sig_traj (bounce_time k + j) = (↑j, .SR) := by
  induction j with
  | zero => simpa
  | succ j ih =>
    have h_prev := ih (by omega)
    have h_time : bounce_time k + (j + 1) = (bounce_time k + j) + 1 := by omega
    rw [h_time]
    have h_not_m2 := no_M2_during_right_phase k j hj
    rw [sig_traj_step_sr _ _ h_prev h_not_m2]
    norm_cast

-- Collision: sig_traj gives (2^k, SL)
private lemma sig_traj_at_collision' (k : ℕ)
    (h_base : sig_traj (bounce_time k) = (0, .SR)) :
    sig_traj (collision_time k) = (↑(2 ^ k), .SL) := by
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have h_prev := sig_traj_right_phase' k (2 ^ k - 1) (by omega) h_base
  have h_time : collision_time k = (bounce_time k + (2 ^ k - 1)) + 1 := by
    simp only [collision_time]; omega
  rw [h_time]
  have h_m2 : mirror_config (bounce_time k + (2 ^ k - 1) + 1) (↑(2 ^ k - 1 : ℕ) + 1) = .M2 := by
    rw [show (↑(2 ^ k - 1 : ℕ) : ℤ) + 1 = ↑(2 ^ k) from by norm_cast; omega,
      show bounce_time k + (2 ^ k - 1) + 1 = collision_time k from by
        simp only [collision_time]; omega]
    exact M2_at_collision k
  rw [sig_traj_step_sr_bounce _ _ h_prev h_m2]
  refine Prod.ext ?_ rfl
  show (↑(2 ^ k - 1 : ℕ) : ℤ) + 1 = ↑(2 ^ k)
  norm_cast; omega

-- Left phase: given collision result, induction on j (strict bound)
private lemma sig_traj_left_phase' (k : ℕ) (j : ℕ) (hj : j < 2 ^ k)
    (h_base : sig_traj (bounce_time k) = (0, .SR)) :
    sig_traj (collision_time k + j) = ((↑(2 ^ k) : ℤ) - ↑j, .SL) := by
  induction j with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, Nat.add_zero]
    exact sig_traj_at_collision' k h_base
  | succ j ih =>
    have hj_lt : j < 2 ^ k := by omega
    have h_prev := ih hj_lt
    have h_time : collision_time k + (j + 1) = (collision_time k + j) + 1 := by omega
    rw [h_time]
    have h_pos_ne : (↑(2 ^ k) : ℤ) - ↑j - 1 ≠ 0 := by
      have h := Nat.cast_lt (α := ℤ).mpr hj
      push_cast at h ⊢
      intro heq; linarith
    rw [sig_traj_step_sl _ _ h_prev h_pos_ne]
    refine Prod.ext ?_ rfl
    push_cast; ring

-- End of left phase: bounce at position 0
private lemma sig_traj_left_phase_end' (k : ℕ)
    (h_base : sig_traj (bounce_time k) = (0, .SR)) :
    sig_traj (bounce_time (k + 1)) = (0, .SR) := by
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have h_prev := sig_traj_left_phase' k (2 ^ k - 1) (by omega) h_base
  have h_time : bounce_time (k + 1) = (collision_time k + (2 ^ k - 1)) + 1 := by
    rw [bounce_time_succ]; omega
  rw [h_time]
  have h_pos_eq : (↑(2 ^ k) : ℤ) - ↑(2 ^ k - 1 : ℕ) - 1 = 0 := by
    have := congr_arg (Nat.cast (R := ℤ)) (Nat.sub_add_cancel hpow)
    push_cast at this ⊢; linarith
  rw [sig_traj_step_sl_bounce _ _ h_prev h_pos_eq]
  refine Prod.ext ?_ rfl
  exact h_pos_eq

-- Main result: sig_traj at bounce_time k = (0, SR)
lemma sig_traj_at_bounce (k : ℕ) : sig_traj (bounce_time k) = (0, .SR) := by
  induction k with
  | zero => simp [sig_traj, bounce_time]
  | succ k ih => exact sig_traj_left_phase_end' k ih

-- Between consecutive bounce times, position is strictly positive
private lemma sig_traj_nonzero_between (k j : ℕ) (hj1 : 0 < j) (hj2 : j < 2 ^ (k + 1)) :
    (sig_traj (bounce_time k + j)).1 ≠ 0 := by
  have hb := sig_traj_at_bounce k
  rcases Nat.lt_or_ge j (2 ^ k) with hjk | hjk
  · -- Right phase: position = ↑j > 0
    rw [sig_traj_right_phase' k j hjk hb]; simp
    exact_mod_cast hj1.ne'
  · rcases eq_or_lt_of_le hjk with rfl | hjk
    · -- Collision: position = ↑(2^k) > 0
      rw [show bounce_time k + 2 ^ k = collision_time k from rfl,
        sig_traj_at_collision' k hb]; simp
    · -- Left phase: position = ↑(2^k) - ↑(j - 2^k) > 0
      have hm_lt : j - 2 ^ k < 2 ^ k := by omega
      rw [show bounce_time k + j = collision_time k + (j - 2 ^ k) from by
          simp [collision_time]; omega,
        sig_traj_left_phase' k (j - 2 ^ k) hm_lt hb]; simp
      have := Nat.cast_lt (α := ℤ).mpr hm_lt
      push_cast at this ⊢; linarith

-- Every time falls into [bounce_time k, bounce_time (k+1)) for some k
private lemma time_in_period (t : ℕ) : ∃ k j, t = bounce_time k + j ∧ j < 2 ^ (k + 1) := by
  suffices h : ∃ k, bounce_time k ≤ t ∧ t < bounce_time (k + 1) by
    obtain ⟨k, hle, hlt⟩ := h
    have hperiod : bounce_time (k + 1) = bounce_time k + 2 ^ (k + 1) := by
      simp only [bounce_time]
      have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
      omega
    exact ⟨k, t - bounce_time k, by omega, by omega⟩
  induction t with
  | zero => exact ⟨0, by simp [bounce_time], by simp [bounce_time]⟩
  | succ t ih =>
    obtain ⟨k, hle, hlt⟩ := ih
    if h : t + 1 < bounce_time (k + 1) then
      exact ⟨k, by omega, h⟩
    else
      push_neg at h
      refine ⟨k + 1, h, ?_⟩
      simp only [bounce_time] at hlt ⊢
      have h1 : 2 ^ (k + 3) = 2 * 2 ^ (k + 2) := by ring
      have h2 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      have h3 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
      omega

-- sig_traj is at position 0 iff t is a bounce time
lemma sig_traj_zero_iff (t : ℕ) :
    (sig_traj t).1 = 0 ↔ ∃ k, t = bounce_time k := by
  constructor
  · intro h0
    obtain ⟨k, j, rfl, hj⟩ := time_in_period t
    rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj1
    · exact ⟨k, by omega⟩
    · exact absurd h0 (sig_traj_nonzero_between k j hj1 hj)
  · rintro ⟨k, rfl⟩
    exact congr_arg Prod.fst (sig_traj_at_bounce k)

private lemma comp_iff_sig_pos_zero (t : ℕ) :
    exp_core.comp ⟬([()] : Word Unit)⟭ t 0 = true ↔ (sig_traj t).1 = 0 := by
  show exp_core.project (ca_state t 0) = true ↔ _
  have h_sig := signal_invariant t 0
  constructor
  · intro hp
    by_contra h_ne
    have h_exp : expected_sig t 0 = .None := by
      simp only [expected_sig, show ¬((0 : ℤ) = (sig_traj t).1) from fun h => h_ne h.symm,
        ite_false]
    rw [h_exp] at h_sig
    simp only [exp_core] at hp; rw [h_sig] at hp; simp at hp
  · intro h_eq
    have h_exp : expected_sig t 0 = (sig_traj t).2 := by
      unfold expected_sig; rw [h_eq]; simp
    rw [h_exp] at h_sig
    simp only [exp_core]; rw [h_sig]
    cases hd : (sig_traj t).2 with
    | SR => simp
    | SL => simp
    | None => exact absurd hd (sig_traj_dir_ne_none t)

theorem exp_core_spec (τ : ℕ) :
    exp_core.comp ⟬([()] : Word Unit)⟭ τ 0 = true ↔ ∃ k, τ = bounce_time k := by
  rw [comp_iff_sig_pos_zero, sig_traj_zero_iff]

end CellularAutomatas
