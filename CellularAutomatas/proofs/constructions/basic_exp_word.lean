import CellularAutomatas.defs
import CellularAutomatas.proofs.constructions.basic_compose_k_steps
import CellularAutomatas.proofs.constructions.basic_ca_left_edge_marker

/-!
# Real-Time Recognition of { w | |w| = 2^n }

## Core CA (exp_core)

Runs on input `[Unit]` (a single cell). A signal bounces between position 0
and a slow mirror moving at speed 1/3. The signal returns to position 0 at
exactly the times τ = 2^(k+1) − 2 (bounce_time k), with differences doubling
each cycle: 2, 4, 8, 16, ...

### Execution Trace

```
        pos: -2   -1    0      1      2      3      4      5      6      7      8
input:        #    #   Unit    #      #      #      #      #      #      #      #
        ────────────────────────────────────────────────────────────────────────────
t=0                   SR,M1
t=1                          SR,M2                                                   ← bounce!
t=2                   SL      M3
t=3                          SR,M1
t=4                                 SR,M2                                            ← bounce!
t=5                          SL      M3
t=6                   SL             M1
t=7                          SR            M2
t=8                                 SR     M3
t=9                                        SR,M1
t=10                                              SR,M2                              ← bounce!
t=11                                       SL      M3
t=12                                SL             M1
t=13                         SL                          M2
t=14                  SL                                 M3
t=15                         SR                          M1
t=16                                SR                         M2
t=17                                       SR                  M3
t=18                                              SR            M1
t=19                                                     SR          M2
t=20                                                            SR   M3
t=21                                                                 SR,M1
t=22                                                                        SR,M2   ← bounce!
t=23                                                                 SL      M3
t=24                                                            SL          M1
t=25                                                     SL
t=26                                              SL
t=27                                       SL
t=28                                SL
t=29                         SL
t=30                  SL
```

Signal at p=0: t = 0, 2, 6, 14, 30 — differences 2, 4, 8, 16 (doubling).
Return times: b(k) = 2^(k+1) − 2.

### Cell State

Triple `(S, M, is_unit)`:
- `S ∈ {SR, SL, None}` — signal direction
- `M ∈ {M1, M2, M3, None}` — mirror phase
- `is_unit : Bool` — true only at position 0, preserved forever

Mirror evolves independently of signal: M1→shift right→M2→M3→M1.
Signal bounces: SR at M2 → SL, SL at is_unit → SR.

## Full Construction

Composes `leftEdgeCA` (1 step, maps any non-empty word to `[()]`) with `exp_core`.
For word of length n ≥ 2: accepts iff n-2 = bounce_time k, i.e., n = 2^(k+1).
The n=1 = 2^0 case is handled by a custom project on the phase1 state.
-/

namespace CellularAutomatas

-- ═══════════════════════════════════════════════════════════════════
-- Part 1: exp_core — marks p=0 at times τ = 2^(k+1) − 2 on [Unit]
-- ═══════════════════════════════════════════════════════════════════

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
  · have h1 : (t + 1) % 3 = 1 := by omega
    simp only [mirror_phase, hmod, h1]
    rw [mirror_pos_of_mod3_eq_0 t hmod]
    by_cases hp : p = mirror_pos t + 1
    <;> by_cases hp2 : p = mirror_pos t
    <;> by_cases hp3 : p - 1 = mirror_pos t
    <;> (simp_all; try omega)
  · have h1 : (t + 1) % 3 = 2 := by omega
    simp only [mirror_phase, hmod, h1]
    rw [mirror_pos_of_mod3_eq_1 t hmod]
    by_cases hp : p = mirror_pos t
    <;> by_cases hp3 : p - 1 = mirror_pos t
    <;> (simp_all; try omega)
  · have h1 : (t + 1) % 3 = 0 := by omega
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

/-! ## Full CA Invariant -/

def init_config : Config ExpQ := CellAutomaton.embed_config (C := exp_core) ⟬([()] : Word Unit)⟭

def ca_state (t : ℕ) (p : ℤ) : ExpQ := exp_core.nextt init_config t p

lemma exp_δ_preserves_unit (l c r : ExpQ) : (exp_δ l c r).2.2 = c.2.2 := by
  simp [exp_δ]

lemma exp_δ_mirror (l c r : ExpQ) :
    (exp_δ l c r).2.1 = match c.2.1 with
      | .M1 => MirrorState.None
      | .M2 => .M3
      | .M3 => .M1
      | .None => if l.2.1 == .M1 then .M2 else .None := by
  unfold exp_δ
  cases c.2.1 <;> simp
  cases l.2.1 <;> simp

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

lemma exp_δ_sig_none (l c r : ExpQ) (hl : l.1 ≠ .SR) (hr : r.1 ≠ .SL) :
    (exp_δ l c r).1 = .None := by
  rcases l with ⟨sl, ml, ul⟩; rcases c with ⟨sc, mc, uc⟩; rcases r with ⟨sr, mr, ur⟩
  simp only at hl hr; unfold exp_δ; cases sl <;> cases sr <;> simp_all

lemma exp_δ_sig_of_sr (l c r : ExpQ) (hl : l.1 = .SR) :
    (exp_δ l c r).1 = if (exp_δ l c r).2.1 == .M2 then .SL else .SR := by
  rcases l with ⟨sl, ml, ul⟩; rcases c with ⟨sc, mc, uc⟩; rcases r with ⟨sr, mr, ur⟩
  simp only at hl; subst hl; unfold exp_δ; cases mc <;> cases ml <;> simp

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
    · -- dir = SR
      have h_pos : (sig_traj (t + 1)).1 = (sig_traj t).1 + 1 := by
        rw [sig_traj_pos_succ]; simp [hdir]
      have h_dir := sig_traj_dir_succ_of_sr t hdir
      by_cases hp : p = (sig_traj t).1 + 1
      · subst hp
        have h_l : (ca_state t (sig_traj t).1).1 = .SR := by
          rw [ih]; simp [expected_sig, hdir]
        rw [show (sig_traj t).1 + 1 - 1 = (sig_traj t).1 from by ring]
        rw [exp_δ_sig_of_sr _ _ _ h_l]
        have hm := mirror_at_succ t ((sig_traj t).1 + 1)
        rw [show (sig_traj t).1 + 1 - 1 = (sig_traj t).1 from by ring] at hm
        rw [hm]
        simp [expected_sig, h_pos, h_dir]
      · have h_l : (ca_state t (p - 1)).1 ≠ .SR := by
          rw [ih]; unfold expected_sig
          split <;> (simp_all; try omega)
        have h_r : (ca_state t (p + 1)).1 ≠ .SL := by
          rw [ih]; unfold expected_sig
          split <;> simp_all
        rw [exp_δ_sig_none _ _ _ h_l h_r]
        simp only [expected_sig, h_pos]
        split <;> simp_all
    · -- dir = SL
      have h_pos : (sig_traj (t + 1)).1 = (sig_traj t).1 - 1 := by
        rw [sig_traj_pos_succ]; simp [hdir]
      have h_dir := sig_traj_dir_succ_of_sl t hdir
      by_cases hp : p = (sig_traj t).1 - 1
      · subst hp
        have h_r : (ca_state t (sig_traj t).1).1 = .SL := by
          rw [ih]; simp [expected_sig, hdir]
        have h_l_ne : (ca_state t ((sig_traj t).1 - 1 - 1)).1 ≠ .SR := by
          rw [ih]; unfold expected_sig
          split <;> (simp_all; try omega)
        rw [show (sig_traj t).1 - 1 + 1 = (sig_traj t).1 from by ring]
        rw [exp_δ_sig_of_sl _ _ _ h_l_ne h_r, ca_unit_matches]
        simp [expected_sig, h_pos, h_dir]
      · have h_l : (ca_state t (p - 1)).1 ≠ .SR := by
          rw [ih]; unfold expected_sig
          split <;> simp_all
        have h_r : (ca_state t (p + 1)).1 ≠ .SL := by
          rw [ih]; unfold expected_sig
          split <;> (simp_all; try omega)
        rw [exp_δ_sig_none _ _ _ h_l h_r]
        simp only [expected_sig, h_pos]
        split <;> simp_all
    · exact absurd hdir h_ne

/-! ## Mirror/Signal Specification Helpers -/

lemma mirror_config_eq_M2 (t : ℕ) (p : ℤ) :
    mirror_config t p = .M2 ↔ p = mirror_pos t ∧ mirror_phase t = .M2 := by
  unfold mirror_config
  split <;> simp_all

lemma mirror_config_ne_M2_of_ne_pos (t : ℕ) (p : ℤ) (h : p ≠ mirror_pos t) :
    mirror_config t p ≠ .M2 := by
  intro heq; exact h ((mirror_config_eq_M2 t p).mp heq).1

lemma no_M2_during_right_phase (k : ℕ) (j : ℕ) (hj : j + 1 < 2 ^ k) :
    mirror_config (bounce_time k + j + 1) (↑(j + 1)) ≠ .M2 := by
  intro heq
  have ⟨h_pos, h_phase⟩ := (mirror_config_eq_M2 _ _).mp heq
  have hpow : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
  have h2k1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hbt : bounce_time k = 2 * 2 ^ k - 2 := by simp only [bounce_time, h2k1]
  simp only [mirror_phase] at h_phase
  have hmod3 : (bounce_time k + j + 1) % 3 = 0 ∨ (bounce_time k + j + 1) % 3 = 1 ∨ (bounce_time k + j + 1) % 3 = 2 := by omega
  rcases hmod3 with hm | hm | hm <;> simp [hm] at h_phase
  simp only [mirror_pos] at h_pos
  have ⟨q, hq⟩ : ∃ q, bounce_time k + j + 1 = 3 * q + 1 := ⟨(bounce_time k + j + 1) / 3, by omega⟩
  rw [hq] at h_pos
  push_cast at h_pos
  have hq_nat : q = j := by omega
  rw [hbt] at hq; omega

lemma M2_at_collision (k : ℕ) :
    mirror_config (collision_time k) (↑(2 ^ k)) = .M2 := by
  rw [mirror_config_eq_M2]
  refine ⟨?_, mirror_phase_at_collision k⟩
  simp only [mirror_pos, collision_time_eq]
  have hsub : 2 ≤ 3 * 2 ^ k := by nlinarith [Nat.one_le_pow k 2 (by omega)]
  rw [Nat.cast_sub hsub]
  push_cast; omega

lemma left_phase_pos_ne_zero (k : ℕ) (j : ℕ) (_hj : 0 < j) (hj2 : j < 2 ^ k) :
    (↑(2 ^ k) : ℤ) - ↑j ≠ 0 := by
  have : (↑j : ℤ) < ↑(2 ^ k) := Nat.cast_lt.mpr hj2
  omega

/-! ## Phase Invariants -/

lemma sig_traj_step_sr (t : ℕ) (p : ℤ) (h : sig_traj t = (p, .SR))
    (hm : mirror_config (t + 1) (p + 1) ≠ .M2) :
    sig_traj (t + 1) = (p + 1, .SR) := by
  have h1 := sig_traj_pos_succ t
  have h2 := sig_traj_dir_succ_of_sr t (by rw [h])
  rw [h] at h1
  simp at h1 h2
  ext <;> simp_all

lemma sig_traj_step_sr_bounce (t : ℕ) (p : ℤ) (h : sig_traj t = (p, .SR))
    (hm : mirror_config (t + 1) (p + 1) = .M2) :
    sig_traj (t + 1) = (p + 1, .SL) := by
  have h1 := sig_traj_pos_succ t
  have h2 := sig_traj_dir_succ_of_sr t (by rw [h])
  rw [h] at h1
  simp at h1 h2
  ext <;> simp_all

lemma sig_traj_step_sl (t : ℕ) (p : ℤ) (h : sig_traj t = (p, .SL))
    (hp : p - 1 ≠ 0) :
    sig_traj (t + 1) = (p - 1, .SL) := by
  have h1 := sig_traj_pos_succ t
  have h2 := sig_traj_dir_succ_of_sl t (by rw [h])
  rw [h] at h1
  simp at h1 h2
  ext <;> simp_all

lemma sig_traj_step_sl_bounce (t : ℕ) (p : ℤ) (h : sig_traj t = (p, .SL))
    (hp : p - 1 = 0) :
    sig_traj (t + 1) = (p - 1, .SR) := by
  have h1 := sig_traj_pos_succ t
  have h2 := sig_traj_dir_succ_of_sl t (by rw [h])
  rw [h] at h1
  simp at h1 h2
  ext <;> simp_all

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

lemma sig_traj_at_bounce (k : ℕ) : sig_traj (bounce_time k) = (0, .SR) := by
  induction k with
  | zero => simp [sig_traj, bounce_time]
  | succ k ih => exact sig_traj_left_phase_end' k ih

private lemma sig_traj_nonzero_between (k j : ℕ) (hj1 : 0 < j) (hj2 : j < 2 ^ (k + 1)) :
    (sig_traj (bounce_time k + j)).1 ≠ 0 := by
  have hb := sig_traj_at_bounce k
  rcases Nat.lt_or_ge j (2 ^ k) with hjk | hjk
  · rw [sig_traj_right_phase' k j hjk hb]; simp
    exact_mod_cast hj1.ne'
  · rcases eq_or_lt_of_le hjk with rfl | hjk
    · rw [show bounce_time k + 2 ^ k = collision_time k from rfl,
        sig_traj_at_collision' k hb]; simp
    · have hm_lt : j - 2 ^ k < 2 ^ k := by omega
      rw [show bounce_time k + j = collision_time k + (j - 2 ^ k) from by
          simp [collision_time]; omega,
        sig_traj_left_phase' k (j - 2 ^ k) hm_lt hb]; simp
      have := Nat.cast_lt (α := ℤ).mpr hm_lt
      push_cast at this ⊢; linarith

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


-- ═══════════════════════════════════════════════════════════════════
-- Part 2: Full Construction — { w | |w| = 2^n } in real time
-- ═══════════════════════════════════════════════════════════════════

open CellAutomaton

/-! ## Composition: leftEdgeCA (1 step) → exp_core -/

def exp_composed : ComposeKSteps :=
  { C1 := leftEdgeCA Unit, C2 := exp_core, k := 1 }

-- Accept in phase1 for n=1 (handles 2^0), in phase2 via exp_core
def exp_final_project (s : exp_composed.State) : Bool :=
  match s with
  | .phase1 ⟨0, _⟩ true => true
  | .phase2 q => exp_core.project q
  | _ => false

def exp_word_ca : CA_rt Unit := {
  Q := exp_composed.State,
  δ := exp_composed.C.δ,
  embed := exp_composed.C.embed,
  project := exp_final_project,
}

/-! ## Computational Verification -/

def test_exp_word (n : ℕ) : Bool := exp_word_ca.accepts (List.replicate n ())
#eval! (List.range 10).map (fun n => (n, test_exp_word n))
-- [(0,false),(1,true),(2,true),(3,false),(4,true),(5,false),(6,false),(7,false),(8,true),(9,false)]

/-! ## Helper: after 1 step, all cells are in phase2 -/

private lemma composed_phase2 (c : Config Unit？) (t : ℕ) (p : ℤ) :
    ∃ q, exp_composed.C.nextt ⦋c⦌ (t + 1) p = .phase2 q := by
  induction t generalizing p with
  | zero =>
    rw [nextt_succ, nextt_zero]
    exact ⟨_, rfl⟩
  | succ t ih =>
    rw [show t + 1 + 1 = (t + 1) + 1 from by ring, nextt_succ]
    unfold CellAutomaton.next
    obtain ⟨_, hl⟩ := ih (p - 1)
    obtain ⟨_, hc⟩ := ih p
    obtain ⟨_, hr⟩ := ih (p + 1)
    rw [hl, hc, hr]
    exact ⟨_, rfl⟩

/-! ## Connecting exp_word_ca to exp_composed.C -/

-- For t ≥ 1: exp_word_ca's comp equals exp_composed.C's comp
-- (the state is in phase2, so both projects agree)
private lemma comp_eq_for_ge1 (c : Config Unit？) (t : ℕ) (ht : t ≥ 1) (p : ℤ) :
    exp_word_ca.toCellAutomaton.comp c t p = exp_composed.C.comp c t p := by
  unfold CellAutomaton.comp CellAutomaton.project_config
  simp only [Function.comp_apply]
  -- nextt of exp_word_ca = nextt of exp_composed.C (same Q, δ, embed)
  change exp_final_project (exp_composed.C.nextt ⦋c⦌ t p) =
    exp_composed.C.project (exp_composed.C.nextt ⦋c⦌ t p)
  obtain ⟨q, hq⟩ := composed_phase2 c (t - 1) p
  rw [show t = (t - 1) + 1 from by omega, hq]
  rfl

/-! ## bounce_time ↔ power-of-two -/

private lemma bounce_time_iff (τ : ℕ) :
    (∃ k, τ = bounce_time k) ↔ ∃ k, τ + 2 = 2 ^ (k + 1) := by
  constructor
  · rintro ⟨k, rfl⟩
    use k; simp [bounce_time]
    have : 2 ^ (k + 1) ≥ 2 := by
      have := Nat.one_le_pow (k + 1) 2 (by omega); omega
    omega
  · rintro ⟨k, hk⟩
    use k; simp [bounce_time]; omega

/-! ## Main Acceptance Lemmas -/

private lemma accepts_ge2 (w : Word Unit) (hn : w.length ≥ 2) :
    exp_word_ca.accepts w = true ↔ ∃ k, w.length = 2 ^ (k + 1) := by
  have hw : w ≠ [] := by intro h; subst h; simp at hn
  -- exp_word_ca.accepts w = exp_word_ca.comp w (n-1) 0
  -- For n-1 ≥ 1, comp_eq_for_ge1 gives us exp_composed.C.comp w (n-1) 0
  show exp_word_ca.toCellAutomaton.comp (word_to_config w) (w.length - 1) 0 = true ↔ _
  rw [comp_eq_for_ge1 (word_to_config w) (w.length - 1) (by omega) 0]
  -- By ComposeKSteps.spec: exp_composed.C.comp w (n-1) 0 = exp_core.comp (leftEdgeCA.comp w 1) (n-2) 0
  rw [ComposeKSteps.spec]
  simp only [show w.length - 1 ≥ exp_composed.k from by simp [exp_composed]; omega, ite_true]
  -- leftEdgeCA.comp w 1 = ⟬[()]⟭ for non-empty w
  rw [show exp_composed.C1 = leftEdgeCA Unit from rfl,
      show exp_composed.C2 = exp_core from rfl,
      show exp_composed.k = 1 from rfl,
      CellAutomaton.leftEdgeCA.comp_spec w hw,
      show w.length - 1 - 1 = w.length - 2 from by omega]
  -- Now: exp_core.comp ⟬[()]⟭ (n-2) 0 = true ↔ ∃ k, n = 2^(k+1)
  rw [exp_core_spec]
  rw [bounce_time_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩

lemma exp_word_ca_correct (w : Word Unit) :
    exp_word_ca.accepts w = true ↔ ∃ n, w.length = 2 ^ n := by
  by_cases h0 : w.length = 0
  · -- n = 0: reject (no k with 0 = 2^k)
    constructor
    · intro h
      have hw : w = [] := by cases w <;> simp_all
      subst hw
      -- exp_word_ca.accepts [] = false by computation
      exact absurd h (by decide)
    · rintro ⟨n, hn⟩; simp_all
  · by_cases h1 : w.length = 1
    · -- n = 1 = 2^0: accept
      constructor
      · intro; exact ⟨0, h1⟩
      · intro
        -- w is a length-1 Unit word, so w = [()]
        have hw : w = [()] := by
          cases w with
          | nil => simp at h1
          | cons u t =>
            simp at h1; subst h1
            exact congrArg (· :: []) (Unit.ext u ())
        subst hw
        decide
    · -- n ≥ 2: use accepts_ge2
      have hn : w.length ≥ 2 := by omega
      rw [accepts_ge2 w hn]
      constructor
      · rintro ⟨k, hk⟩; exact ⟨k + 1, hk⟩
      · rintro ⟨n, hn'⟩
        cases n with
        | zero => simp at hn'; omega
        | succ n => exact ⟨n, hn'⟩

/-! ## Main Theorem -/

theorem exp_word_length_rt : ∃ C : CA_rt Unit, C.L = { w | ∃ n, w.length = 2 ^ n } := by
  use exp_word_ca
  ext w
  simp only [tCellAutomaton.L]
  exact exp_word_ca_correct w

end CellularAutomatas
