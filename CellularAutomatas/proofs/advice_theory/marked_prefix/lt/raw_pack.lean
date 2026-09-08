import CellularAutomatas.proofs.constructions.basic_ca_id
import CellularAutomatas.proofs.constructions.basic_ca_left_edge_marker
import CellularAutomatas.proofs.constructions.basic_compose_k_steps
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.speedup_compressed
import CellularAutomatas.proofs.constructions.trace_id
import CellularAutomatas.proofs.constructions.trace_kx

namespace CellularAutomatas.MarkedPrefix.LT.RawPack

open CellAutomaton

variable {α : Type} [Alphabet α]

/-- The uniform startup offset of the raw packet stream. -/
def offset (q : ℕ) : ℕ := q

/-- State of the slow right-moving pulse. The active index is one less than
the number of ticks remaining at the current cell. -/
inductive PulseState (q : ℕ)
  | idle
  | active (remaining : Fin (q - 1))
deriving DecidableEq, Inhabited, Fintype

instance (q : ℕ) : Alphabet (PulseState q) where

/-- During a slow right-moving pulse, the active index counts down to zero. -/
def slowPulse (q : ℕ) (hq : 2 ≤ q) :
    CellAutomaton (Option Unit) Bool where
  Q := PulseState q
  δ := fun left center _ =>
    match center with
    | .active remaining =>
        if hzero : remaining.val = 0 then
          .idle
        else
          .active ⟨remaining.val - 1, by omega⟩
    | .idle =>
        match left with
        | .active remaining =>
            if remaining.val = 0 then
              .active ⟨q - 2, by omega⟩
            else
              .idle
        | .idle => .idle
  embed
    | some _ => .active ⟨q - 2, by omega⟩
    | none => .idle
  project
    | .active remaining => decide (remaining.val = q - 2)
    | .idle => false

/-- The unique active countdown state at time `t`. -/
private def slowExpected (q : ℕ) (hq : 2 ≤ q) (t : ℕ) (p : ℤ) :
    PulseState q :=
  if p = (t / (q - 1) : ℕ) then
    .active ⟨q - 2 - t % (q - 1), by
      have hmod := Nat.mod_lt t (by omega : 0 < q - 1)
      omega⟩
  else
    .idle

private theorem slowPulse_state (q : ℕ) (hq : 2 ≤ q)
    (t : ℕ) (p : ℤ) :
    (slowPulse q hq).nextt [()] t p = slowExpected q hq t p := by
  induction t generalizing p with
  | zero =>
      simp only [CellAutomaton.nextt_zero]
      unfold CellAutomaton.embed_config slowExpected
      by_cases hp : p = 0
      · subst p
        simp [word_to_config, slowPulse]
      · have hout : ¬(0 ≤ p ∧ p < (1 : ℤ)) := by omega
        simp [word_to_config, slowPulse, hp, hout]
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      rw [ih (p - 1), ih p, ih (p + 1)]
      have hd : 0 < q - 1 := by omega
      have hmod : t % (q - 1) < q - 1 := Nat.mod_lt t hd
      have hdecomp :
          (q - 1) * (t / (q - 1)) + t % (q - 1) = t :=
        Nat.div_add_mod t (q - 1)
      by_cases hwrap : t % (q - 1) + 1 = q - 1
      · have htime :
          t + 1 = (q - 1) * (t / (q - 1) + 1) := by
          calc
            t + 1 =
                (q - 1) * (t / (q - 1)) +
                  (t % (q - 1) + 1) := by omega
            _ = (q - 1) * (t / (q - 1) + 1) := by
              rw [hwrap, Nat.mul_add, Nat.mul_one]
        have hdiv :
            (t + 1) / (q - 1) = t / (q - 1) + 1 := by
          rw [htime, Nat.mul_comm (q - 1),
            Nat.mul_div_left _ hd]
        have hrem : (t + 1) % (q - 1) = 0 := by
          simp [htime]
        by_cases hpold : p = (t / (q - 1) : ℕ)
        · have hleft :
              p - 1 ≠ (t / (q - 1) : ℕ) := by omega
          have hnew :
              p ≠ ((t + 1) / (q - 1) : ℕ) := by
            rw [hdiv]
            omega
          have hnew' :
              p ≠ (↑(t / (q - 1) + 1) : ℤ) := by
            omega
          simp only [slowPulse, slowExpected]
          simp only [hdiv, hrem]
          rw [if_neg hleft, if_pos hpold, if_neg hnew']
          have hcount : q - 2 - t % (q - 1) = 0 := by omega
          simp [hcount]
        · by_cases hpnew :
            p = (t / (q - 1) : ℕ) + 1
          · have hcenter :
                p ≠ (t / (q - 1) : ℕ) := by omega
            have hleft :
                p - 1 = (t / (q - 1) : ℕ) := by omega
            have hnext :
                p = ((t + 1) / (q - 1) : ℕ) := by
              rw [hdiv]
              exact_mod_cast hpnew
            have hnext' :
                p = (↑(t / (q - 1) + 1) : ℤ) := by
              omega
            simp only [slowPulse, slowExpected]
            simp only [hdiv, hrem]
            rw [if_pos hleft, if_neg hcenter, if_pos hnext']
            have hcount : q - 2 - t % (q - 1) = 0 := by omega
            simp [hcount]
          · have hcenter :
                p ≠ (t / (q - 1) : ℕ) := hpold
            have hleft :
                p - 1 ≠ (t / (q - 1) : ℕ) := by omega
            have hnext :
                p ≠ ((t + 1) / (q - 1) : ℕ) := by
              rw [hdiv]
              exact_mod_cast hpnew
            have hnext' :
                p ≠ (↑(t / (q - 1) + 1) : ℤ) := by
              omega
            simp only [slowPulse, slowExpected]
            simp only [hdiv, hrem]
            rw [if_neg hleft, if_neg hcenter, if_neg hnext']
      · have hnowrap : t % (q - 1) + 1 < q - 1 := by omega
        have htime :
            t + 1 =
              (t % (q - 1) + 1) +
                (q - 1) * (t / (q - 1)) := by
          omega
        have hdiv :
            (t + 1) / (q - 1) = t / (q - 1) := by
          rw [htime, Nat.add_mul_div_left _ _ hd,
            Nat.div_eq_of_lt hnowrap, Nat.zero_add]
        have hrem :
            (t + 1) % (q - 1) = t % (q - 1) + 1 := by
          rw [htime, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hnowrap]
        by_cases hpactive : p = (t / (q - 1) : ℕ)
        · have hleft :
              p - 1 ≠ (t / (q - 1) : ℕ) := by omega
          have hnext :
              p = ((t + 1) / (q - 1) : ℕ) := by
            rw [hdiv]
            exact hpactive
          simp only [slowPulse, slowExpected]
          simp only [hdiv, hrem]
          rw [if_neg hleft, if_pos hpactive, if_pos hpactive]
          have hpositive : q - 2 - t % (q - 1) ≠ 0 := by omega
          change
            (if _ : q - 2 - t % (q - 1) = 0 then
                PulseState.idle
              else
                PulseState.active
                  ⟨q - 2 - t % (q - 1) - 1, by omega⟩) =
              PulseState.active
                ⟨q - 2 - (t % (q - 1) + 1), by omega⟩
          rw [dif_neg hpositive]
          congr 2
        · by_cases hleft :
            p - 1 = (t / (q - 1) : ℕ)
          · simp only [slowPulse, slowExpected]
            simp only [hdiv, hrem]
            rw [if_neg hpactive, if_neg hpactive, if_pos hleft]
            have hpositive : q - 2 - t % (q - 1) ≠ 0 := by omega
            simp [hpositive]
          · simp only [slowPulse, slowExpected]
            simp only [hdiv, hrem]
            rw [if_neg hpactive, if_neg hpactive, if_neg hleft]

/-- Starting from one cell, the pulse fires at natural position `p` exactly
after `(q-1)*p` ticks, and nowhere on the negative half-line. -/
theorem slowPulse_comp (q : ℕ) (hq : 2 ≤ q) (t : ℕ) (p : ℤ) :
    (slowPulse q hq).comp [()] t p =
      decide (0 ≤ p ∧ t = (q - 1) * p.natAbs) := by
  rw [CellAutomaton.comp_apply, slowPulse_state]
  unfold slowExpected slowPulse
  by_cases hp : p = (t / (q - 1) : ℕ)
  · rw [if_pos hp]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hd : 0 < q - 1 := by omega
    have hmod := Nat.mod_lt t hd
    have hdecomp :
        (q - 1) * (t / (q - 1)) + t % (q - 1) = t :=
      Nat.div_add_mod t (q - 1)
    constructor
    · intro hvalue
      constructor
      · rw [hp]
        exact Int.natCast_nonneg _
      · have hpabs : p.natAbs = t / (q - 1) := by
          rw [hp]
          exact Int.natAbs_natCast _
        rw [hpabs]
        omega
    · rintro ⟨hpnonneg, htime⟩
      have hpabs : p.natAbs = t / (q - 1) := by
        rw [hp]
        exact Int.natAbs_natCast _
      rw [hpabs] at htime
      omega
  · rw [if_neg hp]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.false_eq_true, decide_eq_true_eq, false_iff]
    rintro ⟨hpnonneg, htime⟩
    apply hp
    have hd : 0 < q - 1 := by omega
    have hdiv :
        ((q - 1) * p.natAbs) / (q - 1) = p.natAbs := by
      rw [Nat.mul_comm, Nat.mul_div_left _ hd]
    rw [htime, hdiv]
    calc
      p = |p| := (abs_of_nonneg hpnonneg).symm
      _ = (p.natAbs : ℤ) := (Int.natCast_natAbs p).symm

/-- Detect the left edge, wait until the uniform offset, then run the slow
right-moving pulse. -/
def pulse (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] :
    CellAutomaton (Option α) Bool :=
  (CellAutomaton.leftEdgeCA α).composeKSteps
    ((CellAutomaton.idCA (Option Unit)).composeKSteps
      (slowPulse q hq) (q - 1))
    1

theorem pulse_comp (q : ℕ) (hq : 2 ≤ q) (w : Word α) (hw : w ≠ [])
    (t : ℕ) (p : ℤ) :
    (pulse q hq α).comp w t p =
      decide (0 ≤ p ∧ t = offset q + (q - 1) * p.natAbs) := by
  unfold pulse
  rw [CellAutomaton.composeKSteps_comp]
  by_cases ht₁ : 1 ≤ t
  · rw [if_pos ht₁, CellAutomaton.leftEdgeCA.comp_spec w hw]
    rw [CellAutomaton.composeKSteps_comp]
    by_cases htq : q - 1 ≤ t - 1
    · rw [if_pos htq]
      have hinput :
          (CellAutomaton.idCA (Option Unit)).comp
              ⦋word_to_config [()]⦌ (q - 1) =
            word_to_config [()] := by
        rw [CellAutomaton.idCA.comp_spec]
        funext x
        rfl
      rw [hinput, slowPulse_comp]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, offset]
      constructor
      · rintro ⟨hp, htime⟩
        exact ⟨hp, by omega⟩
      · rintro ⟨hp, htime⟩
        exact ⟨hp, by omega⟩
    · rw [if_neg htq]
      change false =
        decide (0 ≤ p ∧ t = offset q + (q - 1) * p.natAbs)
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.false_eq_true, decide_eq_true_eq, false_iff, offset]
      rintro ⟨_, htime⟩
      omega
  · rw [if_neg ht₁]
    change false =
      decide (0 ≤ p ∧ t = offset q + (q - 1) * p.natAbs)
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.false_eq_true, decide_eq_true_eq, false_iff, offset]
    rintro ⟨_, htime⟩
    omega

/-- The left-shifting input stream. -/
def stream (α : Type) [Alphabet α] : CellAutomaton (Option α) (Option α) :=
  ca_trace_id (Option α)

theorem stream_comp (c : Config (Option α)) (t : ℕ) (p : ℤ) :
    (stream α).comp c t p = c (p + t) := by
  change (ca_trace_id (Option α)).nextt c t p = _
  induction t generalizing p with
  | zero => simp
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      change (ca_trace_id (Option α)).nextt c t (p + 1) = _
      rw [ih]
      congr 1
      push_cast
      omega

/-- A `q`-tick history of the left-shifting stream. -/
def history (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] : TraceKx where
  k := q
  α := Option α
  β := Option α
  inst := ⟨by omega⟩
  C_orig := stream α

/-- Read the first `q` history slots as one spatial packet. -/
def readPacket {q : ℕ} {α : Type}
    (values : Fin (q + 1) → Option (Option α)) :
    Fin q → Option α :=
  fun r => (values r.castSucc).getD none

def packetHistory (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] :
    CellAutomaton (Option α) (Fin q → Option α) :=
  (history q hq α).C.map_project readPacket

theorem packetHistory_at (q : ℕ) (hq : 2 ≤ q) (w : Word α) (p : ℕ) :
    (packetHistory q hq α).comp w
        ((q - 1) * p + q) (p : ℤ) =
      SpeedupKx.compress q (word_to_config w) (p : ℤ) := by
  unfold packetHistory
  simp only [comp_of_map_project]
  have hhistory := (history q hq α).spec_at
    (word_to_config w) ((q - 1) * p) (p : ℤ)
  rw [show (q - 1) * p + q = (q - 1) * p + (history q hq α).k by rfl,
    hhistory]
  funext r
  change
    (stream α).comp (word_to_config w)
        ((q - 1) * p + r.val) (p : ℤ) =
      SpeedupKx.compress q (word_to_config w) (p : ℤ) r
  rw [stream_comp]
  unfold SpeedupKx.compress
  congr 1
  push_cast
  have hqcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  rw [hqcast]
  ring

/-- Raw `q`-packet producer. -/
def C (q : ℕ) (hq : 2 ≤ q) (α : Type) [Alphabet α] :
    CellAutomaton (Option α) (Option (Fin q → Option α)) :=
  ((packetHistory q hq α) ⨂ (pulse q hq α)).map_project
    (fun (packet, fire) => if fire then some packet else none)

/-- Complete all-coordinate specification. Packet slots retain genuine input
padding, including packets strictly beyond the finite word. -/
theorem comp_spec (q : ℕ) (hq : 2 ≤ q) (w : Word α) (hw : w ≠ [])
    (t : ℕ) (p : ℤ) :
    (C q hq α).comp w t p =
      if 0 ≤ p ∧ t = offset q + (q - 1) * p.natAbs then
        some (SpeedupKx.compress q (word_to_config w) p)
      else
        none := by
  unfold C
  simp only [comp_of_map_project, ca_zip_comp]
  rw [pulse_comp q hq w hw]
  by_cases hevent :
      0 ≤ p ∧ t = offset q + (q - 1) * p.natAbs
  · rw [if_pos hevent]
    simp [hevent]
    lift p to ℕ using hevent.1
    simp only [Int.natAbs_natCast, offset] at hevent ⊢
    simpa [Nat.add_comm] using packetHistory_at q hq w p
  · rw [if_neg hevent]
    simp [hevent]

/-- Natural-position specialization of `comp_spec`. -/
theorem positive_spec (q : ℕ) (hq : 2 ≤ q) (w : Word α) (hw : w ≠ [])
    (p : ℕ) :
    (C q hq α).comp w (offset q + (q - 1) * p) (p : ℤ) =
      some (SpeedupKx.compress q (word_to_config w) (p : ℤ)) := by
  rw [comp_spec q hq w hw]
  simp

end CellularAutomatas.MarkedPrefix.LT.RawPack
