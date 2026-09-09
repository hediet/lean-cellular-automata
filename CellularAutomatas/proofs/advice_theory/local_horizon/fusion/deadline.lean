import CellularAutomatas.proofs.advice_theory.local_horizon.defs

namespace CellularAutomatas.LocalHorizon.Fusion

/-- The last occupied packet covers the last input cell, including for an
empty input. -/
theorem length_le_packetCount_mul (q n : ℕ) (hq : 0 < q) :
    n ≤ q * packetCount q n := by
  by_cases hn : n = 0
  · show n ≤ q * packetCount q n
    simp [hn]
  · show n ≤ q * packetCount q n
    rw [packetCount_of_pos q n (by omega)]
    have hdiv := (Nat.div_lt_iff_lt_mul hq).mp
      (Nat.lt_succ_self ((n - 1) / q))
    have hpred : n - 1 + 1 = n := by omega
    nlinarith

/-- Any collection of packets covering the input bounds its packet count. -/
theorem packetCount_le_of_length_le_mul (q n k : ℕ) (hq : 0 < q)
    (hcover : n ≤ q * k) : packetCount q n ≤ k := by
  by_cases hn : n = 0
  · show packetCount q n ≤ k
    simp [packetCount, hn]
  · show packetCount q n ≤ k
    rw [packetCount_of_pos q n (by omega)]
    have hpred : n - 1 + 1 = n := by omega
    have hlast : n - 1 < k * q := by nlinarith
    have hdiv := (Nat.div_lt_iff_lt_mul hq).mpr hlast
    omega

theorem packetCount_first_le (q₁ q₂ n : ℕ)
    (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) :
    packetCount q₁ n ≤ q₂ * packetCount (q₁ * q₂) n := by
  apply packetCount_le_of_length_le_mul q₁ n _ (by omega)
  show n ≤ q₁ * (q₂ * packetCount (q₁ * q₂) n)
  simpa only [Nat.mul_assoc] using
    length_le_packetCount_mul (q₁ * q₂) n (by positivity)

theorem packetCount_second_le (q₁ q₂ n : ℕ)
    (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) :
    packetCount q₂ n ≤ q₁ * packetCount (q₁ * q₂) n := by
  show packetCount q₂ n ≤ q₁ * packetCount (q₁ * q₂) n
  simpa only [Nat.mul_comm q₂ q₁] using
    packetCount_first_le q₂ q₁ n hq₂ hq₁

/-- Every lane of an occupied fused packet is released within `q₁ * d`.
The constant `c = κ₂` avoids rounding or division in the simulation depth. -/
theorem second_stage_release_bound (q₁ q₂ κ₂ n p : ℕ)
    (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    (hp : p < packetCount (q₁ * q₂) n) (s : Fin q₁) :
    κ₂ + (q₂ - 1) * max (packetCount q₂ n) (q₁ * p + s.val) ≤
      q₁ * ((q₂ - 1) * packetCount (q₁ * q₂) n + κ₂) := by
  have hlane : q₁ * p + s.val ≤ q₁ * packetCount (q₁ * q₂) n := by
    have hs := s.isLt
    nlinarith
  have hmax : max (packetCount q₂ n) (q₁ * p + s.val) ≤
      q₁ * packetCount (q₁ * q₂) n :=
    max_le (packetCount_second_le q₁ q₂ n hq₁ hq₂) hlane
  calc
    κ₂ + (q₂ - 1) * max (packetCount q₂ n) (q₁ * p + s.val) ≤
        κ₂ + (q₂ - 1) * (q₁ * packetCount (q₁ * q₂) n) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hmax) _
    _ ≤ q₁ * ((q₂ - 1) * packetCount (q₁ * q₂) n + κ₂) := by
      have hconstant : κ₂ ≤ q₁ * κ₂ := by nlinarith
      nlinarith

/-- The right edge of the backward cone remains strictly before `q₂*K+c`.
This is the one-cell slack supplied by `p < K`. -/
theorem cone_right_edge_lt (q₂ K c p : ℕ) (hq₂ : 2 ≤ q₂)
    (hp : p < K) :
    p + ((q₂ - 1) * K + c) < q₂ * K + c := by
  have hwidth : q₂ - 1 + 1 = q₂ := by omega
  nlinarith

theorem cone_position_lt (q₂ K c p : ℕ) (hq₂ : 2 ≤ q₂)
    (hp : p < K) (z : ℤ) (hz : 0 ≤ z)
    (hcone : |z - (p : ℤ)| ≤ (↑((q₂ - 1) * K + c) : ℤ)) :
    z.toNat < q₂ * K + c := by
  have hright := (abs_le.mp hcone).2
  have hedge := cone_right_edge_lt q₂ K c p hq₂ hp
  have hzcast : (↑z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
  omega

/-- The normalized first-stage release bound is uniform on the nonnegative
part of the full-line backward cone. -/
theorem cone_packet_bound (q₁ q₂ c n p : ℕ)
    (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    (hp : p < packetCount (q₁ * q₂) n) (z : ℤ) (hz : 0 ≤ z)
    (hcone : |z - (p : ℤ)| ≤
      (↑((q₂ - 1) * packetCount (q₁ * q₂) n + c) : ℤ)) :
    max (packetCount q₁ n) z.toNat ≤ q₂ * packetCount (q₁ * q₂) n + c := by
  apply max_le
  · show packetCount q₁ n ≤ q₂ * packetCount (q₁ * q₂) n + c
    exact le_trans (packetCount_first_le q₁ q₂ n hq₁ hq₂) (Nat.le_add_right _ _)
  · show z.toNat ≤ q₂ * packetCount (q₁ * q₂) n + c
    exact Nat.le_of_lt (cone_position_lt q₂ _ c p hq₂ hp z hz hcone)

/-- Negative positions are ready at time zero; every other release in the
full-line cone is bounded by the same first-stage deadline `T`. -/
theorem release_cone_bound (q₁ q₂ κ₁ c n p : ℕ)
    (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    (hp : p < packetCount (q₁ * q₂) n) (R : ℤ → ℕ)
    (hR : ∀ z, 0 ≤ z →
      R z ≤ κ₁ + (q₁ - 1) * max (packetCount q₁ n) z.toNat)
    (hnegative : ∀ z, z < 0 → R z = 0) :
    ∀ z, |z - (p : ℤ)| ≤
      (↑((q₂ - 1) * packetCount (q₁ * q₂) n + c) : ℤ) →
      R z ≤ κ₁ + (q₁ - 1) * (q₂ * packetCount (q₁ * q₂) n + c) := by
  intro z hcone
  by_cases hz : 0 ≤ z
  · show R z ≤ κ₁ + (q₁ - 1) * (q₂ * packetCount (q₁ * q₂) n + c)
    calc
      R z ≤ κ₁ + (q₁ - 1) * max (packetCount q₁ n) z.toNat := hR z hz
      _ ≤ κ₁ + (q₁ - 1) * (q₂ * packetCount (q₁ * q₂) n + c) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _
          (cone_packet_bound q₁ q₂ c n p hq₁ hq₂ hp z hz hcone)) _
  · show R z ≤ κ₁ + (q₁ - 1) * (q₂ * packetCount (q₁ * q₂) n + c)
    rw [hnegative z (by omega)]
    exact Nat.zero_le _

/-- Direct consumption and emission at the current time give `T+d`, with
no extra handoff tick. Its slope is exactly the fused width minus one. -/
theorem deadline_eq (q₁ q₂ κ₁ c K : ℕ)
    (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) :
    (κ₁ + (q₁ - 1) * (q₂ * K + c)) + ((q₂ - 1) * K + c) =
      (κ₁ + q₁ * c) + (q₁ * q₂ - 1) * K := by
  have hfirst : q₁ - 1 + 1 = q₁ := by omega
  have hsecond : q₂ - 1 + 1 = q₂ := by omega
  have hproduct : q₁ * q₂ - 1 + 1 = q₁ * q₂ := by
    have : 1 ≤ q₁ * q₂ := by nlinarith
    omega
  nlinarith [congrArg (fun width => width * c) hfirst,
    congrArg (fun width => width * (q₂ * K)) hfirst,
    congrArg (fun width => width * K) hsecond,
    congrArg (fun width => width * K) hproduct]

/-- The startup absorbs both the fused width and the constant part of the
deadline, without changing its required linear coefficient. -/
def startup (q₁ q₂ κ₁ c : ℕ) : ℕ :=
  max (q₁ * q₂) (κ₁ + q₁ * c)

theorem width_le_startup (q₁ q₂ κ₁ c : ℕ) :
    q₁ * q₂ ≤ startup q₁ q₂ κ₁ c :=
  le_max_left _ _

theorem deadline_le (q₁ q₂ κ₁ c K : ℕ)
    (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) :
    (κ₁ + (q₁ - 1) * (q₂ * K + c)) + ((q₂ - 1) * K + c) ≤
      startup q₁ q₂ κ₁ c + (q₁ * q₂ - 1) * K := by
  calc
    (κ₁ + (q₁ - 1) * (q₂ * K + c)) + ((q₂ - 1) * K + c) =
        (κ₁ + q₁ * c) + (q₁ * q₂ - 1) * K :=
      deadline_eq q₁ q₂ κ₁ c K hq₁ hq₂
    _ ≤ startup q₁ q₂ κ₁ c + (q₁ * q₂ - 1) * K :=
      Nat.add_le_add_right (le_max_right _ _) _

end CellularAutomatas.LocalHorizon.Fusion
