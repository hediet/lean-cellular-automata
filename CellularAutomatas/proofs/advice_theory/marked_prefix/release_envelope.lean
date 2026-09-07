import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace CellularAutomatas.MarkedPrefix

/-- Arrival times generated from an arbitrary release schedule on the
nonnegative half-line. The boundary has two predecessors and interior
positions have the usual radius-one three predecessors. -/
def halfLineArrival (R : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, p => R p
  | k + 1, 0 =>
      1 + max (halfLineArrival R k 0) (halfLineArrival R k 1)
  | k + 1, p + 1 =>
      1 + max (halfLineArrival R k p)
        (max (halfLineArrival R k (p + 1)) (halfLineArrival R k (p + 2)))

/-- The affine lower release bound propagates by always selecting the right
neighbor in the recurrence. -/
theorem halfLineArrival_lower_bound
    (R : ℕ → ℕ) (q κ : ℕ) (hq : 1 ≤ q)
    (hR : ∀ p, κ + (q - 1) * p ≤ R p) :
    ∀ k p, κ + (q - 1) * p + q * k ≤ halfLineArrival R k p := by
  intro k
  induction k with
  | zero =>
      intro p
      simpa [halfLineArrival] using hR p
  | succ k ih =>
      intro p
      cases p with
      | zero =>
          rw [halfLineArrival]
          calc
            κ + (q - 1) * 0 + q * (k + 1) =
                1 + (κ + (q - 1) * 1 + q * k) := by
                  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.mul_add]
                  omega
            _ ≤ 1 + halfLineArrival R k 1 :=
              Nat.add_le_add_left (ih 1) 1
            _ ≤ 1 + max (halfLineArrival R k 0) (halfLineArrival R k 1) :=
              Nat.add_le_add_left (Nat.le_max_right _ _) 1
      | succ p =>
          rw [halfLineArrival]
          calc
            κ + (q - 1) * (p + 1) + q * (k + 1) =
                1 + (κ + (q - 1) * (p + 2) + q * k) := by
                  simp only [Nat.mul_add, Nat.mul_one]
                  omega
            _ ≤ 1 + halfLineArrival R k (p + 2) :=
              Nat.add_le_add_left (ih (p + 2)) 1
            _ ≤ 1 + max (halfLineArrival R k p)
                  (max (halfLineArrival R k (p + 1))
                    (halfLineArrival R k (p + 2))) := by
              apply Nat.add_le_add_left
              exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- The upper release envelope is preserved by all predecessors of both the
boundary and interior recurrence rules. -/
theorem halfLineArrival_upper_bound
    (R : ℕ → ℕ) (q κ D : ℕ) (hq : 1 ≤ q)
    (hR : ∀ p, R p ≤ κ + max ((q - 1) * p) D) :
    ∀ k p,
      halfLineArrival R k p ≤
        κ + max ((q - 1) * p + q * k) (D + k) := by
  intro k
  induction k with
  | zero =>
      intro p
      simpa [halfLineArrival] using hR p
  | succ k ih =>
      intro p
      cases p with
      | zero =>
          rw [halfLineArrival]
          let B := κ + max ((q - 1) * 1 + q * k) (D + k)
          have hzero : halfLineArrival R k 0 ≤ B := by
            apply le_trans (ih 0)
            dsimp [B]
            simp only [Nat.zero_add, Nat.mul_one]
            omega
          have hone : halfLineArrival R k 1 ≤ B := by
            simpa [B] using ih 1
          calc
            1 + max (halfLineArrival R k 0) (halfLineArrival R k 1)
                ≤ 1 + B := Nat.add_le_add_left (max_le hzero hone) 1
            _ = κ + max ((q - 1) * 0 + q * (k + 1)) (D + (k + 1)) := by
                  dsimp [B]
                  simp only [Nat.zero_add, Nat.mul_one, Nat.mul_add]
                  omega
      | succ p =>
          rw [halfLineArrival]
          let B := κ + max ((q - 1) * (p + 2) + q * k) (D + k)
          have hleft : halfLineArrival R k p ≤ B := by
            apply le_trans (ih p)
            dsimp [B]
            simp only [Nat.mul_add]
            omega
          have hcenter : halfLineArrival R k (p + 1) ≤ B := by
            apply le_trans (ih (p + 1))
            dsimp [B]
            simp only [Nat.mul_add, Nat.mul_one]
            omega
          have hright : halfLineArrival R k (p + 2) ≤ B := by
            simpa [B] using ih (p + 2)
          calc
            1 + max (halfLineArrival R k p)
                  (max (halfLineArrival R k (p + 1))
                    (halfLineArrival R k (p + 2)))
                ≤ 1 + B :=
                  Nat.add_le_add_left
                    (max_le hleft (max_le hcenter hright)) 1
            _ = κ + max ((q - 1) * (p + 1) + q * (k + 1))
                  (D + (k + 1)) := by
                  dsimp [B]
                  simp only [Nat.mul_add, Nat.mul_one]
                  omega

/-- A release schedule inside the initial affine envelope remains inside the
corresponding space-time envelope at every generation and position. -/
theorem halfLineArrival_bounds
    (R : ℕ → ℕ) (q κ D : ℕ) (hq : 1 ≤ q)
    (hR : ∀ p,
      κ + (q - 1) * p ≤ R p ∧
        R p ≤ κ + max ((q - 1) * p) D) :
    ∀ k p,
      κ + (q - 1) * p + q * k ≤ halfLineArrival R k p ∧
        halfLineArrival R k p ≤
          κ + max ((q - 1) * p + q * k) (D + k) := by
  intro k p
  exact ⟨halfLineArrival_lower_bound R q κ hq (fun i => (hR i).1) k p,
    halfLineArrival_upper_bound R q κ D hq (fun i => (hR i).2) k p⟩

/-- Once the growing affine cone covers `D`, the origin arrival time is
exactly the intrinsic delay `κ + q*k`. -/
theorem halfLineArrival_origin_of_caught_up
    (R : ℕ → ℕ) (q κ D k : ℕ) (hq : 1 ≤ q)
    (hR : ∀ p,
      κ + (q - 1) * p ≤ R p ∧
        R p ≤ κ + max ((q - 1) * p) D)
    (hcatch : D ≤ (q - 1) * k) :
    halfLineArrival R k 0 = κ + q * k := by
  have hbounds := halfLineArrival_bounds R q κ D hq hR k 0
  have hDk : D + k ≤ q * k := by
    calc
      D + k ≤ (q - 1) * k + k := Nat.add_le_add_right hcatch k
      _ = (q - 1) * k + 1 * k := by simp
      _ = ((q - 1) + 1) * k := (Nat.add_mul _ _ _).symm
      _ = q * k := by rw [Nat.sub_add_cancel hq]
  apply le_antisymm
  · calc
      halfLineArrival R k 0 ≤
          κ + max ((q - 1) * 0 + q * k) (D + k) := hbounds.2
      _ = κ + q * k := by
        simp only [Nat.mul_zero, Nat.zero_add]
        rw [max_eq_left hDk]
  · simpa using hbounds.1

end CellularAutomatas.MarkedPrefix
