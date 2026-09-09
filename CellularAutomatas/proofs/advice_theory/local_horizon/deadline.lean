import CellularAutomatas.proofs.advice_theory.marked_prefix.release_envelope

namespace CellularAutomatas.MarkedPrefix

/-- Only releases in the backward cone can affect an arrival. -/
theorem halfLineArrival_le_of_deadline
    (R : ℕ → ℕ) (K deadline : ℕ)
    (hrelease : ∀ p, p ≤ K → R p ≤ deadline) :
    ∀ k p, p + k ≤ K → halfLineArrival R k p ≤ deadline + k := by
  intro k
  induction k with
  | zero =>
      intro p hp
      show R p ≤ deadline + 0
      exact hrelease p hp
  | succ k ih =>
      intro p hp
      cases p with
      | zero =>
          show 1 + max (halfLineArrival R k 0)
            (halfLineArrival R k 1) ≤ deadline + (k + 1)
          have hcenter := ih 0 (by omega)
          have hright := ih 1 (by omega)
          omega
      | succ p =>
          show 1 + max (halfLineArrival R k p)
            (max (halfLineArrival R k (p + 1))
              (halfLineArrival R k (p + 2))) ≤ deadline + (k + 1)
          have hleft := ih p (by omega)
          have hcenter := ih (p + 1) (by omega)
          have hright := ih (p + 2) (by omega)
          omega

/-- Lower pacing and one common deadline suffice; there is no upper bound
on releases outside the final backward cone. -/
theorem halfLineArrival_origin_of_deadline
    (R : ℕ → ℕ) (q κ K : ℕ) (hq : 1 ≤ q)
    (hlower : ∀ p, κ + (q - 1) * p ≤ R p)
    (hupper : ∀ p, p ≤ K → R p ≤ κ + (q - 1) * K) :
    halfLineArrival R K 0 = κ + q * K := by
  have hl := halfLineArrival_lower_bound R q κ hq hlower K 0
  have hu := halfLineArrival_le_of_deadline R K
    (κ + (q - 1) * K) hupper K 0 (by omega)
  have htime : κ + (q - 1) * K + K = κ + q * K := by
    calc
      κ + (q - 1) * K + K = κ + ((q - 1) + 1) * K := by
        simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      _ = κ + q * K := by rw [Nat.sub_add_cancel hq]
  rw [htime] at hu
  simp only [Nat.mul_zero, Nat.add_zero] at hl
  exact le_antisymm hu hl

end CellularAutomatas.MarkedPrefix
