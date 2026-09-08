import CellularAutomatas.proofs.advice_theory.marked_prefix.selector_marker
import CellularAutomatas.proofs.advice_theory.marked_prefix.producer_budget

namespace CellularAutomatas.MarkedPrefix.LT

/-- A fixed power of two large enough to dominate the producer's linear cost.
Using powers of two makes all sufficiently long selected prefixes pack exactly. -/
def packingFactor (c : ℕ) : ℕ := 2 ^ (c + 1)

theorem packingFactor_large (c : ℕ) : c + 2 ≤ packingFactor c := by
  have := Nat.lt_two_pow_self (n := c + 1)
  dsimp [packingFactor]
  omega

theorem dyadicSelector_dvd {s n : ℕ} (hn : 2 * 2 ^ s ≤ n) :
    2 ^ s ∣ dyadicSelector n := by
  have hpow : 2 ^ (s + 1) ≤ n := by
    simpa only [pow_succ, Nat.mul_comm] using hn
  have hlog : s + 1 ≤ Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le Nat.one_lt_two hpow
  have hn2 : 2 ≤ n := by
    have := Nat.two_pow_pos s
    omega
  rw [dyadicSelector_eq_pow hn2]
  exact pow_dvd_pow 2 (by omega : s ≤ Nat.log2 n - 1)

theorem packingFactor_dvd {c n : ℕ} (hn : 2 * packingFactor c ≤ n) :
    packingFactor c ∣ dyadicSelector n :=
  dyadicSelector_dvd hn

/-- With exact packing, the ceiling budget is simply a linear number of
physical producer steps per packed cell. -/
theorem producerBudget_of_dvd {q L : ℕ} (c : ℕ)
    (hq : 0 < q) (hL : q ∣ L) :
    producerBudget q c 0 L = (q - 1 + c) * (L / q) := by
  have hmultiple : q ∣ (q - 1 + c) * L := dvd_mul_of_dvd_right hL _
  rw [producerBudget, Nat.add_zero, Nat.add_div_of_dvd_right hmultiple,
    Nat.div_eq_of_lt (by omega : q - 1 < q), Nat.add_zero,
    Nat.mul_div_assoc _ hL]

/-- The same finite cutoff ensures exact prefix packing and enough consumer
slack. No independent synchronization barrier is charged here. -/
theorem packed_cost_le_catchup (c n : ℕ)
    (hn : 2 * packingFactor c ≤ n) :
    (packingFactor c - 1 + c) * (dyadicSelector n / packingFactor c) ≤
      (packingFactor c - 1) * ((n - 1) / packingFactor c + 1) := by
  have hq := packingFactor_large c
  rw [← producerBudget_of_dvd c (by omega : 0 < packingFactor c)
    (packingFactor_dvd hn)]
  apply producerBudget_le_catchup (packingFactor c) c 0 (dyadicSelector n) n
  · exact hq
  · exact dyadicSelector_le_half n
  · simp only [Nat.mul_zero, Nat.add_zero]
    omega

end CellularAutomatas.MarkedPrefix.LT
