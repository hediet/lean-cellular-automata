import CellularAutomatas.proofs.advice_theory.marked_prefix.release_envelope
import Mathlib.Tactic.Ring

/-!
# Conservative producer budget

This file contains only the arithmetic needed to absorb a packed linear
latency and a fixed overhead into the half-line release envelope.
-/

namespace CellularAutomatas.MarkedPrefix

/-- Ceiling of the packed linear latency, followed by a fixed overhead. -/
def producerBudget (q c d L : ℕ) : ℕ :=
  ((q - 1 + c) * L + (q - 1)) / q + d

/-- If the packing factor strictly dominates the linear coefficient, then on
sufficiently long inputs the producer budget is caught by the affine cone. -/
theorem producerBudget_le_catchup
    (q c d L n : ℕ)
    (hqc : c + 2 ≤ q)
    (hL : L ≤ n / 2)
    (hcutoff : 2 * ((q - 1) + q * d) ≤ n) :
    producerBudget q c d L ≤
      (q - 1) * ((n - 1) / q + 1) := by
  have hq2 : 2 ≤ q := by omega
  have hqpos : 0 < q := by omega
  have h2L : 2 * L ≤ n := by
    have := (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hL
    omega
  let A := (q - 1 + c) * L + (q - 1)
  have hdiv : q * (A / q) ≤ A := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self A q
  have hbudget :
      q * producerBudget q c d L ≤ A + q * d := by
    calc
      q * producerBudget q c d L =
          q * (A / q) + q * d := by
            simp only [producerBudget, A, Nat.mul_add]
      _ ≤ A + q * d := Nat.add_le_add_right hdiv _
  have hcoefficient : q - 1 + c + 1 ≤ 2 * (q - 1) := by
    omega
  have hlinear :
      2 * ((q - 1 + c) * L) ≤ (q - 1 + c) * n := by
    calc
      2 * ((q - 1 + c) * L) = (q - 1 + c) * (2 * L) := by ring
      _ ≤ (q - 1 + c) * n := Nat.mul_le_mul_left _ h2L
  have htwice :
      2 * (A + q * d) ≤ 2 * ((q - 1) * n) := by
    calc
      2 * (A + q * d) =
          2 * ((q - 1 + c) * L) +
            2 * ((q - 1) + q * d) := by
              simp only [A]
              ring
      _ ≤ (q - 1 + c) * n + n :=
        Nat.add_le_add hlinear hcutoff
      _ = (q - 1 + c + 1) * n := by ring
      _ ≤ (2 * (q - 1)) * n :=
        Nat.mul_le_mul_right n hcoefficient
      _ = 2 * ((q - 1) * n) := by ring
  have hpacked : q * producerBudget q c d L ≤ (q - 1) * n := by
    exact le_trans hbudget
      (Nat.le_of_mul_le_mul_left htwice (by omega : 0 < 2))
  let k := (n - 1) / q + 1
  have hn2 : 2 ≤ n := by
    omega
  have hmod : (n - 1) % q < q := Nat.mod_lt _ hqpos
  have hdecomp :
      q * ((n - 1) / q) + (n - 1) % q = n - 1 :=
    Nat.div_add_mod (n - 1) q
  have hn_le_qk : n ≤ q * k := by
    dsimp [k]
    rw [Nat.mul_add]
    omega
  have hcone :
      (q - 1) * n ≤ q * ((q - 1) * k) := by
    calc
      (q - 1) * n ≤ (q - 1) * (q * k) :=
        Nat.mul_le_mul_left _ hn_le_qk
      _ = q * ((q - 1) * k) := by ring
  apply (Nat.mul_le_mul_left_iff hqpos).mp
  calc
    q * producerBudget q c d L ≤ (q - 1) * n := hpacked
    _ ≤ q * ((q - 1) * k) := hcone

/-- Under the matching release envelope, the caught-up generation reaches the
origin at exactly its intrinsic affine time. This does not assert that any
particular producer realizes the assumed release schedule. -/
theorem halfLineArrival_origin_of_producerBudget
    (R : ℕ → ℕ) (q c d L n κ : ℕ)
    (hqc : c + 2 ≤ q)
    (hL : L ≤ n / 2)
    (hcutoff : 2 * ((q - 1) + q * d) ≤ n)
    (hR : ∀ p,
      κ + (q - 1) * p ≤ R p ∧
        R p ≤ κ + max ((q - 1) * p) (producerBudget q c d L)) :
    halfLineArrival R ((n - 1) / q + 1) 0 =
      κ + q * ((n - 1) / q + 1) := by
  apply halfLineArrival_origin_of_caught_up
      R q κ (producerBudget q c d L) ((n - 1) / q + 1)
  · omega
  · exact hR
  · exact producerBudget_le_catchup q c d L n hqc hL hcutoff

end CellularAutomatas.MarkedPrefix
