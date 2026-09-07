import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace CellularAutomatas.MarkedPrefixClock

/-- The generation-zero release time at position `p`. -/
def release (κ b p : ℕ) : ℕ :=
  κ + max (2 * p) (b - p)

/-- The arrival time of generation `k` at position `p`. -/
def arrival (κ b p k : ℕ) : ℕ :=
  κ + max (2 * p + 3 * k) (b + k - (p - k))

/-- Generation zero is exactly the original release schedule. -/
theorem arrival_zero (κ b p : ℕ) :
    arrival κ b p 0 = release κ b p := by
  simp [arrival, release]

/-- At the origin the truncated spatial subtraction disappears. -/
theorem arrival_origin (κ b k : ℕ) :
    arrival κ b 0 k = κ + max (3 * k) (b + k) := by
  simp [arrival]

/-- The origin has only itself and its right neighbor as predecessors. -/
theorem arrival_boundary_succ (κ b k : ℕ) :
    arrival κ b 0 (k + 1) =
      1 + max (arrival κ b 0 k) (arrival κ b 1 k) := by
  simp only [arrival]
  omega

/-- Among three pairs, increasing left entries and decreasing right entries
leave only the last left entry and the first right entry as candidates. -/
lemma max_three_pairs_of_monotone (κ a₀ b₀ a₁ b₁ a₂ b₂ : ℕ)
    (ha₀ : a₀ ≤ a₂) (ha₁ : a₁ ≤ a₂)
    (hb₁ : b₁ ≤ b₀) (hb₂ : b₂ ≤ b₀) :
    max (κ + max a₀ b₀)
        (max (κ + max a₁ b₁) (κ + max a₂ b₂)) =
      κ + max a₂ b₀ := by
  apply le_antisymm
  · apply max_le
    · exact Nat.add_le_add_left
        (max_le (le_trans ha₀ (Nat.le_max_left _ _)) (Nat.le_max_right _ _)) κ
    · apply max_le
      · exact Nat.add_le_add_left
          (max_le (le_trans ha₁ (Nat.le_max_left _ _))
            (le_trans hb₁ (Nat.le_max_right _ _))) κ
      · exact Nat.add_le_add_left
          (max_le (Nat.le_max_left _ _)
            (le_trans hb₂ (Nat.le_max_right _ _))) κ
  · rcases le_total a₂ b₀ with ha₂ | hb₀
    · rw [max_eq_right ha₂]
      exact le_trans (Nat.add_le_add_left (Nat.le_max_right a₀ b₀) κ)
        (Nat.le_max_left _ _)
    · rw [max_eq_left hb₀]
      exact le_trans (Nat.add_le_add_left (Nat.le_max_left a₂ b₂) κ)
        (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- An interior cell has all three radius-one predecessors. -/
theorem arrival_interior_succ (κ b p k : ℕ) :
    arrival κ b (p + 1) (k + 1) =
      1 + max (arrival κ b p k)
        (max (arrival κ b (p + 1) k) (arrival κ b (p + 2) k)) := by
  unfold arrival
  rw [max_three_pairs_of_monotone]
  · omega
  · omega
  · omega
  · omega
  omega

/-- Every new generation arrives strictly later at a fixed position. -/
theorem arrival_generation_strict (κ b p k : ℕ) :
    arrival κ b p k < arrival κ b p (k + 1) := by
  simp only [arrival]
  omega

/-- Generation `k` cannot reach the origin before its intrinsic `3*k` delay. -/
theorem arrival_origin_lower_bound (κ b k : ℕ) :
    κ + 3 * k ≤ arrival κ b 0 k := by
  rw [arrival_origin]
  exact Nat.add_le_add_left (Nat.le_max_left _ _) κ

/-- Once `2*k` covers the initial backlog, the origin runs at exact rate three. -/
theorem arrival_origin_of_caught_up (κ b k : ℕ) (hcatch : b ≤ 2 * k) :
    arrival κ b 0 k = κ + 3 * k := by
  rw [arrival_origin]
  rw [max_eq_left]
  omega

/-- The final marker is within the cone of generation `(n - 1) / 3 + 1`. -/
theorem final_marker_bound (n L : ℕ) (hn : 2 ≤ n) (hL : L ≤ n / 2) :
    L - 1 ≤ 2 * ((n - 1) / 3 + 1) := by
  omega

/-- Quotient and remainder modulo three decode the exact delayed time. -/
theorem exact_decoding_identity (κ N : ℕ) :
    κ + 3 * (N / 3 + 1) + N % 3 = N + κ + 3 := by
  omega

/-- The constant speedup side condition holds for every nonempty input. -/
theorem constant_speedup_side_condition (n d : ℕ) (hn : 1 ≤ n) :
    (n - 1) + d < (d + 1) * n := by
  have hd : d ≤ d * n := by
    simpa using Nat.mul_le_mul_left d hn
  calc
    (n - 1) + d < n + d := by omega
    _ ≤ n + d * n := Nat.add_le_add_left hd n
    _ = (d + 1) * n := by simp [Nat.add_mul, Nat.add_comm]

end CellularAutomatas.MarkedPrefixClock
