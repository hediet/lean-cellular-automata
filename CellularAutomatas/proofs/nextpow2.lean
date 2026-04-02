import CellularAutomatas.defs

namespace CellularAutomatas

/-- Compute m = 2^⌈log₂ n⌉, the smallest power of 2 ≥ n. -/
def nextPow2 (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)

end CellularAutomatas
