import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.exp_middle_two_stage
import CellularAutomatas.proofs.lx_rt_implies_rt

/-!
# Tests for xPrefixAdvice Two-Stage Proof

## Definitions

1. `mark_pow2 n`: marks positions where i+1 is a power of 2
2. `g w`: FST-independent function - position i is true iff ≥3 marks in w[i..n-2]
3. `threshold n`: position i is true iff i < nextPow2(n)/8

## Plan

1. Define `g` (pure function, no FST)
2. Define `boundary_FST`
3. Test: `boundary_FST.scanr = g`
4. Test: `g (mark_pow2 n) = threshold n`

If tests pass, then we prove both equalities formally.
-/

namespace CellularAutomatas

/-! ## Pure Function Definitions -/

/-- Marks where i+1 is a power of 2. -/
def mark_pow2_test (n : ℕ) : List Bool :=
  (List.range n).map (fun i => isPowerOfTwo (i + 1))

/-- FST-independent function: position i is true iff ≥3 marks in w[i..n-2] (excluding last). -/
def g (w : List Bool) : List Bool :=
  (List.range w.length).map fun i =>
    (w.drop i).dropLast.count true ≥ 3

/-- Target: position i is true iff i < nextPow2(n)/8. -/
def threshold_test (n : ℕ) : List Bool :=
  (List.range n).map (fun i => decide (i < nextPow2 n / 8))

/-! ## FST Definition -/

inductive TestState
  | init | s2 | s1 | s0 | fill
deriving DecidableEq, Repr, Fintype, Inhabited

def test_FST : FiniteStateTransducer Bool Bool := {
  Q := TestState
  δ := fun state input =>
    match state, input with
    | .init, _      => .s2
    | .s2,   true   => .s1
    | .s1,   true   => .s0
    | .s0,   true   => .fill
    | .fill, _      => .fill
    | s,     false  => s
  q0 := .init
  f := fun state => state == .fill
}

/-! ## Tests -/

-- Test mark_pow2
#eval mark_pow2_test 0   -- []
#eval mark_pow2_test 1   -- [true]  (pos 0: 1 = 2^0)
#eval mark_pow2_test 2   -- [true, true]  (pos 0,1: 1=2^0, 2=2^1)
#eval mark_pow2_test 4   -- [T, T, F, T]  (pos 0,1,3)
#eval mark_pow2_test 8   -- [T, T, F, T, F, F, F, T]  (pos 0,1,3,7)
#eval mark_pow2_test 9   -- [T, T, F, T, F, F, F, T, F]
#eval mark_pow2_test 16  -- [T, T, F, T, F, F, F, T, F, F, F, F, F, F, F, T]

-- Test threshold
#eval threshold_test 0   -- []
#eval threshold_test 1   -- [F] (nextPow2(1)=1, /8=0)
#eval threshold_test 2   -- [F, F]
#eval threshold_test 4   -- [F, F, F, F]
#eval threshold_test 8   -- [T, F, F, F, F, F, F, F] (nextPow2(8)=8, /8=1)
#eval threshold_test 9   -- [T, T, F, F, F, F, F, F, F] (nextPow2(9)=16, /8=2)
#eval threshold_test 16  -- [T, T, F, ...] (nextPow2(16)=16, /8=2)

-- Test g on mark_pow2
#eval g (mark_pow2_test 0)   -- []
#eval g (mark_pow2_test 1)   -- [F] (drop 0, dropLast = [], count = 0 < 3)
#eval g (mark_pow2_test 2)   -- [F, F]
#eval g (mark_pow2_test 4)   -- [F, F, F, F]
#eval g (mark_pow2_test 8)   -- Should be [T, F, F, F, F, F, F, F]
#eval g (mark_pow2_test 9)   -- Should be [T, T, F, F, F, F, F, F, F]
#eval g (mark_pow2_test 16)  -- Should be [T, T, F, ...]

-- Test FST on mark_pow2
#eval test_FST.scanr (mark_pow2_test 0)
#eval test_FST.scanr (mark_pow2_test 1)
#eval test_FST.scanr (mark_pow2_test 2)
#eval test_FST.scanr (mark_pow2_test 4)
#eval test_FST.scanr (mark_pow2_test 8)
#eval test_FST.scanr (mark_pow2_test 9)
#eval test_FST.scanr (mark_pow2_test 16)

/-! ## Verification -/

-- Check g = FST.scanr for small cases
#eval g (mark_pow2_test 8) == test_FST.scanr (mark_pow2_test 8)
#eval g (mark_pow2_test 9) == test_FST.scanr (mark_pow2_test 9)
#eval g (mark_pow2_test 16) == test_FST.scanr (mark_pow2_test 16)

-- Check g ∘ mark_pow2 = threshold for small cases
#eval g (mark_pow2_test 0) == threshold_test 0
#eval g (mark_pow2_test 1) == threshold_test 1
#eval g (mark_pow2_test 2) == threshold_test 2
#eval g (mark_pow2_test 4) == threshold_test 4
#eval g (mark_pow2_test 8) == threshold_test 8
#eval g (mark_pow2_test 9) == threshold_test 9
#eval g (mark_pow2_test 16) == threshold_test 16

-- Batch test
#eval (List.range 32).all fun n => g (mark_pow2_test n) == threshold_test n
#eval (List.range 32).all fun n => test_FST.scanr (mark_pow2_test n) == g (mark_pow2_test n)

end CellularAutomatas
