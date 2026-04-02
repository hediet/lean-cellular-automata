# xPrefixAdvice is Two-Stage: Proof Design

## Goal

Prove that `xPrefixAdvice x k` is a two-stage advice (for k = 8).

A two-stage advice has the form `M.scanr ∘ C.trace_rt` where:
- `C` is a CA_RT transducer (processes left→right in real-time)
- `M` is a finite-state transducer (processes right→left)

## Key Definitions

### `nextPow2` — smallest power of 2 ≥ n

2^⌈log₂ n⌉

```lean
def nextPow2 (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)
```

Examples:
| n  | nextPow2(n) |
|----|-------------|
| 1  | 1           |
| 2  | 2           |
| 3  | 4           |
| 4  | 4           |
| 5  | 8           |
| 8  | 8           |
| 9  | 16          |

### `isPowerOfTwo` — checks if n is a power of 2

```lean
def isPowerOfTwo (n : ℕ) : Bool := n > 0 && n = 2 ^ (Nat.log2 n)
```

True for: 1, 2, 4, 8, 16, 32, ...

### `threshold_v` — the target function (simplified from xPrefixAdvice for k=8)

```lean
def threshold_v (n : ℕ) : List Bool :=
  (List.range n).map (fun i => decide (i < nextPow2 n / 8))
```

Position i is `true` iff `i < nextPow2(n) / 8`.

Examples:
| n  | nextPow2(n)/8 | threshold_v n                     |
|----|---------------|-----------------------------------|
| 1  | 0             | [F]                               |
| 4  | 0             | [F,F,F,F]                         |
| 8  | 1             | [T,F,F,F,F,F,F,F]                 |
| 9  | 2             | [T,T,F,F,F,F,F,F,F]               |
| 16 | 2             | [T,T,F,F,F,F,F,F,F,F,F,F,F,F,F,F] |

## Decomposition Strategy

### 1. CA Stage: `mark_pow2`

The CA marks positions where `i+1` is a power of 2:

```lean
def mark_pow2_v (n : ℕ) : List Bool :=
  (List.range n).map (fun i => isPowerOfTwo (i + 1))
```

This marks positions 0, 1, 3, 7, 15, 31, ... (i.e., `2^k - 1` for all valid k).

Examples:
| n  | mark_pow2_v n                      | Marked positions |
|----|------------------------------------|------------------|
| 1  | [T]                                | {0}              |
| 4  | [T,T,F,T]                          | {0,1,3}          |
| 8  | [T,T,F,T,F,F,F,T]                  | {0,1,3,7}        |
| 9  | [T,T,F,T,F,F,F,T,F]                | {0,1,3,7}        |
| 16 | [T,T,F,T,F,F,F,T,F,F,F,F,F,F,F,T]  | {0,1,3,7,15}     |

### 2. FST Stage: `bFST`

The FST scans right-to-left, counting marks (excluding the last position):

```lean
inductive BState
  | init   -- Initial state (at rightmost position)
  | s2     -- Seen 0 marks after skipping last
  | s1     -- Seen 1 mark
  | s0     -- Seen 2 marks
  | fill   -- Seen 3+ marks, output true

def bFST : FiniteStateTransducer Bool Bool := {
  Q := BState
  δ := fun state input =>
    match state, input with
    | .init, _      => .s2     -- Always skip last position
    | .s2,   true   => .s1     -- First mark
    | .s1,   true   => .s0     -- Second mark
    | .s0,   true   => .fill   -- Third mark → fill!
    | .fill, _      => .fill   -- Stay in fill
    | s,     false  => s       -- No mark, stay
  q0 := .init
  f := fun state => state == .fill
}
```

### 3. Pure Function `g` — FST-independent semantics

```lean
def g (w : List Bool) : List Bool :=
  (List.range w.length).map fun i =>
    (w.drop i).dropLast.count true ≥ 3
```

Position i is true iff there are ≥3 marks in `w[i..len-2]` (drop position i, then drop last).

## Proof Structure

```
threshold_v n = g (mark_pow2_v n)           -- Pure combinatorics
              = bFST.scanr (mark_pow2_v n)  -- FST semantics
              = M.scanr (C.trace_rt w)      -- Two-stage form
```

### Step 1: `bFST.scanr = g` (for all w)

Show the FST computes exactly `g`. The key insight:
- FST at position i outputs true iff state after processing suffix is `.fill`
- State is `.fill` iff we've seen ≥3 marks in `w[i+1..len-1]` OR (2 marks AND current is true)
- This is equivalent to ≥3 marks in `w[i..len-2]` = `(w.drop i).dropLast`

### Step 2: `g (mark_pow2_v n) = threshold_v n` (pure combinatorics)

The key theorem:
```lean
theorem threshold_iff_marks_ge_3 (n i : ℕ) (hi : i < n) :
    (i < nextPow2 n / 8) ↔ (mark_pow2_v n).drop i |>.dropLast |>.count true ≥ 3
```

**Intuition:** 
- `nextPow2(n)/8 = 2^(log2(n-1) - 2)` for n ≥ 5
- The boundary position is `2^(log2(n-1) - 2) - 1`
- To the left of this boundary, there are ≥3 power-of-2 marks
- To the right (excluding last), there are only 2 marks

**Proof approach:**
- Small n (< 5): `nextPow2(n)/8 = 0`, verify by cases
- Large n (≥ 5): 
  - Forward: If `i < 2^(M-2)`, exhibit 3 witnesses: `2^(M-2)-1`, `2^(M-1)-1`, `2^M-1`
  - Backward: If `i ≥ 2^(M-2)`, only 2 possible marks in range: `2^(M-1)-1`, `2^M-1`

## Verification Table

| n  | M=log2(n-1) | threshold=2^(M-2) | marks in [i, n-2] for i < threshold |
|----|-------------|-------------------|-------------------------------------|
| 8  | 2           | 1                 | i=0: marks at 0,1,3 (skip 7) ≥3 ✓   |
| 9  | 3           | 2                 | i=0,1: marks at 0,1,3 (skip 7) ≥3 ✓ |
| 16 | 3           | 2                 | i=0,1: marks at 0,1,3,7 (skip 15) ≥3 ✓ |
| 17 | 4           | 4                 | i<4: marks at 0,1,3,7 (skip 15) ≥3 ✓ |

## Files

- `x_prefix_advice_two_stage_step1.lean` — Proves `bFST.scanr (mark_pow2_v n) = threshold_v n`
- `x_prefix_advice_two_stage_v2.lean` — Combines with CA/FST theory to prove `xPrefixAdvice_is_two_stage`
