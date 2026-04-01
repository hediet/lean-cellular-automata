# Plan: OCA_lt = OCA_2n

## Goal
Prove `ℒ(OCA_lt) = ℒ(OCA_2n)` — linear-time OCAs accept the same languages as time-2(n-1) OCAs.

## Space-Time Diagram (k=2 Compression)

Input: `a b c d` (n=4), right border is `#` (quiescent).

**Note:** k=2 is the baseline — no speedup occurs (2*(n-1) → 2*(n-1)). For actual speedup, use k≥3.
This diagram shows the **mechanism**; the speedup becomes visible with k=3.

**Original OCA evolution:**
```
Position:    0    1    2    3    4    5    6
           ────────────────────────────────────
Time 0:      a    b    c    d    #    #    #
Time 1:      a₁   b₁   c₁   d₁   #    #    #
Time 2:      a₂   b₂   c₂   d₂   #    #    #
Time 3:      a₃   b₃   c₃   d₃   #    #    #
Time 4:      a₄   b₄   c₄   d₄   #    #    #
Time 5:      a₅   b₅   c₅   d₅   #    #    #
Time 6:      a₆   b₆   c₆   d₆   #    #    #
             ↑
         Accept at time k*(n-1) = 2*3 = 6 for k=2
```

Where (by left-independence, δ only uses middle and right):
- `d₁ = δ(d, #)`
- `d₂ = δ(d₁, #)`
- `c₁ = δ(c, d)`
- `c₂ = δ(c₁, d₁)`

**Compressed OCA (k=2) — pairs on the border:**
```
Position:    0       1       2       3         4
           ───────────────────────────────────────────
Time 0:      a       b       c       d         (#,#₁)      where #₁ = δ(#,#)
Time 1:      a₁      b₁      c₁      (d₁,d₂)   (#₂,#₃)     where #₂ = δ(#,#), #₃ = δ(#₁,#₁)
Time 2:      a₂      b₂      (c₂,c₃) (d₃,d₄)   (#₄,#₅)
Time 3:      a₃      (b₃,b₄) (c₄,c₅) (d₅,d₆)   (#₆,#₇)
Time 4:      (a₄,a₅) (b₅,b₆) (c₆,c₇) (d₇,d₈)   (#₈,#₉)
Time 5:      (a₆,a₇) (b₇,b₈) (c₈,c₉) (d₉,d₁₀) (#₁₀,#₁₁)
Time 6:      (a₈,a₉) (b₉,b₁₀) (c₁₀,c₁₁) (d₁₁,d₁₂) (#₁₂,#₁₃)
             ↑
         At time 6 = 2*(n-1), position 0 has (a₈, a₉)
         Component 0 gives a₈, component 1 gives a₉
```

Note: The "compression wave" propagates left. At compressed time t:
- Positions ≥ n-t become tuples
- Position 0 becomes a tuple at time n-1 = 3


**How the d column compresses in one step:**

Given `d` and border tuple `(#, #₁)`:
```
d₁ = δ(d, #)           ← uses d and first component of border
d₂ = δ(d₁, #₁)         ← uses d₁ and second component of border
```
Result: `(d₁, d₂)` computed in **one** compressed step.

**Propagation to position 0:**

At compressed time `t`, position 0 has seen `k*t` diagonal steps worth of information from the right border (since each compressed border step does k original steps). So:
- Original: accepts at time `k*(n-1)` at position 0
- Compressed with factor k: accepts at time `2*(n-1)` at position 0

For k=2: no speedup (6 → 6)
For k=3: speedup from 9 → 6
For k=4: speedup from 12 → 6

## Key Insight

For a left-independent OCA accepting at time `k*(n-1)` at position 0:
- Cell (t, p) only depends on cells p, p+1, ..., p+t at time 0
- Information flows **right-to-left**
- The **right border** (positions ≥ n) is quiescent, containing #^∞
- By compressing k border cells into one k-tuple, we can do k steps in one

## The Speedup Argument

Original OCA C accepts at time `k*(n-1)`, position 0.

With right-border compression factor k:
- Compress positions n, n+1, ..., n+k-1 into a single cell with state (q_n, q_{n+1}, ..., q_{n+k-1})
- The compressed border cell evolves k times faster (in terms of diagonal propagation)
- At time 2*(n-1), the cell at position 0 has received all the information it would have at time k*(n-1) in the original

**Result:** `C.comp w (k*(n-1)) 0 = C'.comp w (2*(n-1)) 0`

## Required Construction: RightBorderSpeedupOCA

Existing `LeftIndepSpeedup` compresses the **left** border (positions i < 0).

For OCA_lt = OCA_2n, we need `RightBorderSpeedupOCA` that compresses the **right** border (positions i ≥ n).

### Derivation of the Spec

**Setup:**
- OCA C (left-independent), word of length n
- Compression factor k ≥ 2
- Right border is quiescent: positions ≥ n have state #

**When does position i become a tuple?**

The "compression wave" propagates left from the border:
- Position n-1 → tuple at compressed time 1
- Position n-2 → tuple at compressed time 2
- Position i → tuple at compressed time **n - i**

**Invariant:**

For position i < n, compressed time t ≥ n - i, component j ∈ [0, k):

At the moment of becoming a tuple (t = n - i):
- Component j represents original time (n - i) + j
- (We compute k original steps at once using the border k-tuple)

After Δt = t - (n - i) additional compressed steps:
- Each step advances by k original time units (foldLeft with right neighbor tuple)
- Component j represents original time (n - i) + j + k · Δt

**The mapping φ:**

```
φ(t, i, j) = (n - i) + j + k · (t - (n - i))
           = k·t - (k-1)·(n - i) + j
```

**Spec:**
```
C'.comp w t i [j] = C.comp w (φ(t, i, j)) i
```

**Verification:**
| t | i | j | φ(t,i,j) | Meaning |
|---|---|---|----------|---------|
| n-i | i | 0 | n-i | First tuple, component 0 |
| n-i | i | k-1 | n-i+k-1 | First tuple, last component |
| n-i+1 | i | 0 | n-i+k | After one more step |

### At Position 0, Time 2·(n-1)

```
φ(2(n-1), 0, j) = k·2(n-1) - (k-1)·n + j
                = 2kn - 2k - kn + n + j
                = (k+1)n - 2k + j
```

**For j = 0:** original time = (k+1)n - 2k

**Comparing to target time k·(n-1) = kn - k:**
```
(k+1)n - 2k ≥ kn - k  ⟺  n ≥ k
```

**Result:**
- For n ≥ k: component 0 at time 2(n-1) gives original time **(k+1)n - 2k ≥ k(n-1)** ✓
- For n < k: component **j = k - n** gives original time exactly **k(n-1)** ✓

In both cases, compressed time 2(n-1) suffices to determine acceptance!

## Implementation Options

1. **New `RightBorderSpeedupOCA`** — mirror the `LeftIndepSpeedup` proof with positions flipped

2. **Use mirror construction:**
   - `mirror_CA`: OCA → OCAr (swaps left/right independence)
   - Write symmetric `RightIndepSpeedup` for OCAr (same work as option 1)
   - Apply to mirrored CA, then mirror back

~~3. **Derive from existing via reversed input**~~ — **Does not work:**
   - Reversing input doesn't change which border has speedup potential (still right border for left-indep)
   - Mirroring changes left-indep to right-indep, but `LeftIndepSpeedup` requires left-independence
   - Would need symmetric `RightIndepSpeedup` anyway

Option 1 is cleanest — the LeftIndepSpeedup proof structure transfers with sign changes.

## Files to Create/Modify

- [x] `CellularAutomatas/proofs/constructions/speedup_right_border_oca.lean` — new construction (created, 2 sorry in invariant proof)
- [ ] `CellularAutomatas/results.lean` — add `oca_linear_time_eq_2n` theorem
- [ ] Remove sorry from `CellularAutomatas/results_unproven.lean`
