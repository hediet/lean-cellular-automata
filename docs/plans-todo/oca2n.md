# Completed: OCA_lt = OCA_2n

## Result
The theorem `ℒ(OCA_lt) = ℒ(OCA_2n)` is proved in
`CellularAutomatas/proofs/constructions/speedup_right_border_oca.lean` and
exported as `CellularAutomatas.results.oca_linear_time_eq_2n`.

The key correction to the original plan is exact timing. For a source OCA with
coefficient `c ≥ 3`, the construction compresses tuples of width `m = c - 1`
and reads component `j = c - 2`. Compressing with width `c` generally reaches a
time later than `c(n-1)`, which is insufficient because acceptance need not be
stable after its designated time.

## Space-Time Diagram (m=2 Compression, c=3 Source)

Input: `a b c d` (n=4), right border is `#` (quiescent).

Here `m` is the tuple width and the source coefficient is `c = m + 1`.
Thus width `m=2` speeds source time `3(n-1)` up to `2(n-1)`.

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
   ...
Time 9:      a₉   b₉   c₉   d₉   #    #    #
                   ↑
             Accept at time c*(n-1) = 3*3 = 9
```

Where (by left-independence, δ only uses middle and right):
- `d₁ = δ(d, #)`
- `d₂ = δ(d₁, #)`
- `c₁ = δ(c, d)`
- `c₂ = δ(c₁, d₁)`

**Compressed OCA (m=2) — pairs on the border:**
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
         Component j=c-2=1 gives exactly a₉
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

At compressed time `t`, each tuple step advances `m` original time steps.
For source coefficient `c=m+1`, component `j=m-1` at compressed time
`2(n-1)` represents exactly source time `c(n-1)`.

For `m=2`: speedup from 9 to 6.
For `m=3`: speedup from 12 to 6.

## Key Insight

For a left-independent OCA accepting at time `c*(n-1)` at position 0:
- Cell (t, p) only depends on cells p, p+1, ..., p+t at time 0
- Information flows **right-to-left**
- The **right border** (positions ≥ n) is quiescent, containing #^∞
- By using tuples of width `m = c-1`, we can do `m` steps in one

## The Speedup Argument

Original OCA C accepts at time `c*(n-1)`, position 0.

With tuple width `m = c-1`:
- The compressed border stores `m` consecutive original states.
- The compression wave reaches position 0 after `n` compressed steps.
- At time `2(n-1)`, component `j = c-2` represents exactly original time `c(n-1)`.

**Result:** `C.comp w (c*(n-1)) 0 = C'.comp w (2*(n-1)) 0`

## Required Construction: RightBorderSpeedupOCA

Existing `LeftIndepSpeedup` compresses the **left** border (positions i < 0).

For OCA_lt = OCA_2n, we need `RightBorderSpeedupOCA` that compresses the **right** border (positions i ≥ n).

### Derivation of the Spec

**Setup:**
- OCA C (left-independent), word of length n
- Tuple width `m ≥ 2`
- Right border is quiescent: positions ≥ n have state #

**When does position i become a tuple?**

The "compression wave" propagates left from the border:
- Position n-1 → tuple at compressed time 1
- Position n-2 → tuple at compressed time 2
- Position i → tuple at compressed time **n - i**

**Invariant:**

For position i < n, compressed time t ≥ n - i, component j ∈ [0, m):

At the moment of becoming a tuple (t = n - i):
- Component j represents original time (n - i) + j
- (We compute `m` original steps at once using the border tuple)

After Δt = t - (n - i) additional compressed steps:
- Each step advances by `m` original time units (foldLeft with the right-neighbor tuple)
- Component j represents original time `(n-i) + j + m·Δt`

**The mapping φ:**

```
φ(t, i, j) = (n - i) + j + m · (t - (n - i))
           = m·t - (m-1)·(n - i) + j
```

**Spec:**
```
C'.comp w t i [j] = C.comp w (φ(t, i, j)) i
```

**Verification:**
| t | i | j | φ(t,i,j) | Meaning |
|---|---|---|----------|---------|
| n-i | i | 0 | n-i | First tuple, component 0 |
| n-i | i | m-1 | n-i+m-1 | First tuple, last component |
| n-i+1 | i | 0 | n-i+m | After one more step |

### Exact Time at Position 0

Set `m = c-1` and choose `j = c-2 = m-1`. At compressed time `2(n-1)`:
```
φ(2(n-1), 0, c-2)
  = (c-1)·2(n-1) - (c-2)·n + (c-2)
  = c(n-1).
```

This equality, rather than an inequality, is what transfers acceptance without
assuming that the source CA latches its answer.

## Completed Construction

`RightBorderSpeedupOCA` first makes the border quiescent while preserving
left-independence, then propagates compressed tuples left from that border. Its
main invariant is `spec_compressed_nextt`, proved by induction on compressed
time with separate first-compression and steady-compression branches.

The language-level proof handles coefficients separately:
- `c = 0`: preserve the embedded input state forever.
- `c = 1`: repackage as real time, then delay with a left-independent latch.
- `c = 2`: use the source machine unchanged.
- `c ≥ 3`: use right-border compression with width `c-1`.

## Files to Create/Modify

- [x] `CellularAutomatas/proofs/constructions/speedup_right_border_oca.lean`
- [x] `CellularAutomatas/results.lean`: exports `oca_linear_time_eq_2n`
- [x] `CellularAutomatas/verification_candidates.lean`: candidate removed
