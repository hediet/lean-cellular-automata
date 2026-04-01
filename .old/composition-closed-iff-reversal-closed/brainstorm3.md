# Clean Plan: Lx(L) ∈ CA(RT) ⟹ L ∈ CA(RT)

## Key Equivalence

**OCA(2(n-1), -(n-1)) = CA(n-1, 0) = CA(RT)**

---

## Given

CA C accepting Lx(L) where:
- Lx(L) = { x^m w | w ∈ L, m = 2^⌈log₂|w|⌉ }
- Accepts at (time = m+n-1, pos = 0)

## Goal

Construct CA C' accepting L at (time = n-1, pos = 0).

---

## Step 0: CA → OCA

Convert CA C to OCA C₀ via `RegularToLeftIndep`:
```
C₀.comp c (2t) i = C.comp c t (i + t)
```

Now OCA C₀ accepts Lx(L) at (time = 2(m+n-1), pos = -(m+n-1)).

---

## Step 1: Mixed Compressed/Uncompressed Configuration

Define a configuration with **two zones**:

```
pos:  ...  -3     -2     -1   │  0    1    2   ...  n-1   │  n   n+1  ...
     ─────────────────────────┼───────────────────────────┼─────────────
     #####  #xxxx  xxxxx      │  w₀   w₁   w₂  ...  wₙ₋₁  │  #    #   ...
     COMPRESSED (k=5 tuple)   │  UNCOMPRESSED (single)    │  UNCOMPRESSED
```

**Left zone (positions < 0):** Compressed cells, each holding a `Fin 5 → Q` tuple
- Represents the x^m prefix and # border
- Uses LeftIndepSpeedup compression

**Right zone (positions ≥ 0):** Uncompressed single cells
- Position 0..n-1: the input word w
- Position ≥ n: border #

### State Space

```
Q' = Compressed (Fin 5 → Q) | Single Q
```

With projection:
- `Compressed w → spatial regime output` (all 5 components projected)
- `Single q → single cell output`

### Embedding

```
mixed_embed(w) : ℤ → Q'
mixed_embed(w)(i) = 
  if i ≥ 0 ∧ i < n then Single (embed w[i])
  else if i ≥ n then Single (embed #)
  else Compressed (x/# pattern based on advice)
```

---

## Step 2: OCA on Mixed Config

**Claim:** There exists OCA C₁ such that C₁ on mixed_embed(w) computes the same acceptance as C₀ on x^m w, with the result available at (2(n-1), -(n-1)) via the lock-in mechanism.

**Proof sketch:**
- Use LeftIndepSpeedup spec for the compressed zone
- At compressed position i < 0, component j has original position 5i + j
- Diagonal regime: original time = t + 4|i| - j
- Uncompressed positions pass through directly
- Lock-in captures the acceptance result whenever it occurs

**Key insight:** The original acceptance at (2(m+n-1), -(m+n-1)) falls within the space-time cone of our compressed acceptance (2(n-1), -(n-1)). The lock-in mechanism ensures we capture and propagate this result.

---

## Step 3: OCA → CA on Mixed Config

Convert OCA C₁ to CA C₂ via `LeftIndepToRegular`:
```
C₂.comp c t i = C₁.comp c (2t) (i - t)
```

CA C₂ accepts mixed_embed(w) at:
- OCA accepted at (2(n-1), -(n-1))
- CA accepts at (n-1, 0)

**The CA operates on the same mixed config!**

---

## Step 4: Apply Mirror + Advice in CA World

Now we have CA C₂ on mixed config accepting at (n-1, 0).

### Mirror Theory

Use `mirrorConfigCA` to understand how the CA tracks both zones:

**spec_interior:**
```
mirrorConfigCA(C).comp ⦋w⦌ t i = (C.comp ⦋mirror_config w⦌ t i, 
                                  C.comp ⦋mirror_config w⦌ t (i - n))
```

The forward component tracks the w-zone (positions 0..n-1).
The backward component tracks the compressed x/#-zone (negative positions).

### Advice for x/# Boundary

Mark positions 0..m/4-1 in the negative region as x-zone (rest is #-zone).

Use `exp_middle`-style two-stage advice:
- CArtTransducer computes powers of 2
- FST selects the right boundary

**Theorem:** Two-stage advice is RT-closed, so adding it doesn't change CA(RT) power.

---

## Step 5: Final CA for L

Chain all constructions:

1. CA C accepting Lx(L) at (m+n-1, 0)
2. → OCA C₀ accepting at (2(m+n-1), -(m+n-1))
3. → OCA C₁ on mixed config accepting at (2(n-1), -(n-1))
4. → CA C₂ on mixed config accepting at (n-1, 0)
5. + advice marking x/# boundary
6. = CA C' accepting L at (n-1, 0) = CA(RT) ✓

---

## Updated LeftIndepSpeedup Spec

Need to update/verify that LeftIndepSpeedup handles mixed compressed/uncompressed:

**Original spec (for fully compressed):**
```
(e.C.comp w t i)[j] = C.comp w (t - (k-1)·i - j) (k·i + j)
```
(for negative i in diagonal regime)

**Extended for mixed config:**
- Compressed zone (i < 0): Use spatial/diagonal regime as before
- Uncompressed zone (i ≥ 0): Direct pass-through, `Single q` maps to `q`

The δ function for C₁ needs to handle the boundary between zones:
- Compressed cell at pos -1 has right neighbor = Single cell at pos 0
- Transition function combines: `δ'(compressed, single) → compressed`

This is where the "single → spatial embedding" comes in: treat Single q as if it were a spatial-regime compressed cell with all components equal to q.

---

## Transition at Compressed/Uncompressed Boundary

At the boundary (compressed cell at -1, single cell at 0):

```
δ'(left: Compressed, center: Compressed, right: Single q) = 
  Compressed (compute_fold using right = (q, q, q, q, q))
```

I.e., the Single cell is treated as a compressed cell in spatial regime (all components equal).

Similarly, the single cell at 0 sees:
```
δ'(left: Compressed w, center: Single q, right: Single r) = 
  Single (C.δ (w[k-1]) q r)
```

I.e., it uses the rightmost component (j = k-1 = 4) of the compressed neighbor.

---

## Summary of Constructions Used

| Step | Construction | Input | Output |
|------|--------------|-------|--------|
| 0 | RegularToLeftIndep | CA C | OCA C₀ |
| 1 | LeftIndepSpeedup (mixed) | OCA C₀ | OCA C₁ on mixed config |
| 2 | LeftIndepToRegular | OCA C₁ | CA C₂ on mixed config |
| 3 | mirrorConfigCA | CA C₂ | CA with mirror tracking |
| 4 | two-stage advice | mark x/# boundary | RT-closed |
| 5 | compose | all above | CA C' for L |

---

## Example: n=5, m=8

**Original:** CA C on "xxxxxxxxabcde" accepts at (t=12, pos=0)

**Step 0:** OCA C₀ accepts at (t=24, pos=-12) [in coords where w starts at pos 8]

**Step 1:** OCA C₁ on mixed config:
```
pos:  -4     -3     -2     -1   │  0    1    2    3    4
     ────────────────────────────┼─────────────────────────
     #####  ##xxx  xxxxx  xxxxx │  a    b    c    d    e
     comp   comp   comp   comp  │ single cells
     d=4    d=3    d=2    d=1   │
```

**Marked area:** 2 cells (positions -1, -2) for m/4 = 2 → represents 8 x's
**Unmarked area:** Positions -3, -4, ... → represents #'s

**Acceptance directly at compressed (t=8, pos=-4, j=0):**
- At pos=-4 (d=4), j=0: original_time = t + 4d - j = 8 + 16 - 0 = 24 ✓
- Original position: 5×d to the left of w = 5×4 = 20 positions left of w
- In original coords where w starts at m=8: position 8 - 20 = -12 ✓

**So (t=8, pos=-4, j=0) in compressed = (t=24, pos=-12) in original!**

From brainstorm.md diagram:
```
t=8:   #₂₄#₂₃#₂₂#₂₁#₂₀★  
        [diagonal]       
                     ↑
          Component 0 = #₂₄ = original (pos=-12, t=24) ✓
```

The acceptance state appears **directly** at the compressed acceptance position — no lock-in propagation needed!

**Step 2:** OCA at (2(n-1), -(n-1)) = (8, -4) contains the acceptance state in component 0.

CA C₂ via LeftIndepToRegular: CA accepts at (t, i) where OCA accepts at (2t, i-t).
- 2t = 8 → t = 4
- i - t = -4 → i = 0

CA accepts at (t=4, pos=0) = (n-1, 0) ✓

---

## When IS Lock-In Needed?

**Lock-in is needed when** the acceptance appears in component j ≠ 0.

### Component Formula

At compressed (t = 2(n-1), pos = -(n-1)), which component j contains the original acceptance?

From original_time = t + 4d - j where d = n-1:
```
2(m+n-1) = 2(n-1) + 4(n-1) - j
j = 4(n-1) - 2m = 4n - 4 - 2m
```

**Examples:**

| n | m | j = 4n - 4 - 2m | Valid (0 ≤ j ≤ 4)? |
|---|---|-----------------|---------------------|
| 3 | 4 | 12 - 4 - 8 = 0 | ✓ |
| 4 | 4 | 16 - 4 - 8 = 4 | ✓ |
| 5 | 8 | 20 - 4 - 16 = 0 | ✓ |
| 6 | 8 | 24 - 4 - 16 = 4 | ✓ |
| 7 | 8 | 28 - 4 - 16 = 8 | ✗ |
| 8 | 8 | 32 - 4 - 16 = 12 | ✗ |
| 9 | 16 | 36 - 4 - 32 = 0 | ✓ |

**Problem:** For n near a power of 2 (specifically n = 2^k - 1, 2^k), j > 4!

### Analysis

For n = 2^k (power of 2): m = 2^k = n, so j = 4n - 4 - 2n = 2n - 4 = 2(2^k) - 4
- n = 4: j = 4 ✓ (boundary)
- n = 8: j = 12 ✗

**The issue:** When m = n (both powers of 2), the time skew between original and compressed exceeds what 5 components can handle.

### Potential Fixes

1. **Use larger k:** With k=6, we have 5 extra time per cell, might be enough
   - j = 5(n-1) - 2m for k=6
   - For n=8, m=8: j = 35 - 16 = 19... still too large

2. **Use different compression for different n/m ratios:**
   - When m ≈ n, use smaller speedup
   - When m ≈ 2n, use larger speedup

3. **Variable window position:**
   - Don't fix acceptance at -(n-1), allow it to vary based on m
   - Accept at position -(n-1+δ) where δ absorbs the component mismatch

4. **Multi-stage compression:**
   - First stage: compress some
   - Second stage: compress more

---

## Revised Approach: Variable Acceptance Position

Instead of fixing acceptance at (2(n-1), -(n-1)), let the position vary:

**Claim:** There exists d ≤ n such that acceptance at (2d, -d) correctly captures original acceptance at (2(m+n-1), -(m+n-1)) in some component j ∈ {0,1,2,3,4}.

**Derivation:**
- original_time = 2d + 4d - j = 6d - j
- 2(m+n-1) = 6d - j
- d = (2(m+n-1) + j) / 6

For j ∈ {0,1,2,3,4}, we need (2(m+n-1) + j) to be divisible by 6 for some j.

Since consecutive 5 values are checked, at least one will satisfy d being close to correct.

**But** we still need d ≤ n for real-time acceptance. Let's check:
- d ≤ (2(m+n-1) + 4) / 6 = (2m + 2n + 2) / 6 = (m + n + 1) / 3
- Need (m + n + 1) / 3 ≤ n → m + n + 1 ≤ 3n → m ≤ 2n - 1

Since m < 2n, we have m ≤ 2n - 1 ✓

So d ≤ n is achievable!

---

## Updated Construction with Variable d

1. Choose d = ⌈(2(m+n-1)) / 6⌉ (rounded to make j ∈ {0,...,4})
2. Acceptance at (2d, -d) in compressed OCA
3. j = 6d - 2(m+n-1)

Since we don't know m at runtime, use **advice** to mark d in the compressed zone.

The advice marks position -d based on the power-of-2 structure of m, which is computable from input length markers.

---

## Padding Analysis and Time Budget

### Padding Size

- m = 2^⌈log₂n⌉, so **n ≤ m < 2n**
- m/4 compressed x-cells needed (marked area)
- Since m < 2n: **m/4 < n/2** compressed x-cells

### Marked vs Unmarked Areas

```
pos:  ... -(n-1) ... -m/4  ...  -1   │  0    1   ...  n-1
     ─────────────────────────────────┼─────────────────────
      ###...###    xxx...xxx          │  w₀   w₁  ...  wₙ₋₁
      UNMARKED     MARKED (m/4 cells) │  UNCOMPRESSED
      ≤ n cells    < n/2 cells        │  n cells
```

- **Marked area:** m/4 < n/2 compressed cells → represents the x-zone
- **Unmarked area:** Remaining cells to the left → represents the #-zone
- Total compressed area: up to n-1 cells (to reach acceptance position -(n-1))

### Time Budget

With 4x speedup (k=5, gain = k-1 = 4):
- Each compressed cell at distance d contributes 4 time units
- At distance n-1, time contribution = 4(n-1)
- Base time = 2(n-1)
- Total original time reachable = 2(n-1) + 4(n-1) = 6(n-1)

For original acceptance at 2(m+n-1):
- Need 2(m+n-1) ≤ 6(n-1)
- 2m + 2n - 2 ≤ 6n - 6
- 2m ≤ 4n - 4
- m ≤ 2n - 2

Since m < 2n, we have **m ≤ 2n - 1 ≤ 2n - 2** for n ≥ 2 ✓

---

## Lock-In Mechanism (Revised)

The lock-in is simpler than originally thought:

### When j is within {0,1,2,3,4}

Just **project the correct component j** at acceptance time. The formula j = 4(n-1) - 2m can be computed via advice (since m is a power of 2 determined by n).

### When j > 4 (doesn't fit in window)

Use **variable acceptance position d** such that j falls in range. This requires advice to mark position -d.

### Implementation

1. **Advice 1:** Mark positions in x-zone (m/4 cells) vs #-zone
2. **Advice 2:** Mark the acceptance position -d based on m = 2^⌈log₂n⌉
3. **Projection:** At position -d, time 2d, project component j = 6d - 2(m+n-1)

Both advice functions are two-stage (depend on powers of 2), hence RT-closed.

---

## What Needs to be Formalized

1. **Mixed Q' state space:** `Compressed (Fin k → Q) | Single Q`

2. **mixed_embed function:** Embeds w with compressed x/# on left

3. **LeftIndepSpeedup extended spec:** Handles mixed compressed/uncompressed

4. **Boundary δ transitions:** Compressed ↔ Single interaction

5. **Component formula:** j = 4(n-1) - 2m, with case split on whether j ∈ {0,...,4}

6. **Variable d advice:** When j > 4, compute d = ⌈(2(m+n-1) + j') / 6⌉ for some j' ∈ {0,...,4}

7. **Two-stage advice constructions:**
   - x/# boundary marking (similar to exp_middle)
   - Acceptance position marking (similar to exp_middle)

8. **Final theorem:** Chain all constructions, prove L ∈ CA(RT)

---

## Open Questions

1. **Is variable d always ≤ n?** Claimed yes, but needs formal proof.

2. **Can both advice functions be combined into one two-stage advice?** Likely yes, since both depend on 2^⌈log₂n⌉.

3. **Does the boundary handling at position -1 work correctly?** The single ↔ compressed transition needs careful verification.

4. **What happens for small n (n ≤ 3)?** Edge cases where m/4 < 1.

---

## Summary

The construction works with these components:

1. **CA → OCA conversion** (existing)
2. **LeftIndepSpeedup with mixed config** (needs extension)
3. **OCA → CA conversion** (existing)
4. **Mirror theory** (existing)
5. **Two-stage advice** (existing framework, new specific advice)
6. **Component selection via advice** (new, but uses existing power-of-2 machinery)

**Confidence: 65-75%** — The main uncertainty is whether all the component/position arithmetic works out cleanly for all n, and whether the boundary transitions are correct.

3. **LeftIndepSpeedup extended spec:** Handles mixed compressed/uncompressed

4. **Boundary δ transitions:** Compressed ↔ Single interaction

5. **Time/position calculations:** Verify for all cases

6. **Advice marking:** Two-stage advice for x/# boundary

7. **Final theorem:** Chain all constructions, prove L ∈ CA(RT)
