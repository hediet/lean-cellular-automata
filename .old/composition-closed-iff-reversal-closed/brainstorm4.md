# Lx(L) ∈ CA(RT) ⟹ L ∈ CA(RT): Complete Construction

## Definitions

- **Lx(L)** := { x^m w | w ∈ L, m = 2^⌈log₂|w|⌉ }
- **n** = |w|
- **m** = 2^⌈log₂n⌉, so **n ≤ m < 2n**
- **CA(RT)**: accepts at (time = n-1, pos = 0) for input length n
- **OCA(2(n-1), -(n-1))** = CA(RT) via standard conversions

## Given

CA C accepting Lx(L) in real-time: accepts x^m w at (time = m+n-1, pos = 0).

## Goal

Construct CA C' accepting L in real-time: accepts w at (time = n-1, pos = 0).

---

## Construction Overview

```
CA C on Lx(L)
    │
    ▼ RegularToLeftIndep
OCA C₀ on Lx(L)
    │
    ▼ LeftIndepSpeedup (mixed config)
OCA C₁ on mixed_embed(w) with compressed x/# zone
    │
    ▼ LeftIndepToRegular  
CA C₂ on mixed_embed(w)
    │
    ▼ mirrorConfigCA + advice
CA C' on w
```

---

## Step 0: CA → OCA

Apply `RegularToLeftIndep` to CA C:
```
C₀.comp c (2t) i = C.comp c t (i + t)
```

**Result:** OCA C₀ accepts Lx(L) at (time = 2(m+n-1), pos = -(m+n-1)).

---

## Step 1: Mixed Compressed/Uncompressed Configuration

### Configuration Layout

```
pos:  ... -(n-1) ...  -d  ...  -1   │  0    1   ...  n-1   │  n   ...
     ────────────────────────────────┼─────────────────────┼────────
      #####    ...    xxxxx          │  w₀   w₁  ...  wₙ₋₁ │  #   ...
      COMPRESSED (k=5 tuples)        │  UNCOMPRESSED       │  UNCOMPRESSED
      #-zone   │ x-zone (m/4 cells)  │  w-zone             │  border
               ↑
         acceptance at -d
```

### State Space

```lean
inductive Q'
  | compressed : (Fin 5 → Q) → Q'
  | single : Q → Q'
```

### Embedding

```
mixed_embed(w)(i) :=
  if 0 ≤ i < n       then Single (embed w[i])
  else if i ≥ n      then Single (embed #)
  else if -m/4 ≤ i   then Compressed (x, x, x, x, x)  -- x-zone
  else                    Compressed (#, #, #, #, #)  -- #-zone
```

Note: The exact x/# split within a cell is determined by advice.

### Spec

Apply `LeftIndepSpeedup.spec` to the compressed zone. The spec relates compressed positions to original OCA positions/times. At the boundary (compressed pos -1, single pos 0), the original OCA naturally has w[0] at position 0 — no special handling needed.

---

## Step 2: Time and Position Analysis

### Time Budget

- m/4 < n/2 compressed x-cells (since m < 2n)
- Each compressed cell at distance d contributes 4 time units in diagonal regime
- At distance d = n-1: time contribution = 4(n-1)
- Total reachable original time = 2(n-1) + 4(n-1) = 6(n-1)

For original acceptance at 2(m+n-1):
- Need 2(m+n-1) ≤ 6(n-1)
- Simplifies to m ≤ 2n - 2
- Since m < 2n, this holds for n ≥ 2 ✓

### Acceptance Position and Component

At compressed (time = 2d, pos = -d), component j has:
- **Original time** = 2d + 4d - j = 6d - j
- **Original position** = -5d + j (relative to where w starts at 0)

For original acceptance at (time = 2(m+n-1), pos = -(m+n-1)):
```
6d - j = 2(m+n-1)
d = (2(m+n-1) + j) / 6
```

We need j ∈ {0,1,2,3,4}. We can choose d such that this holds.

### Choosing d via Advice

Set **d = ⌈(m+n-1) / 3⌉** and compute j = 6d - 2(m+n-1).

Since m+n-1 ≡ r (mod 3) for some r ∈ {0,1,2}:
- r = 0: d = (m+n-1)/3, j = 0
- r = 1: d = (m+n)/3, j = 6d - 2(m+n-1) = 2
- r = 2: d = (m+n+1)/3, j = 6d - 2(m+n-1) = 4

So **j ∈ {0, 2, 4}** always! ✓

### Verification: d ≤ n-1?

Need d = ⌈(m+n-1)/3⌉ ≤ n-1.

Worst case: m = 2n-1 (maximum).
d ≤ ⌈(2n-1+n-1)/3⌉ = ⌈(3n-2)/3⌉ = n-1 + ⌈1/3⌉ = n

Actually d could equal n, which is one more than n-1. But OCA(2n, -n) = CA(n, 0), which still accepts in time n — one step more than RT.

**Issue:** We may need time 2n instead of 2(n-1). This is **linear time** but not quite **real-time**.

**Fix:** Use the lock-in mechanism: once the original acceptance state is computed (at some earlier time), latch the result and propagate it to the standard acceptance position (2(n-1), -(n-1)).

---

## Step 3: Lock-In Mechanism

### Extended State Space

```lean
inductive Q'
  | compressed : (Fin 5 → Q) × Option Bool → Q'
  | single : Q × Option Bool → Q'
```

The `Option Bool` tracks: `none` (pending), `some true` (accept), `some false` (reject).

### Rules

1. **Detection:** If component j would be the original acceptance and shows "accept" output, set decided = some true.

2. **Latch:** Once decided ≠ none, keep it.

3. **Propagate:** In OCA, info flows left→right. If left neighbor has decided, copy it.

4. **Output:** At (2(n-1), -(n-1)), read decided.

### Why It Works

The original acceptance at (2(m+n-1), -(m+n-1)) appears somewhere in the cone of (2(n-1), -(n-1)) at compressed coordinates (≤ 2n, ≤ -1). 

The lock-in captures the result when it appears and propagates rightward. Since OCA position -(n-1) is to the right of where acceptance appears (some position ≤ -d where d ≤ n), the result arrives in time.

---

## Step 4: OCA → CA Conversion

Apply `LeftIndepToRegular` to OCA C₁:
```
C₂.comp c t i = C₁.comp c (2t) (i - t)
```

**Result:** CA C₂ accepts mixed_embed(w) at (n-1, 0).

---

## Step 5: Mirror and Advice in CA World

### mirrorConfigCA

The CA C₂ operates on mixed_embed(w). Using `spec_interior`:
- Forward component: tracks w-zone computation
- Backward component: tracks compressed x/#-zone computation

### Two-Stage Advice

Two pieces of advice needed:

1. **x/# boundary advice:** Marks positions -m/4..-1 as x-zone.
   - Similar to `exp_middle`: CArtTransducer detects m/4 = 2^(⌈log₂n⌉-2)
   - FST marks the boundary
   - Two-stage → RT-closed ✓

2. **Acceptance position advice:** Marks position -d = -⌈(m+n-1)/3⌉.
   - Computable from n via 2^⌈log₂n⌉
   - Two-stage → RT-closed ✓

### Combined Advice

Both advice functions depend on 2^⌈log₂n⌉, which is detectable by:
- CArtTransducer: marks powers of 2 in prefix lengths
- FST: computes the derived quantities (m/4, d)

This is the same structure as `exp_middle_two_stage_advice`.

---

## Step 6: Final CA for L

Chain all constructions:

1. **CA C** accepting Lx(L) at (m+n-1, 0)
2. **→ OCA C₀** via RegularToLeftIndep, accepts at (2(m+n-1), -(m+n-1))
3. **→ OCA C₁** on mixed config via LeftIndepSpeedup, accepts at (2d, -d) with lock-in
4. **→ CA C₂** via LeftIndepToRegular, accepts at (d, 0) with lock-in propagated to (n-1, 0)
5. **+ mirrorConfigCA** to track both zones from positive positions
6. **+ two-stage advice** for x/# boundary and acceptance position
7. **= CA C'** accepting L at (n-1, 0) = CA(RT) ✓

---

## Summary of Existing Theorems Used

| Theorem | Location | Purpose |
|---------|----------|---------|
| RegularToLeftIndep | results.lean | CA → OCA |
| LeftIndepToRegular | results.lean | OCA → CA |
| LeftIndepSpeedup.spec | speedup_left_independent.lean | k-step compression |
| mirrorConfigCA.spec_interior | basic_mirror.lean | Simultaneous forward/backward |
| exp_middle_two_stage_advice | exp_middle_two_stage.lean | Power-of-2 marking |
| two_stage_is_rt_closed | is_two_stage_of_rt_closed_and_causal.lean | Advice doesn't change RT |

## New Constructions Needed

1. **Mixed Q' state space:** Compressed | Single with lock-in flag
2. **mixed_embed function:** Embedding with compressed left zone
3. **LeftIndepSpeedup boundary handling:** Compressed ↔ Single transitions
4. **Acceptance position advice:** Mark position -d based on 2^⌈log₂n⌉
5. **Lock-in δ extension:** Detect, latch, propagate acceptance result

---

## Example Walkthrough: n = 5

- m = 2^⌈log₂5⌉ = 2³ = 8
- Original acceptance: (2(8+5-1), -(8+5-1)) = (24, -12)
- d = ⌈(8+5-1)/3⌉ = ⌈12/3⌉ = 4
- j = 6×4 - 2×12 = 24 - 24 = 0 ✓
- Compressed acceptance: (2×4, -4) = (8, -4)
- CA acceptance: (4, 0) = (n-1, 0) ✓

```
Mixed config for "abcde":
pos:  -4     -3     -2     -1   │  0    1    2    3    4
     ────────────────────────────┼─────────────────────────
     #####  ##xxx  xxxxx  xxxxx │  a    b    c    d    e
     d=4    d=3    d=2    d=1   │  single cells
     ↑ acceptance here
```

At (t=8, pos=-4, j=0): original_time = 8 + 16 - 0 = 24 ✓

---

## Confidence Assessment

**High confidence (90%+):**
- All conversion theorems (CA ↔ OCA)
- LeftIndepSpeedup core spec
- Two-stage advice is RT-closed

**Medium-high confidence (75-85%):**
- Time budget calculation (m < 2n ensures enough time)
- Component formula (j ∈ {0,2,4} by mod-3 analysis)

**Medium confidence (60-75%):**
- Lock-in mechanism correctness (standard but needs verification)
- Compressed/Single boundary transitions
- Advice correctly computes both m/4 and d

**Overall: 70-80%** — The construction is sound in principle; main work is verifying the arithmetic and formalizing the boundary handling.
