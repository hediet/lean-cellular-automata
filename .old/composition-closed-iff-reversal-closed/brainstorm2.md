# Detailed Plan: Lx(L) ∈ CA(RT) ⟹ L ∈ CA(RT)

## Equivalences Used

**Key fact:** OCA(2(n-1), -(n-1)) = CA(n-1, 0) = CA(RT)

Via:
- `LeftIndepToRegular`: OCA.comp c t i = CA.comp c (2t) (i-t)
- `RegularToLeftIndep`: CA.comp c t i = OCA.comp c (2t) (i-t)

Setting t' = n-1, i = 0 in CA ↔ t = n-1, i' = -(n-1) in OCA.

---

## Given

OCA C accepting Lx(L) where:
- Lx(L) = { x^m w | w ∈ L, m = 2^⌈log₂|w|⌉ }
- Input length N = m + n
- Accepts at (time = 2(N-1), pos = -(N-1)) = (2(m+n-1), -(m+n-1))

## Goal

Construct CA C' accepting L at (time = n-1, pos = 0).

---

## Step 1: Compressed Configuration for OCA

Define a compressed embedding that maps word w to a configuration where:
- **Positions 0..n-1:** The actual letters w[0], w[1], ..., w[n-1]
- **Positions -1, -2, ..., -m/4:** Compressed x-cells (each holds 5 original cells)
- **Positions < -m/4:** Compressed #-cells (each holds 5 original cells)

### Compressed Config Definition

```
compressed_config(w) : Config (Fin 5 → (α？ × Bool))
```

Where for position i:
- If i ≥ 0: `(w[i], true)` in component 0, border in others (single-cell mode)
- If -m/4 ≤ i < 0: x-zone compressed cell
- If i < -m/4: #-zone compressed cell

The Bool tag distinguishes:
- `true`: w-zone (actual input)
- `false`: x/#-zone (compressed virtual prefix)

### LeftIndepSpeedup Spec Recap

For OCA with k=5 compression at negative position i (i.e., i < 0, d = |i|):

```
comp_compressed(t, i)[j] = comp_orig(τ(t,d,j), ψ(i,j))
```

Where (diagonal regime, t ≥ d):
- τ(t, d, j) = t + 4d - j  (original time)
- ψ(i, j) = 5i + j         (original position)

---

## Step 2: Show OCA C Accepts on Compressed Config

**Claim:** OCA C on `compressed_config(w)` accepts at (2(n-1), -(n-1)) iff w ∈ L.

### Time Calculation

At acceptance position -(n-1) in compressed coords, time 2(n-1):
- d = n - 1
- Original time = 2(n-1) + 4(n-1) - 0 = 6(n-1) - but wait...

Hmm, let me recalculate. Looking at brainstorm.md examples:

For n=3, m=4:
- Compressed acceptance: (pos=2, t=4)  (relative to w at positions 4..6)
- In our new coords with w at 0..2: pos = 2-4 = -2 = -(n-1) ✓
- Original acceptance was at (pos=-6, t=12)

Check: At compressed pos -2, t=4:
- d = 2
- Original time = 4 + 4×2 - 0 = 12 ✓
- Original pos = 5×(-2) + 0 = -10... that's not -6

Wait, the indexing in brainstorm.md has w starting at position 4, not 0. Let me reconsider...

---

## Step 2 (Revised): Configuration Layout

In brainstorm.md, with w at positions m..m+n-1:
- Original x-zone: positions 0..m-1
- Original #-zone: positions < 0
- Compressed x/#-zone: positions 0..m/4+n-1 (shifted right so w is at m/4..m/4+n-1)

**Alternative approach:** Keep w at positions 0..n-1, put compressed stuff at negative positions:

```
Compressed layout:
pos:  ...  -3     -2     -1   │  0    1    2   ...  n-1
     ─────────────────────────┼─────────────────────────
      ####  ####  xxxx        │  w₀   w₁   w₂  ...  wₙ₋₁
      comp  comp  comp        │  single cells
```

With m=4, n=3: m/4 = 1 compressed x-cell at pos -1.

---

## Step 3: OCA → CA Conversion

Convert the OCA with compressed config to CA:

**Theorem (LeftIndepToRegular):**
```
CA.comp c t i = OCA.comp c (2t) (i - t)
```

So OCA accepting at (2(n-1), -(n-1)) corresponds to CA accepting at (n-1, 0).

The CA operates on the same compressed configuration! The conversion preserves the spatial layout.

---

## Step 4: Apply Mirror Theory in CA World

Now we have CA C₁ on compressed config accepting at (n-1, 0).

Use `mirrorConfigCA` to understand the backward component:
- Forward: tracks computation at position i (w-zone)
- Backward: tracks computation at position i - n (compressed x/#-zone)

**spec_interior:**
```
mirrorConfigCA(C).comp ⦋w⦌ t i = (C.comp ⦋mirror_config w⦌ t i, 
                                  C.comp ⦋mirror_config w⦌ t (i - n))
```

For this to work, we need mirror_config to embed the compressed stuff at negative positions. This is exactly what we defined!

---

## Step 5: Advice Theory for x/# Boundary

The compressed config needs to know where x-zone ends and #-zone begins. Use advice:

**Marker advice (two-stage, hence RT-closed):**
- Mark positions 0..m/4-1 in the negative region
- Marked → x-cell
- Unmarked → #-cell

This is similar to `exp_middle` advice: uses CArtTransducer + FST, hence two-stage.

**Theorem:** Two-stage advice is RT-closed.

So adding this advice doesn't change CA(RT) recognition power.

---

## Step 6: Uniform Zone Lemma

The x-zone and #-zone are uniform (all same symbol). This means:

**Lemma:** For OCA C, the state at any position in x^m at time t depends only on:
1. Distance from left border (#/x boundary)
2. Distance from right border (x/w boundary)
3. Time t

Since x is a fixed symbol, these dynamics can be precomputed into the compression.

Similarly for #-zone (all border symbols).

---

## Full Construction Summary

1. **Input:** OCA C accepting Lx(L) at (2(m+n-1), -(m+n-1))

2. **Compress:** Define `compressed_embed` that places:
   - w at positions 0..n-1
   - Compressed x-cells at positions -m/4..-1
   - Compressed #-cells at positions < -m/4

3. **Show OCA accepts compressed config:** Using LeftIndepSpeedup spec, OCA C on compressed_embed(w) accepts at (2(n-1), -(n-1)) iff x^m w ∈ Lx(L) iff w ∈ L

4. **Convert to CA:** Via LeftIndepToRegular, get CA C₁ accepting compressed_embed(w) at (n-1, 0)

5. **Apply mirror_config:** Use spec_interior to show mirrorConfigCA tracks both w (forward) and compressed prefix (backward)

6. **Add advice:** Two-stage advice marks x/# boundary, doesn't change RT power

7. **Result:** CA C' accepting w at (n-1, 0) = CA(RT) for L ✓

---

## Key Theorems Needed

1. **LeftIndepSpeedup.spec** (exists): Compressed OCA simulation is exact
2. **LeftIndepToRegular.spec** (exists): OCA ↔ CA conversion
3. **mirrorConfigCA.spec_interior** (exists): Mirror simulation is exact in interior
4. **exp_middle_two_stage_advice** (exists): Marker advice is two-stage
5. **two_stage_is_rt_closed** (exists): Two-stage advice is RT-closed

All these theorems already exist in the codebase!

---

## What Remains to Formalize

1. **compressed_embed definition:** The specific embedding function for our construction

2. **Boundary handling:** Show that interior conditions of spec_interior are satisfied

3. **Time/position arithmetic:** Verify the calculations match for all cases

4. **Advice application:** Combine marker advice with compressed config

5. **Final composition:** Chain all the constructions together

---

## Concrete Example Verification (n=5, m=8)

Original: OCA C on "xxxxxxxxabcde" (length 13)
- Accepts at (t=24, pos=-12)

Compressed config on input "abcde":
```
pos:  -4     -3     -2     -1   │  0    1    2    3    4
     ─────────────────────────────┼─────────────────────────
     #####  ##xxx  xxxxx  xxxxx │  a    b    c    d    e
     (5#)   (2#3x) (5x)   (5x)  │
```

Wait, m=8 x's = 2 compressed cells of 5x would be 10x, too many. Need m/4 = 2 cells but with only 4 x's each? Or the compression factor is different...

Actually with k=5, we get (k-1)=4 extra time per cell. So m x's need m/4 compressed cells to match the 4x time savings.

Let me recalculate: m=8, so m/4=2 compressed x-cells. Each cell holds 5 values. Total x-values stored: 2×5 = 10, but we only need 8. The extra 2 are #'s at the boundary.

```
pos:  -3     -2     -1   │  0    1    2    3    4
     ────────────────────┼─────────────────────────
     #####  ##xxx  xxxxx │  a    b    c    d    e
     (5#)   (2#3x) (5x)  │ single cells
```

Hmm, this still doesn't perfectly account for 8 x's with 2 cells... Let me check brainstorm.md again.

From brainstorm.md n=5 diagram:
- pos 7 has `x₀ x₀ x₀ x₀ x₀` (5 x's)
- pos 6 has `#₀ #₀ x₀ x₀ x₀` (2# + 3x)
- Total x's: 5 + 3 = 8 ✓

So cell at d=1 (pos 7 in their coords, or pos -1 in ours): 5 x's
Cell at d=2 (pos 6 in their coords, or pos -2 in ours): 3 x's + 2 #'s

The x/# boundary falls within a cell, which is fine — advice marks which positions have x vs #.

---

## Final Notes

The construction chains together existing machinery:
- OCA k-step speedup for compression
- OCA ↔ CA conversion
- Mirror config CA for tracking negative positions
- Two-stage advice for boundary marking

All pieces exist; the main work is:
1. Defining the combined embed function
2. Showing time/position calculations work out
3. Handling boundary cases

The brainstorm.md diagrams serve as concrete test cases.
