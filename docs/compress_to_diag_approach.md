# Compress-to-Diagonal Construction: Thesis Approach and Lean Proof Strategy

## Overview

This document describes the 3-step diagonal compression pipeline from the bachelor's thesis (Chapter 3 "Linksunabhängige Zellularautomaten" and Chapter 4 "Speedup-Konstruktionen"), lists the specifications we have formalized in Lean, and outlines a proof strategy for the `g₁`/`g₂` specs in Lean.

## Warning: 0-Indexed vs 1-Indexed Conventions

**Critical difference:**
- **Thesis**: Words and configurations are 1-indexed. Position 1 is the first character.
  - `[w]_p` undefined for `p ≤ 0` or `p > |w|`, returns `#` (border)
- **Lean**: Words and configurations are 0-indexed. Position 0 is the first character.
  - `embed_word w i` returns `some w[i]` for `0 ≤ i < w.length`, else `none` (border)

**Conversion**: `thesis_position = lean_position + 1`

When translating theorems:
- Thesis "position 1" = Lean "position 0"
- Thesis `Δ_C^t(c)_1` = Lean `C.nextt c t 0`

---

## Thesis Pipeline: CAgfSpeedup (Satz 3.9)

The thesis constructs three transformations to achieve diagonal compression:

### Step 1: zellautoZuLinksunabhaengig (Regular → Left-Independent)

**Reference**: Satz in Chapter 3

Given CA `C = (Q, δ)`, construct left-independent `C' = (Q', δ')` where:
- `Q' = Q ∪ Q×Q`
- `δ'(_, b, c) = (b, c)` for `b, c ∈ Q`
- `δ'(_, (b₁,b₂), (c₁,c₂)) = δ(b₁, b₂, c₂)` for pairs

**Spec** (thesis, 1-indexed):
```
Δ^t_{C'}(c)_i = 
  - Δ^{t/2}_C(c)_{i+t/2}           if t even
  - (Δ^{(t-1)/2}_C(c)_{i+(t-1)/2}, 
     Δ^{(t-1)/2}_C(c)_{i+(t+1)/2}) if t odd
```

**Lean**: `RegularToLeftIndep` in [regular_to_left_indep.lean](../CellularAutomatas/proofs/regular_to_left_indep.lean)

```lean
theorem spec_even (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c (2*t) i = .single (e.C_orig.comp c t (i + t))

theorem spec_odd (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c (2*t + 1) i = .pair (e.C_orig.comp c t (i + t)) 
                                   (e.C_orig.comp c t (i + t + 1))
```

### Step 2: linksunabhaengigSpeedup (Left-Independent → k-Compressed Left-Independent)

**Reference**: Lemma linksunabhaengigSpeedup in Chapter 4

Given left-independent CA `C` with passive/initial border `#`, construct left-independent `C'` where each cell stores a k-tuple of states from the diagonal.

**Spec** (thesis, 1-indexed, for `i ≤ 0`):
```
Δ^t_{C'}(c)_i = w ∈ Q^k where w_j := Δ^{t + i - ki + k - j}_C(c)_{ki - k + j}
```

For `k = 3`:
```
Δ^t_{C'}(c)_i = (Δ^{t-2i+2}_C(c)_{3i-2}, Δ^{t-2i+1}_C(c)_{3i-1}, Δ^{t-2i}_C(c)_{3i})
```

**Lean φ/ψ formulas** (0-indexed components, `j ∈ Fin k`):
```
ψ(i, j) = k·i + j          -- position mapping
φ(t, i, j) = t - (k-1)·i - j  -- time mapping
```

**Lean**: `LeftIndepSpeedupQuiescent` in [left_indep_speedup.lean](../CellularAutomatas/proofs/left_indep_speedup.lean)

```lean
theorem spec (w : Word e.α) (i : ℤ) (hi : i < 0) (t : ℕ) (j : Fin e.k) :
    (e.C.comp (embed_word w) t i) j =
    e.C_orig.comp (embed_word w) (t - ((e.k - 1) * i) - j).toNat (e.k * i + j)
```

**Border requirement**: The thesis requires `#` to be passive and initial. In Lean, we use `PassiveBorderLeftIndep` to transform any left-independent CA to one with a truly passive border before applying the speedup.

### Step 3: linksunabhaengigZuZellauto (Left-Independent → Regular)

**Reference**: Satz in Chapter 3

Given left-independent CA `C = (Q, δ)`, construct regular `C' = (Q, δ')` where:
- `δ'(a, b, c) = δ(q, δ(q, a, b), δ(q, b, c))` for any fixed `q`

**Spec** (thesis, 1-indexed):
```
Δ^t_{C'}(c)_i = Δ^{2t}_C(c)_{i-t}
```

**Lean**: `LeftIndepToRegular` in [left_indep_to_regular.lean](../CellularAutomatas/proofs/left_indep_to_regular.lean)

```lean
theorem spec (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c t i = e.C_orig.comp c (2 * t) (i - t)
```

---

## Combined Pipeline: CAgfSpeedup

Composing the three steps with `k = 3`:

```
C (original) 
  → C' (left-independent, 2× slower, shifts left)
  → C'' (3-compressed left-independent)  
  → C''' (regular, 2× faster, shifts right)
```

### Thesis Extraction Functions (1-indexed)

The thesis defines `g₁` and `g₂` to extract the diagonal trace from C''' states:

**Theorem (Satz CAgfSpeedup, 1-indexed):**
```
g₁(Δ_{C'''}^{2p-1}(c)_p) = Δ_C^{3p-2}(c)_1        for p ≥ 1
g₂(Δ_{C'''}^{2p}(c)_{p+1}) = (Δ_C^{3p-1}(c)_1, Δ_C^{3p}(c)_1)  for p ≥ 1
```

The thesis defines:
- `g₁(q) := q₃` (third component of the k=3 tuple)
- `g₂(q) := ((q₂)₁, q₁)` where `q₂` is a pair from step 1 and `q₁` is a single

### Conversion to Lean (0-indexed)

Substitute `p_thesis = p_lean + 1` (so `p_lean ≥ 0` corresponds to `p_thesis ≥ 1`):

**Lean-indexed theorems:**
```
g₁(Δ_{C'''}^{2p+1}(c)_{p+1}) = Δ_C^{3p+1}(c)_0     for p ≥ 0
g₂(Δ_{C'''}^{2p+2}(c)_{p+2}) = (Δ_C^{3p+2}(c)_0, Δ_C^{3p+3}(c)_0)  for p ≥ 0
```

---

## Coordinate Trace for g₁ Proof

Goal: Prove `g₁(C'''.nextt c (2p+1) (p+1)) = C_orig.nextt c (3p+1) 0`

### Step-by-step coordinate analysis (Lean 0-indexed):

**1. C''' → C'' via step3.spec:**
```
C'''.nextt c (2p+1) (p+1) = C''.nextt c (4p+2) ((p+1)-(2p+1))
                          = C''.nextt c (4p+2) (-p)
```

Position after step3: `i = (p+1) - (2p+1) = -p`
Time after step3: `t = 2·(2p+1) = 4p+2`

Note: `-p < 0` for `p > 0`, so we're in the compressed region!

**2. C'' component extraction via step2.spec:**

For `i = -p < 0`, time `t = 4p+2`, component `j`:
```
φ(4p+2, -p, j) = (4p+2) - (k-1)·(-p) - j = (4p+2) + 2p - j = 6p+2-j
ψ(-p, j) = 3·(-p) + j = -3p+j
```

For component `j = 0` (thesis `q₃`):
```
φ = 6p+2, ψ = -3p
```

So: `compr_at(C''.nextt c (4p+2) (-p), 0) = C'.nextt c (6p+2) (-3p)`

**3. C' → C'_raw via step1b (PassiveBorder):**

Need to verify `-3p ∈ WordConeLeftIndep w (6p+2)`:
- Cone condition: `-(6p+2) ≤ -3p < w.length`
- Left bound: `-6p-2 ≤ -3p` ⟺ `-2 ≤ 3p` ✓ (always true for `p ≥ 0`)
- Right bound: `-3p < w.length` ✓ (for `p ≥ 0`, need `w.length > 0`)

Inside the cone, `C' = C'_raw` by `PassiveBorderLeftIndep.spec`.

**4. C'_raw → C_orig via step1a (RegularToLeftIndep):**

At time `6p+2 = 2·(3p+1)` (even), position `-3p`:
```
C'_raw.comp c (6p+2) (-3p) = .single(C_orig.comp c (3p+1) ((-3p)+(3p+1)))
                            = .single(C_orig.comp c (3p+1) 1)  -- thesis position 1
                            = .single(C_orig.comp c (3p+1) 0)  -- lean position 0!
```

Wait, let me recalculate:
- Even time: `6p+2 = 2t` means `t = 3p+1`
- Position shift: `(-3p) + (3p+1) = 1` in thesis-indexed = `0` in Lean-indexed

**Verification**: The spec says `spec_even(c, t, i) = .single(comp c t (i+t))`:
- `i = -3p`, `t = 3p+1`
- `i + t = -3p + (3p+1) = 1`

But this is the Lean position! The thesis uses 1-indexed positions.

Actually, looking at the Lean spec more carefully:
```lean
theorem spec_even (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c (2*t) i = .single (e.C_orig.comp c t (i + t))
```

Here `i + t` is directly the Lean position. So if we want `C_orig.comp c (3p+1) 0`, we need `i + t = 0`.

From above: `i = -3p`, `t = 3p+1`, so `i + t = 1` ≠ 0.

**Issue**: The coordinate analysis doesn't quite work out! We get position 1, not 0.

### Resolution: Re-examining the pipeline

The issue is that the thesis formulas assume different conventions. Let me re-trace:

In the thesis Satz 3.9, the claim is:
```
g₁(Δ_{C'''}^{2p-1}(c)_p) = Δ_C^{3p-2}(c)_1
```

In 1-indexed conventions:
- Time: `2p-1` at C''', position `p`
- Result: time `3p-2` at C, position `1`

Converting to Lean (0-indexed positions only for the final position):
- If thesis position 1 = Lean position 0, then:
- `g₁(Δ_{C'''}^{2p-1}(c)_{p}) = Δ_C^{3p-2}(c)_0`

With `p_lean = p_thesis - 1` (so `p_thesis = 1` maps to `p_lean = 0`):
- Time at C''': `2(p_lean+1)-1 = 2p_lean+1`
- Position at C''': `p_lean + 1` (Lean already uses 0-indexed positions in ℤ, so this is position (p+1) in Lean)
- Time at C: `3(p_lean+1)-2 = 3p_lean+1`

So for `p ≥ 0` (Lean):
```
g₁(C'''.nextt c (2p+1) (p+1)) should give C.nextt c (3p+1) 0
```

But from our trace we got position 1 (in the Lean sense), not 0.

### The missing piece: Component index confusion

Looking at the thesis more carefully for `k = 3`:
```
Δ^t_{C''}(c)_i = (Δ^{t-2i+2}_{C'}(c)_{3i-2}, Δ^{t-2i+1}_{C'}(c)_{3i-1}, Δ^{t-2i}_{C'}(c)_{3i})
```

Components are numbered 1, 2, 3 in the thesis. The thesis says `g₁(q) := q₃`.

In Lean, we use 0-indexed components: `Fin 3` with values 0, 1, 2.

**Mapping**:
- Thesis component 1 = Lean `j = 2`
- Thesis component 2 = Lean `j = 1`
- Thesis component 3 = Lean `j = 0`

This is because the Lean formula is `φ(t, i, j) = t - (k-1)i - j`:
- For `j = 0`: largest φ value (most steps of C')
- For `j = k-1`: smallest φ value

Let me re-verify:
- Thesis component 1 has time `t - 2i` (for `k = 3`, factor `k-1 = 2`)
- Thesis component 3 has time `t - 2i + 2`

Lean formula: `φ(t, i, j) = t - 2i - j`
- `j = 0`: `φ = t - 2i`
- `j = 2`: `φ = t - 2i - 2`

Wait, this seems backwards from the thesis! The thesis has:
- Component 1 → time `t - 2i` → Lean `j = 0`? No...

Let me look at the actual definitions more carefully. The thesis says for component `j ∈ {1, 2, 3}`:
```
w_j = Δ^{t + i - 3i + 3 - j}_{C'}(c)_{3i - 3 + j} = Δ^{t - 2i + 3 - j}_{C'}(c)_{3i - 3 + j}
```

For `j = 1`: time `t - 2i + 2`, position `3i - 2`
For `j = 2`: time `t - 2i + 1`, position `3i - 1`
For `j = 3`: time `t - 2i + 0`, position `3i`

Lean uses 0-indexed `j ∈ {0, 1, 2}`:
```
φ(t, i, j) = t - 2i - j    (for k=3)
ψ(i, j) = 3i + j
```

For `j = 0`: time `t - 2i`, position `3i`
For `j = 1`: time `t - 2i - 1`, position `3i + 1`
For `j = 2`: time `t - 2i - 2`, position `3i + 2`

**Mapping conclusion**:
- Thesis `(t-2i+2, 3i-2)` with component 1 → Lean needs `φ = t-2i+2`, but `φ = t-2i-j`
- The formulas don't directly match!

The issue: the thesis and Lean use different orderings/conventions for the tuple components.

Looking at [left_indep_speedup.lean](../CellularAutomatas/proofs/left_indep_speedup.lean) line 247-248:
```lean
def ψ (i : ℤ) (j : Fin e.k) : ℤ := e.k * i + j
def φ (t : ℕ) (i : ℤ) (j : Fin e.k) : ℤ := t - (e.k - 1 : ℕ) * i - j
```

For `k = 3, i = -1, j = 2`:
- `ψ(-1, 2) = -3 + 2 = -1`
- `φ(t, -1, 2) = t - 2·(-1) - 2 = t + 2 - 2 = t`

This is checking out: the "last" component (j=2) at position -1 after t steps maps to position -1 after t steps of C'.

---

## Proof Strategy for g₁/g₂ in Lean

Given the complexity of coordinate tracking, here's a systematic approach:

### 1. Define the extraction functions properly

In [compress_to_diag.lean](../CellularAutomatas/proofs/compress_to_diag.lean), we need to:

```lean
/-- Extract function g₁: thesis q₃ = Lean j=0 after unwrapping passive border and step1a -/
def g₁ (q : e.Q''') : e.C_orig.Q :=
  let q_compr := e.step2.compr_at q ⟨0, by simp⟩  -- component 0
  e.extract_state q_compr  -- unwrap PassiveBorder.Q' → RegularToLeftIndep.Q' → Q
```

But wait, the current definition has `j=0`. Based on the analysis, we need to verify which component corresponds to the thesis `q₃`.

### 2. Verify coordinate arithmetic in a separate lemma

Create helper lemmas that verify:
```lean
lemma g1_coordinate_trace (w : Word e.α) (p : ℕ) (hp : p > 0) :
  let t''' := 2*p + 1
  let i''' := (p : ℤ) + 1
  let t'' := 4*p + 2  -- after step3
  let i'' := -(p : ℤ)  -- after step3
  let j := (0 : Fin 3)  -- component to extract
  let φ_val := e.step2.φ t'' i'' j  -- = 6p + 2
  let ψ_val := e.step2.ψ i'' j      -- = -3p
  let t' := φ_val.toNat  -- time at C'
  let i' := ψ_val         -- position at C'
  -- Now check parity and apply step1a spec
  ...
```

### 3. Use the composition of specs

The proof should chain:
1. `step3.spec`: `C'''.nextt c t i = C''.nextt c (2t) (i-t)`
2. `step2.spec_nextt`: Extract component via φ/ψ
3. `step1b.spec`: Inside cone → identity with passive border adjustment
4. `step1a.spec_even/spec_odd`: Even/odd time determines single/pair

### 4. Handle the passive border carefully

The key insight is that `PassiveBorderLeftIndep` wraps the states:
- `C'.Q' = border | state(s, tracked_border)`
- For positions inside the cone, `spec_internal` shows the state is `state(C'_raw.nextt ..., δδt border t)`

We need an `extract_state` function that:
1. Unwraps `PassiveBorderLeftIndep.Q'` to get the inner state
2. Handles `RegularToLeftIndep.Q'` to get either the single or pair element

### 5. Verify the cone membership

For the passive border spec to apply, we need to verify that the target position is inside `WordConeLeftIndep w t`:
```lean
lemma g1_position_in_cone (w : Word e.α) (hw : w.length > 0) (p : ℕ) (hp : p > 0) :
    (-3*p : ℤ) ∈ WordConeLeftIndep w (6*p + 2) := by
  rw [WordConeLeftIndep_mem]
  constructor
  · -- -(6p+2) ≤ -3p ⟺ -6p-2 ≤ -3p ⟺ -2 ≤ 3p ✓
    omega
  · -- -3p < w.length: for p > 0, this is -3p < 0 < w.length ✓
    omega
```

---

## Summary of Lean Specs Available

| Transformation | File | Key Theorem |
|----------------|------|-------------|
| Regular → LeftIndep | `regular_to_left_indep.lean` | `spec_even`, `spec_odd` |
| LeftIndep → k-Compressed | `left_indep_speedup.lean` | `spec`, `spec_nextt` |
| LeftIndep → Regular | `left_indep_to_regular.lean` | `spec`, `spec_nextt` |
| Passive Border | `passive_border.lean` | `spec`, `spec_internal` |

The full composition is in `compress_to_diag.lean` with `CAgfSpeedup` and the `g₁`/`g₂`/`f` extraction functions, but the main specs (`spec_g₁`, `spec_g₂`, `spec_f`) currently have `sorry` placeholders.

## Next Steps

1. Fix the component indexing in `g₁`/`g₂` definitions to match thesis semantics
2. Write helper lemmas for coordinate arithmetic
3. Verify cone membership conditions
4. Chain the specs with careful attention to even/odd time cases
5. Complete the `spec_g₁` proof as a template for the others
