# Compress-to-Diagonal Construction: Thesis Approach and Lean Proof Strategy

## Overview

This document describes the 3-step diagonal compression pipeline from the bachelor's thesis (Chapter 3 "Linksunabhängige Zellularautomaten" and Chapter 4 "Speedup-Konstruktionen"), lists the specifications we have formalized in Lean, and outlines a proof strategy for the $g_1$/$g_2$ specs in Lean.

## Warning: 0-Indexed vs 1-Indexed Conventions

**Critical difference for word embedding:**
- **Thesis**: Words are embedded at positions $1, 2, \ldots, |w|$.
  - $[w]_p = w_p$ for $1 \leq p \leq |w|$, else $\#$ (border)
- **Lean**: Words are embedded at positions $0, 1, \ldots, |w|-1$.
  - `embed_word w i` returns `some w[i]` for $0 \leq i < \text{w.length}$, else `none` (border)

**Important**: The transformation specs (steps 1-3) are stated for **arbitrary configuration positions** $i \in \mathbb{Z}$. These specs are identical in thesis and Lean—no index conversion needed.

The index conversion only matters when reading at **word-relative positions**:
- Thesis "position 1" (first char) = Lean "position 0" (first char)
- Thesis $\Delta_C^t(c)_1$ = Lean `C.nextt c t 0`

---

## Thesis Pipeline: CAgfSpeedup (Satz 3.9)

The thesis constructs three transformations to achieve diagonal compression:

### Step 1: zellautoZuLinksunabhaengig (Regular → Left-Independent)

**Reference**: Satz in Chapter 3

Given CA $C = (Q, \delta)$, construct left-independent $C' = (Q', \delta')$ where:
- $Q' = Q \cup Q \times Q$
- $\delta'(\cdot, b, c) = (b, c)$ for $b, c \in Q$
- $\delta'(\cdot, (b_1, b_2), (c_1, c_2)) = \delta(b_1, b_2, c_2)$ for pairs

**Spec** (for any $i \in \mathbb{Z}$, identical in thesis and Lean):
$$
\Delta_{C'}^{t}(c)_i =
\begin{cases}
\Delta_C^{t/2}(c)_{i+t/2} & \text{if } t \text{ even} \\
\left(\Delta_C^{(t-1)/2}(c)_{i+(t-1)/2}, \Delta_C^{(t-1)/2}(c)_{i+(t+1)/2}\right) & \text{if } t \text{ odd}
\end{cases}
$$

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

Given left-independent CA $C$ with passive/initial border $\#$, construct left-independent $C'$ where each cell stores a k-tuple of states from the diagonal.

**Spec** (thesis uses 1-indexed components $j \in \{1, \ldots, k\}$, for $i \leq 0$):
$$
\Delta_{C'}^{t}(c)_i = w \in Q^k \text{ where } w_j := \Delta^{t + i - ki + k - j}_{C}(c)_{ki - k + j}
$$

For $k = 3$:
$$
\Delta_{C'}^{t}(c)_i = \left( \Delta^{t-2i+2}_{C}(c)_{3i-2}, \Delta^{t-2i+1}_{C}(c)_{3i-1}, \Delta^{t-2i}_{C}(c)_{3i} \right)
$$

**Lean formulas** (0-indexed components $j \in \{0, \ldots, k-1\}$):
$$
\psi(i, j) = k \cdot i + j \quad \text{(position mapping)}
$$
$$
\varphi(t, i, j) = t - (k-1) \cdot i - j \quad \text{(time mapping)}
$$

**Lean**: `LeftIndepSpeedupQuiescent` in [left_indep_speedup.lean](../CellularAutomatas/proofs/left_indep_speedup.lean)

```lean
theorem spec (w : Word e.α) (i : ℤ) (hi : i < 0) (t : ℕ) (j : Fin e.k) :
    (e.C.comp (embed_word w) t i) j =
    e.C_orig.comp (embed_word w) (t - ((e.k - 1) * i) - j).toNat (e.k * i + j)
```

**Border requirement**: The thesis requires $\#$ to be passive and initial. In Lean, we use `PassiveBorderLeftIndep` to transform any left-independent CA to one with a truly passive border before applying the speedup.

### Step 3: linksunabhaengigZuZellauto (Left-Independent → Regular)

**Reference**: Satz in Chapter 3

Given left-independent CA $C = (Q, \delta)$, construct regular $C' = (Q, \delta')$ where:
$$
\delta'(a, b, c) = \delta(q, \delta(q, a, b), \delta(q, b, c))
$$
for any fixed $q \in Q$.

**Spec** (for any $i \in \mathbb{Z}$, identical in thesis and Lean):
$$
\Delta^t_{C'}(c)_{i} = \Delta^{2t}_C(c)_{i-t}
$$

**Lean**: `LeftIndepToRegular` in [left_indep_to_regular.lean](../CellularAutomatas/proofs/left_indep_to_regular.lean)

```lean
theorem spec (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c t i = e.C_orig.comp c (2 * t) (i - t)
```

---

## Combined Pipeline: CAgfSpeedup

Composing the three steps with $k = 3$:

$$
C \xrightarrow{\text{step1}} C' \xrightarrow{\text{step2}} C'' \xrightarrow{\text{step3}} C'''
$$

- $C$: original CA
- $C'$: left-independent, 2× slower, shifts left
- $C''$: 3-compressed left-independent  
- $C'''$: regular, 2× faster, shifts right

### Thesis Extraction Functions (1-indexed)

The thesis defines $g_1$ and $g_2$ to extract the diagonal trace from $C'''$ states:

**Theorem (Satz CAgfSpeedup, 1-indexed):**
$$
g_1\left(\Delta_{C'''}^{2p-1}(c)_p\right) = \Delta_C^{3p-2}(c)_1 \quad \text{for } p \geq 1
$$
$$
g_2\left(\Delta_{C'''}^{2p}(c)_{p+1}\right) = \left(\Delta_C^{3p-1}(c)_1, \Delta_C^{3p}(c)_1\right) \quad \text{for } p \geq 1
$$

The thesis defines:
- $g_1(q) := q_3$ (third component of the $k=3$ tuple)
- $g_2(q) := ((q_2)_1, q_1)$ where $q_2$ is a pair from step 1 and $q_1$ is a single

### Conversion to Lean (0-indexed)

**Step 1:** Convert all positional subscripts: every `_idx` in the thesis becomes `_{idx-1}` in Lean.
- Position `_p` → `_{p-1}`
- Position `_{p+1}` → `_p`
- Position `_1` → `_0`

**Step 2:** Variable substitution $p \to p+1$ to get $p \geq 0$ instead of $p \geq 1$.

**Derivation for $g_1$:**
1. Thesis: $g_1(\Delta_{C'''}^{2p-1}(c)_p) = \Delta_C^{3p-2}(c)_1$ for $p \geq 1$
2. After position conversion: $g_1(\Delta_{C'''}^{2p-1}(c)_{p-1}) = \Delta_C^{3p-2}(c)_0$ for $p \geq 1$
3. Substitute $p \to p+1$: $g_1(\Delta_{C'''}^{2p+1}(c)_{p}) = \Delta_C^{3p+1}(c)_0$ for $p \geq 0$

**Derivation for $g_2$:**
1. Thesis: $g_2(\Delta_{C'''}^{2p}(c)_{p+1}) = (\Delta_C^{3p-1}(c)_1, \Delta_C^{3p}(c)_1)$ for $p \geq 1$
2. After position conversion: $g_2(\Delta_{C'''}^{2p}(c)_{p}) = (\Delta_C^{3p-1}(c)_0, \Delta_C^{3p}(c)_0)$ for $p \geq 1$
3. Substitute $p \to p+1$: $g_2(\Delta_{C'''}^{2p+2}(c)_{p+1}) = (\Delta_C^{3p+2}(c)_0, \Delta_C^{3p+3}(c)_0)$ for $p \geq 0$

**Lean-indexed theorems:**
$$
g_1\left(\Delta_{C'''}^{2p+1}(c)_{p}\right) = \Delta_C^{3p+1}(c)_0 \quad \text{for } p \geq 0
$$
$$
g_2\left(\Delta_{C'''}^{2p+2}(c)_{p+1}\right) = \left(\Delta_C^{3p+2}(c)_0, \Delta_C^{3p+3}(c)_0\right) \quad \text{for } p \geq 0
$$

---

## Coordinate Trace for $g_1$ Proof

Goal: Prove $g_1(C'''\text{.nextt } c\; (2p+1)\; p) = C_{\text{orig}}\text{.nextt } c\; (3p+1)\; 0$ for $p \geq 0$

### Step-by-step coordinate analysis (Lean 0-indexed):

**1. $C''' \to C''$ via step3.spec:**
$$
C'''\text{.nextt } c\; (2p+1)\; p = C''\text{.nextt } c\; (4p+2)\; (p-(2p+1)) = C''\text{.nextt } c\; (4p+2)\; (-p-1)
$$
Position after step3: $i = p - (2p+1) = -p-1$  
Time after step3: $t = 2 \cdot (2p+1) = 4p+2$

**2. $C''$ component extraction via step2.spec:**

For $i = -p-1 < 0$, time $t = 4p+2$, component $j$:
$$
\varphi(4p+2, -p-1, j) = (4p+2) - 2 \cdot (-p-1) - j = 6p+4-j
$$
$$
\psi(-p-1, j) = 3 \cdot (-p-1) + j = -3p-3+j
$$

For component **$j = 2$**:
$$
\varphi = 6p+2 \quad \text{(even)}, \quad \psi = -3p-1
$$

**3. $C' \to C'_{\text{raw}}$ via step1b (PassiveBorder):**

Need to verify $-3p-1 \in \text{WordConeLeftIndep } w\; (6p+2)$:
- Cone condition: $-(6p+2) \leq -3p-1 < |w|$
- Left bound: $-6p-2 \leq -3p-1 \Leftrightarrow -1 \leq 3p+1$ ✓ (always true for $p \geq 0$)
- Right bound: $-3p-1 < 0 < |w|$ ✓ (since $p \ge 0$).

**4. $C'_{\text{raw}} \to C_{\text{orig}}$ via step1a (RegularToLeftIndep):**

At even time $6p+2 = 2 \cdot (3p+1)$:
$$
\text{Pos} = \psi + \frac{\varphi}{2} = (-3p-1) + (3p+1) = 0
$$

**Result:** Position 0 at time $3p+1$. This matches the target!

**Conclusion**:
- $g_1$ must use **$j=2$**.
- $g_2$ (targeting time $3p+2, 3p+3$) acts similarly.
  - At $t=2p+2$, $C'''$ pos $p+1 \to i=-p-1$.
  - $\varphi \approx 6p+6$.
  - Time $3p+2 \iff$ Odd step from $\varphi=6p+5 \implies j=1$.
     - $\psi = -3p-2$. Pos: $-3p-2+(3p+2)=0$.
  - Time $3p+3 \iff$ Even step from $\varphi=6p+6 \implies j=0$.
     - $\psi = -3p-3$. Pos: $-3p-3+(3p+3)=0$.

So $g_2$ uses $j=1$ and $j=0$.

---

## Proof Strategy for $g_1$/$g_2$ in Lean

### 1. Correct Component Definitions

Based on the resolution:

- **$g_1$**: Extracts component $j=2$.
- **$g_2$**: Extracts components $j=1$ and $j=0$.

```lean
/-- Extract function g₁: j=2 -/
def g₁ (q : e.Q''') : e.C_orig.Q :=
  let q_compr := e.step2.compr_at q ⟨2, by simp⟩
  e.extract_state q_compr

/-- Extract function g₂: j=1 and j=0 -/
def g₂ (q : e.Q''') : e.C_orig.Q × e.C_orig.Q :=
  let q1' := e.step2.compr_at q ⟨1, by simp⟩
  let q0' := e.step2.compr_at q ⟨0, by simp⟩
  (e.extract_state q1', e.extract_state q0')
```

### 3. Verify coordinate arithmetic with helper lemmas

The coordinate trace above confirms that $j=2$ targets Position 0 correctly. We should formalize these arithmetic steps as helper lemmas (e.g., `calc` blocks) inside the proof.

### 4. Chain the specs with cone membership verification

The proof should chain:
1. `step3.spec`: $C'''\text{.nextt } c\; t\; i = C''\text{.nextt } c\; (2t)\; (i-t)$
2. `step2.spec_nextt`: Extract component via $\varphi$/$\psi$
3. `step1b.spec`: Inside cone → identity with passive border adjustment
4. `step1a.spec_even/spec_odd`: Even/odd time determines single/pair

```lean
lemma position_in_cone (w : Word e.α) (hw : w.length > 0) (p : ℕ) :
    (-3*(p:ℤ)-3) ∈ WordConeLeftIndep w (6*p + 4) := by
  rw [WordConeLeftIndep_mem]
  constructor
  · omega  -- -(6p+4) ≤ -3p-3
  · omega  -- -3p-3 < w.length (since -3p-3 < 0 < w.length)
```

---

## Summary of Lean Specs Available

| Transformation | File | Key Theorem |
|----------------|------|-------------|
| Regular → LeftIndep | `regular_to_left_indep.lean` | `spec_even`, `spec_odd` |
| LeftIndep → k-Compressed | `left_indep_speedup.lean` | `spec`, `spec_nextt` |
| LeftIndep → Regular | `left_indep_to_regular.lean` | `spec`, `spec_nextt` |
| Passive Border | `passive_border.lean` | `spec`, `spec_internal` |

The full composition is in `compress_to_diag.lean` with `CAgfSpeedup` and the $g_1$/$g_2$/$f$ extraction functions, but the main specs (`spec_g₁`, `spec_g₂`, `spec_f`) currently have `sorry` placeholders.

## Next Steps

1. Fix the component indexing in $g_1$/$g_2$ definitions to match thesis semantics
2. Write helper lemmas for coordinate arithmetic
3. Verify cone membership conditions
4. Chain the specs with careful attention to even/odd time cases
5. Complete the `spec_g₁` proof as a template for the others
