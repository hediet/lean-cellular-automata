# Proof Pipeline: $L_x(L) \in \mathrm{CA(RT)} \implies L \in \mathrm{CA(RT)}$

This document traces the complete transformation chain from the hypothesis to the conclusion, making each step's input/output explicit.

---

## Notation Reference

| Notation | Meaning |
|----------|---------|
| $\langle w \rangle$ | Standard word embedding: $w$ at positions $0, \ldots, n-1$; $\#$ elsewhere |
| $[v \mid w]$ | Shifted embedding: $w$ at $0, \ldots, n-1$; $v$ at $-1, \ldots, -\|v\|$; $\#$ elsewhere |
| $\mathsf{compress}_k(c)$ | Compress negative positions by factor $k$: position $i \ge 0$ → Single$(c(i))$; position $i < 0$ → Spatial$(j \mapsto c(k \cdot i + j))$ |
| $\mathsf{Fold}(c)$ | Fold bi-infinite config: position $i \ge 0$ → $(c(i), c(-i-1))$; position $i < 0$ → border |
| $\mathsf{BorderedConfig}(b_1, v, w, b_2)$ | $w$ at $[0, n)$; $v$ at $[-\|v\|, 0)$; $b_2$ at $\ge n$; $b_1$ at $< -\|v\|$ |
| $\langle w \rangle_{(b_1, b_2)}$ | Shorthand for $\mathsf{BorderedConfig}(b_1, [], w, b_2)$: $w$ at $[0,n)$, $b_2$ at $\ge n$, $b_1$ at $< 0$ |

---

## The Pipeline

**Given:** $L_x(L) \in \mathrm{CA(RT)}$ via CA $C$.

**Goal:** Construct CA $C'$ such that $C'$ accepts $\langle w \rangle$ at $(n-1, 0)$ iff $w \in L$.

---

### Step 0: Hypothesis

**CA:** $C$ (arbitrary)

**Input:** $\langle x^m w \rangle$ where $m = 2^{\lceil \log_2 n \rceil}$

**Acceptance:** $(m+n-1, 0)$

**Statement:**
> $C$ accepts $\langle x^m w \rangle$ at $(m+n-1, 0)$ $\iff$ $w \in L$

---

### Step 1: Regular → Left-Independent (Lemma 1)

**Construction:** `result_regular_to_left_indep`

**Transformation:**
> Given CA $C$, there exists left-independent CA $C_1$ such that:
> $$C_1.\mathsf{comp}(c, 2t, i) = C.\mathsf{comp}(c, t, i+t)$$

**Application with** $t = m+n-1$, $i = -(m+n-1)$:

**CA:** $C_1$ (left-independent)

**Input:** $\langle x^m w \rangle$ (same configuration)

**Acceptance:** $(2(m+n-1), -(m+n-1))$

**Statement:**
> $C_1$ accepts $\langle x^m w \rangle$ at $(2(m+n-1), -(m+n-1))$ $\iff$ $w \in L$

---

### Step 2: Shift (Lemma 2)

**Construction:** Translation invariance

**Transformation:**
> For any CA $C$, if $c' = c \circ (+m)$ (i.e., $c'(i) = c(i+m)$), then:
> $$C.\mathsf{comp}(c', t, i) = C.\mathsf{comp}(c, t, i+m)$$

**Observation:** $[x^m \mid w](i) = \langle x^m w \rangle(i + m)$

Specifically:
- $\langle x^m w \rangle(i) = x$ for $0 \le i < m$, $w_{i-m}$ for $m \le i < m+n$, $\#$ elsewhere
- $[x^m \mid w](i) = w_i$ for $0 \le i < n$, $x$ for $-m \le i < 0$, $\#$ elsewhere

**Application with** $i + m = -(m+n-1)$, i.e., $i = -(2m+n-1)$:

**CA:** $C_1$ (left-independent, unchanged)

**Input:** $[x^m \mid w]$

**Acceptance:** $(2(m+n-1), -(2m+n-1))$

**Statement:**
> $C_1$ accepts $[x^m \mid w]$ at $(2(m+n-1), -(2m+n-1))$ $\iff$ $w \in L$

---

### Step 3: Speedup/Compress (Lemma 9)

**Construction:** `LeftIndepSpeedupConfig` with $k = 5$

**Transformation:**
> Given left-independent CA $C$ with compression factor $k$, there exists left-independent CA $C'$ over mixed state space $Q' = \mathsf{Single}(Q) \mid \mathsf{Spatial}(Q^k) \mid \mathsf{Diagonal}(Q^k)$ such that:
>
> For $i < 0$, $t \ge -i$ (diagonal regime):
> $$C'.\mathsf{comp}(\mathsf{compress}_k(c), t, i)(j) = C.\mathsf{comp}(c, (t - (k-1) \cdot i - j), k \cdot i + j)$$

**Definition of compressed config:**
$$\mathsf{compress}_5([x^m \mid w])(i) = \begin{cases}
\mathsf{Single}([x^m \mid w](i)) & \text{if } i \ge 0 \\
\mathsf{Spatial}(j \mapsto [x^m \mid w](5i + j)) & \text{if } i < 0
\end{cases}$$

**Explicit form for** $i \ge 0$:
$$\mathsf{compress}_5([x^m \mid w])(i) = \begin{cases}
\mathsf{Single}(w_i) & \text{if } 0 \le i < n \\
\mathsf{Single}(\#) & \text{if } i \ge n
\end{cases}$$

**Explicit form for** $i < 0$ (compressed cell at position $-d$ for $d \ge 1$):

Packs original positions $\{-5d, -5d+1, -5d+2, -5d+3, -5d+4\}$.
Content depends on which of these fall in $[-m, 0)$ (containing $x$) vs outside (containing $\#$).

**Finding the acceptance position:**

Original acceptance: $(2(m+n-1), -(2m+n-1))$

Set $d = \lceil (2m+n-1)/5 \rceil$ and $j = 5d - (2m+n-1)$.

The spec gives, at $t_0 = d + n - 1$:
$$C_2.\mathsf{comp}_j(\mathsf{compress}_5([x^m \mid w]), t_0, -d) = C_1.\mathsf{comp}([x^m \mid w], 2(m+n-1), -(2m+n-1))$$

**Lock-in mechanism:** (To be composed on top)

Since $d \le n-1$ (proven: $m \le 2(n-1)$ implies $2m+n-1 \le 5(n-1)$), the acceptance at $(-d, j)$ can propagate leftward to reach $-(n-1)$ by time $2(n-1)$.

**CA:** $C_2$ (left-independent over $Q'$)

**Input:** $\mathsf{compress}_5([x^m \mid w])$

**Acceptance:** $(2(n-1), -(n-1))$ after lock-in

**Statement:**
> $C_2$ accepts $\mathsf{compress}_5([x^m \mid w])$ at $(2(n-1), -(n-1))$ $\iff$ $w \in L$

---

### Step 4: Left-Independent → Regular (Lemma 4)

**Construction:** `result_left_indep_to_regular`

**Transformation:**
> Given left-independent CA $C$, there exists CA $C'$ such that:
> $$C'.\mathsf{comp}(c, t, i) = C.\mathsf{comp}(c, 2t, i - t)$$

**Application with** $t = n-1$, $i = 0$:

**CA:** $C_3$ (regular CA over $Q'$)

**Input:** $\mathsf{compress}_5([x^m \mid w])$

**Acceptance:** $(n-1, 0)$

**Statement:**
> $C_3$ accepts $\mathsf{compress}_5([x^m \mid w])$ at $(n-1, 0)$ $\iff$ $w \in L$

---

### Step 5: Fold (Lemma 8)

**Construction:** `foldCA` (generalized for mixed state space)

**Transformation:**
> Given CA $C$ over state space $Q$, there exists CA $C'$ over $\mathsf{Option}(Q \times Q)$ such that:
> $$C'.\mathsf{comp}(\mathsf{Fold}(c), t, i) = C.\mathsf{comp}(c, t, i) \quad \text{for } i \ge 0$$

where $\mathsf{Fold}(c)(i) = \begin{cases} \mathsf{some}(c(i), c(-i-1)) & i \ge 0 \\ \mathsf{none} & i < 0 \end{cases}$

**Unpacking the folded config:**

For $c = \mathsf{compress}_5([x^m \mid w])$, define the **advice word** $v_m$ of length $n$ where:
$$v_m[i] = \mathsf{Spatial}(j \mapsto [x^m \mid w](-5(i+1) + j))$$

This is the content of compressed cell $-(i+1)$, which packs original positions $\{-5(i+1), \ldots, -5(i+1)+4\}$.

The folded config is then a **bordered config**:
$$\mathsf{Fold}(\mathsf{compress}_5([x^m \mid w])) = [b_1 \mid [] \mid w \otimes v_m \mid b_2]$$

where:
- $w \otimes v_m$ is the **zipped word**: $(w \otimes v_m)[i] = (\mathsf{Single}(w_i), v_m[i])$
- $b_1 = \mathsf{none}$ (left border)
- $b_2 = (\mathsf{Single}(\#), \mathsf{Spatial}(\#^5))$ (right border)

**Explicit view:**
```
pos:   -2    -1   |  0                   1                   ...  n-1              | n        n+1    ...
      none  none  | (Sgl(w₀), v_m[0])   (Sgl(w₁), v_m[1])   ...  (Sgl(w_{n-1}), .) | b₂       b₂     ...
       └─ b₁ ─┘   └───────────────── w ⊗ v_m ─────────────────┘   └──── b₂ ────────┘
```

**CA:** $C_4$ (regular CA over $\mathsf{Option}(Q' \times Q')$)

**Input:** $[b_1 \mid [] \mid w \otimes v_m \mid b_2]$

**Acceptance:** $(n-1, 0)$

**Statement:**
> $C_4$ accepts $[b_1 \mid [] \mid w \otimes v_m \mid b_2]$ at $(n-1, 0)$ $\iff$ $w \in L$

---

### Step 6: Border Normalization (Lemma 7)

**Construction:** `borderNormalizeCA`

**Transformation:**
> Given CA $C$ and borders $b_1, b_2$, there exists CA $C'$ such that:
> $$C'.\mathsf{comp}(\langle u \rangle, t, i) = C.\mathsf{comp}([b_1 \mid [] \mid u \mid b_2], t, i)$$

**Application:** The CA $C_4$ runs on $[b_1 \mid [] \mid w \otimes v_m \mid b_2]$.

After border normalization, we get a CA that runs on the **standard embedding** $\langle w \otimes v_m \rangle$:
- Word $w \otimes v_m$ at positions $[0, n-1]$
- Standard $\#$ border elsewhere

**CA:** $C_5$ (regular CA)

**Input:** $\langle w \otimes v_m \rangle$ — word $w$ zipped with advice $v_m$

**Acceptance:** $(n-1, 0)$

**Statement:**
> $C_5$ accepts $\langle w \otimes v_m \rangle$ at $(n-1, 0)$ $\iff$ $w \in L$

---

### Step 7: Separate Word from Advice

The input $\langle w \otimes v_m \rangle$ is a word over the **augmented alphabet**:
$$\Sigma' = \Sigma \times Q'_{\mathsf{compressed}}$$

where $Q'_{\mathsf{compressed}} = \mathsf{Spatial}(\mathrm{Fin}\;5 \to Q)$.

**Advice function:** Define $\mathsf{Adv}_m : \Sigma^n \to (\Sigma')^n$ by:
$$\mathsf{Adv}_m(w)[i] = (w_i, v_m[i])$$

So: $\langle w \otimes v_m \rangle = \langle \mathsf{Adv}_m(w) \rangle$

**CA:** $C_5$ (unchanged)

**Input:** $\langle \mathsf{Adv}_m(w) \rangle$

**Acceptance:** $(n-1, 0)$

**Statement:**
> $C_5$ accepts $\langle \mathsf{Adv}_m(w) \rangle$ at $(n-1, 0)$ $\iff$ $w \in L$

---

### Step 8: Advice is Two-Stage (Lemma 6)

**The advice** $v_m[i]$ depends on $m = 2^{\lceil \log_2 n \rceil}$.

**Explicit formula:**
$$v_m[i](j) = [x^m \mid w](-5(i+1) + j) = \begin{cases} x & \text{if } 5(i+1) - j \le m \\ \# & \text{otherwise} \end{cases}$$

**Claim:** The function $w \mapsto \mathsf{Adv}_m(w)$ is a **two-stage advice**.

**Proof:**

*Stage 1 (CA-RT transducer):* Mark position $i$ iff $i+1$ is a power of 2.
- Marks: $\{0, 1, 3, 7, 15, \ldots\}$ (i.e., positions $2^k - 1$)
- The rightmost mark determines $m$: if $n \in (2^{k-1}, 2^k]$, then position $2^k - 1$ is marked, so $m = 2^k$

*Stage 2 (FST):* Right-to-left scan computing $v_m[i](j)$ for each $i$:
- Once $m$ is known from the marks, compute $5(i+1) - j \le m$ (arithmetic mod 5, compare to fixed $m$)

Both stages are realizable: Stage 1 by `exp_word_ca`, Stage 2 by a finite-state transducer.

---

### Step 9: Two-Stage Advice is RT-Closed (Lemma 6, cont.)

**Construction:** `result_two_stage_is_rt_closed`

**Transformation:**
> If $C$ is a CA(RT) and $f$ is a two-stage advice, then there exists CA $C'$ such that:
> $$C'\ \text{accepts}\ \langle w \rangle\ \text{at}\ (n-1, 0) \iff C\ \text{accepts}\ \langle f(w) \rangle\ \text{at}\ (n-1, 0)$$

**Application:** Apply to $C_5$ with the two-stage advice $\mathsf{Adv}_m$.

**CA:** $C' = C_6$ (final CA, no advice)

**Input:** $\langle w \rangle$ — standard word embedding

**Acceptance:** $(n-1, 0)$

**Statement:**
> $C'$ accepts $\langle w \rangle$ at $(n-1, 0)$ $\iff$ $w \in L$

**This completes the construction.** $\blacksquare$

---

## Summary Table

| Step | CA | Input Config | Acceptance Position | Key Transformation |
|------|-----|--------------|---------------------|-------------------|
| 0 | $C$ | $\langle x^m w \rangle$ | $(m+n-1, 0)$ | Hypothesis |
| 1 | $C_1$ (left-indep) | $\langle x^m w \rangle$ | $(2(m+n-1), -(m+n-1))$ | RegularToLeftIndep |
| 2 | $C_1$ | $[x^m \mid w]$ | $(2(m+n-1), -(2m+n-1))$ | Shift by $m$ |
| 3 | $C_2$ (left-indep, $Q'$) | $\mathsf{compress}_5([x^m \mid w])$ | $(2(n-1), -(n-1))$ | Speedup + Lock-in |
| 4 | $C_3$ ($Q'$) | $\mathsf{compress}_5([x^m \mid w])$ | $(n-1, 0)$ | LeftIndepToRegular |
| 5 | $C_4$ (folded) | $[b_1 \mid [] \mid w \otimes v_m \mid b_2]$ | $(n-1, 0)$ | Fold |
| 6 | $C_5$ (border) | $\langle w \otimes v_m \rangle$ | $(n-1, 0)$ | Border normalization |
| 7 | $C_5$ | $\langle \mathsf{Adv}_m(w) \rangle$ | $(n-1, 0)$ | Separate advice (notation) |
| 8 | — | — | — | Advice is two-stage |
| 9 | $C'$ | $\langle w \rangle$ | $(n-1, 0)$ | RT-closed advice |

---

## Formalization Status

| Step | Component | Status | Location |
|------|-----------|--------|----------|
| 1 | RegularToLeftIndep | ✓ Formalized | `results.lean` |
| 2 | Shift lemma | To formalize | Trivial |
| 3 | LeftIndepSpeedupConfig | ✓ Formalized | `speedup_left_independent_config.lean` |
| 3 | Lock-in mechanism | To formalize | — |
| 4 | LeftIndepToRegular | ✓ Formalized | `results.lean` |
| 5 | foldCA | ✓ Formalized | `basic_fold.lean` |
| 6 | borderNormalizeCA | ✓ Formalized | `basic_border_normalization.lean` |
| 8 | exp_word two-stage | ✓ Formalized | `exp_middle_two_stage.lean` |
| 9 | Two-stage ⟹ RT-closed | ✓ Formalized | `is_two_stage_of_rt_closed_and_causal.lean` |

---

## Appendix: Concrete Example ($n = 4$, $m = 4$)

**Original config** $[x^4 \mid w]$ for $w = abcd$:
```
pos: ... -8  -7  -6  -5 | -4  -3  -2  -1 |  0   1   2   3 |  4   5  ...
     ... #   #   #   # |  x   x   x   x |  a   b   c   d |  #   #  ...
```

**After compress** $\mathsf{compress}_5([x^4 \mid w])$:
```
pos:        -2               -1           |  0     1     2     3   |  4      ...
        Spatial(#####)  Spatial(#xxxx)    | Sgl(a) Sgl(b) Sgl(c) Sgl(d) | Sgl(#) ...
```

**After fold** $\mathsf{Fold}(\mathsf{compress}_5([x^4 \mid w]))$:
```
pos:     0                    1                    2                    3
         (Sgl(a),             (Sgl(b),             (Sgl(c),             (Sgl(d),
          Spatial(#xxxx))      Spatial(#####))      Spatial(#####))      Spatial(#####))
```

**After fold** $\mathsf{Fold}(\mathsf{compress}_5([x^4 \mid w]))$ = $[b_1 \mid [] \mid w \otimes v_4 \mid b_2]$:
```
pos:  ... -2   -1   |  0             1             2             3            |  4         ...
     ... none none  | (Sgl(a),      (Sgl(b),      (Sgl(c),      (Sgl(d),      | (Sgl(#),   ...
                    |  Sp(#xxxx))    Sp(#####))    Sp(#####))    Sp(#####))   |  Sp(#####))
          └─ b₁ ─┘   └───────────── w ⊗ v₄ ─────────────────────────────────┘  └── b₂ ────┘
```

**Advice word** $v_4$:
- $v_4[0] = \mathsf{Spatial}(\#, x, x, x, x)$ — from cell $-1$ packing positions $\{-5, -4, -3, -2, -1\}$
- $v_4[1] = \mathsf{Spatial}(\#, \#, \#, \#, \#)$ — from cell $-2$ packing positions $\{-10, \ldots, -6\}$
- $v_4[2], v_4[3] = \mathsf{Spatial}(\#^5)$

**After border normalization** $\langle w \otimes v_4 \rangle$:
```
pos:  ... -2   -1   |  0             1             2             3            |  4   5   ...
     ...  #    #    | (a, #xxxx)    (b, #####)    (c, #####)    (d, #####)    |  #   #   ...
          └─ standard # border ─┘   └───────────── w ⊗ v₄ ─────────────────────────────────┘   └─ standard # border ─┘
```

**After advice removal** $\langle w \rangle$:
```
pos:  ... -2   -1   |  0   1   2   3  |  4   5   ...
     ...  #    #    |  a   b   c   d  |  #   #   ...
```

This is the standard word embedding — the goal!

