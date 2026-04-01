# Theorem: $L_x(L) \in \mathrm{CA(RT)} \implies L \in \mathrm{CA(RT)}$

## Statement

**Theorem.** *Let $L$ be a language over a finite alphabet $\Sigma$. Define*
$$L_x(L) := \{ x^m w \mid w \in L,\; m = 2^{\lceil \log_2 |w| \rceil} \}.$$
*If $L_x(L)$ is recognizable in real-time by a cellular automaton, then $L$ is recognizable in real-time by a cellular automaton.*

## Conventions

**Cellular automaton (CA).** A CA $C = (Q, \delta, \mathsf{embed}, \mathsf{project})$ consists of a finite state set $Q$, a local transition function $\delta: Q \times Q \times Q \to Q$, an input embedding $\mathsf{embed}: \Sigma_\# \to Q$ (where $\Sigma_\# = \Sigma \cup \{\#\}$), and an output projection $\mathsf{project}: Q \to \{0,1\}$.

**Configuration.** A configuration is a map $c: \mathbb{Z} \to Q$. One step: $\mathsf{next}(c)(p) = \delta(c(p-1), c(p), c(p+1))$. Time evolution: $c^{(t)} = \mathsf{next}^t(c)$.

**Word embedding.** A word $w$ of length $n$ is embedded as:
$$\langle w \rangle(i) = \begin{cases} \mathsf{embed}(w_i) & \text{if } 0 \le i < n, \\ \mathsf{embed}(\#) & \text{otherwise.} \end{cases}$$

**Real-time acceptance (CA(RT)).** A CA accepts a word $w$ of length $n$ in real-time if $\mathsf{project}(c^{(n-1)}(0)) = 1$ where $c = \langle w \rangle$.

**Left-independent CA (OCA).** A CA is *left-independent* if $\delta(a, b, c) = \delta(a', b, c)$ for all $a, a', b, c \in Q$. We write $\delta_2(b, c) := \delta(\cdot, b, c)$.

**OCA acceptance.** For an OCA, real-time acceptance at $(n-1, 0)$ in the standard CA sense corresponds to acceptance at $(2(n-1), -(n-1))$ in the OCA's natural coordinates, via the standard conversions (see Lemma 1 below).

---

## Proof Structure

The proof chains six transformations, each justified by a lemma stated (and, where applicable, already formalized in Lean 4) below. The overall pipeline is:

| Step | Transformation | Operates on | Reference |
|------|---------------|-------------|-----------|
| 0 | CA → OCA | $[x^m w]$ | Lemma 1 |
| 0b | Shift | $[x^m w] \to [x^m \mid w]$ | Lemma 2 |
| 1 | LeftIndepSpeedup ($k=5$) + Lock-in | $[x^m \mid w] \to \mathsf{mixed}(w)$ | Lemma 3 |
| 2 | OCA → CA | $\mathsf{mixed}(w)$ | Lemma 4 |
| 3 | Mirror + Advice | $\mathsf{mixed}(w) \to w$ | Lemma 5, 6 |

We now present each step in detail.

---

## Notation: $[v \mid w]$

For words $v, w$ over $\Sigma_\#$, define the configuration $[v \mid w]: \mathbb{Z} \to \Sigma_\#$:
$$[v \mid w](i) = \begin{cases}
w_i & \text{if } 0 \le i < |w|, \\
v_{|v| - 1 + i} & \text{if } -|v| \le i < 0 \quad\text{(i.e., $v$ reversed onto negative positions)}, \\
\# & \text{otherwise.}
\end{cases}$$

That is, $w$ occupies positions $0, 1, \ldots, |w|-1$ and $v$ occupies positions $-1, -2, \ldots, -|v|$ (with $v_{|v|-1}$ at position $-1$, $v_{|v|-2}$ at $-2$, etc.). In the case of $v = x^m$, all negatives positions $-1$ through $-m$ hold $x$, so the reading order is irrelevant.

---

## Lemma 1 (RegularToLeftIndep) — Already Formalized

*Given any CA $C$, there exists a left-independent CA $C_0$ such that*
$$C_0.\mathsf{comp}(c, 2t, i) = C.\mathsf{comp}(c, t, i + t).$$

**Application.** If $C$ accepts $\langle x^m w \rangle$ at $(m+n-1, 0)$, then $C_0$ accepts $\langle x^m w \rangle$ at $(2(m+n-1), -(m+n-1))$.

*Proof reference:* `result_regular_to_left_indep` in `results.lean`. $\square$

---

## Lemma 2 (Shift Lemma)

*For any CA $C$ (left-independent or not), words $v, w$, and all $t, i$:*
$$C.\mathsf{comp}([v \mid w], t, i) = C.\mathsf{comp}(\langle vw \rangle, t, i + |v|).$$

*Proof.* The configurations $[v \mid w]$ and $\langle vw \rangle$ are related by the translation $\tau_{|v|}(c)(i) = c(i + |v|)$. Since $\delta$ is shift-invariant (it depends only on the values at $p-1, p, p+1$, not on $p$ itself), the computation commutes with translation. $\square$

**Application.** From Lemma 1, $C_0$ accepts $\langle x^m w \rangle$ at $(2(m+n-1), -(m+n-1))$. By Lemma 2 with $|v| = m$:

$$C_0.\mathsf{comp}([x^m \mid w], 2(m+n-1), i) = C_0.\mathsf{comp}(\langle x^m w \rangle, 2(m+n-1), i + m)$$

Setting $i + m = -(m+n-1)$ gives $i = -(2m+n-1)$. Therefore:

> $C_0$ accepts $[x^m \mid w]$ at $(2(m+n-1),\; -(2m+n-1))$.

Now $w$ sits at positions $0, \ldots, n-1$ and $x^m$ at positions $-1, \ldots, -m$.

---

## Lemma 3 (Mixed Speedup with Lock-In)

*Let $C_0$ be a left-independent CA and let $m = 2^{\lceil \log_2 n \rceil}$ for $n \ge 2$. There exists a left-independent CA $C_1$ such that:*

$$C_1\ \text{accepts}\ \mathsf{mixed}(w)\ \text{at}\ (2(n-1),\; -(n-1)) \iff C_0\ \text{accepts}\ [x^m \mid w]\ \text{at}\ (2(m+n-1),\; -(2m+n-1))$$

*where $\mathsf{mixed}(w)$ is a configuration with $n$ single cells at positions $0, \ldots, n-1$ (containing $w$) and at most $n-1$ compressed cells at positions $-1, \ldots, -(n-1)$ (each packing 5 cells from $[x^m \mid w]$).*

**Key property:** The compressed cells require advice to determine which positions contain $x$ vs $\#$ (depending on $m$), but the acceptance position does **not** require advice — it is tracked via a "deciding" bit that propagates through the simulation.

---

### Proof of Lemma 3

The construction compresses the negative positions (containing $x$ and $\#$) by a factor of $k = 5$, while leaving the positive positions (containing $w$) uncompressed. A lock-in mechanism propagates the acceptance signal to the standard OCA acceptance position.

#### 3.1 State Space

First, augment the original CA's state space with a "deciding" bit:
$$Q_{\text{aug}} = Q \times \{\mathsf{Deciding}, \mathsf{NonDeciding}\}$$
Only position 0 in the original configuration carries $\mathsf{Deciding}$; all others carry $\mathsf{NonDeciding}$. The transition function ignores this bit (it propagates unchanged through all transformations).

Then define the mixed state space:
$$Q' = \mathsf{Compressed}((\mathrm{Fin}\;5 \to Q_{\text{aug}}) \times \mathrm{Flag}) \;\mid\; \mathsf{Single}(Q_{\text{aug}} \times \mathrm{Flag})$$
where $\mathrm{Flag} = \mathsf{None} \mid \mathsf{Accept} \mid \mathsf{Reject}$.

#### 3.2 Mixed Configuration

Given $w$ of length $n$ and $m = 2^{\lceil \log_2 n \rceil}$, define $\mathsf{mixed}_m(w): \mathbb{Z} \to Q'$.

**Background: Original Configuration $[x^m \mid w]$**

Recall the bi-infinite configuration (from Section "Notation"):
$$[x^m \mid w](i) = \begin{cases}
w_i & \text{if } 0 \le i < n, \\
x & \text{if } -m \le i < 0, \\
\# & \text{otherwise.}
\end{cases}$$

**Compression: Grouping into k=5 Cells**

For $i < 0$, compressed position $i$ packs 5 original cells at positions $5i, 5i+1, 5i+2, 5i+3, 5i+4$:
- Compressed position $-1$ packs original positions $-5, -4, -3, -2, -1$
- Compressed position $-2$ packs original positions $-10, -9, -8, -7, -6$
- Compressed position $-d$ packs original positions $-5d, \ldots, -5d+4$

Since $m \le 2(n-1)$ (proven in Section 3.5), we have $2m + n - 1 \le 5(n-1)$ for $n \ge 2$.
Thus, the acceptance position $-(2m+n-1)$ fits within compressed positions $\{-1, \ldots, -(n-1)\}$.

**Mixed Configuration Definition**

$$\mathsf{mixed}_m(w)(i) = \begin{cases}
\mathsf{Single}(w_i) & \text{if } 0 \le i < n, \\
\mathsf{Single}(\#) & \text{if } i \ge n, \\
\mathsf{Spatial}(f_i) & \text{if } i < 0,
\end{cases}$$

where for $i < 0$, the tuple $f_i : \mathrm{Fin}\;5 \to Q$ is:
$$f_i(j) = \mathsf{embed}([x^m \mid w](5i + j))$$

**Example: $n=4$, $m=4$**

| Compressed pos $i$ | Original positions $5i$ to $5i+4$ | Contents |
|--------------------|-----------------------------------|----------|
| $-1$ | $-5, -4, -3, -2, -1$ | $\#, x, x, x, x$ |
| $-2$ | $-10, -9, -8, -7, -6$ | $\#, \#, \#, \#, \#$ |
| $-3$ | $-15, \ldots, -11$ | $\#, \#, \#, \#, \#$ |

**Example: $n=9$, $m=16$**

| Compressed pos $i$ | Original positions | Contents |
|--------------------|---------------------|----------|
| $-1$ | $-5, \ldots, -1$ | $x, x, x, x, x$ |
| $-2$ | $-10, \ldots, -6$ | $x, x, x, x, x$ |
| $-3$ | $-15, \ldots, -11$ | $x, x, x, x, x$ |
| $-4$ | $-20, \ldots, -16$ | $\#, \#, \#, \#, x$ | (boundary: $x$ at $-16$, $\#$ at $-17$ to $-20$) |
| $-5$ to $-8$ | ... | all $\#$ |

#### 3.3 Transition Rules

**Compressed cells:**
$$\delta'(\_, \mathsf{Compressed}(f, \mathsf{flag}),\; c_{\mathrm{right}}) = \mathsf{Compressed}(\mathsf{fold}(f, \mathsf{asQ}(c_{\mathrm{right}})),\; \mathsf{flag}')$$

where $\mathsf{fold}$ applies $\delta_2$ across the tuple using the right neighbor's leftmost component, and $\mathsf{flag}'$ is updated by the lock-in rules (Section 3.6). The left argument is ignored (left-independence).

**Boundary (compressed position $-1$, single position $0$):**
- The compressed cell at $-1$ reads $\mathsf{asQ}(\mathsf{Single}(q, \_)) = q$ from its right neighbor at position $0$.
- This correctly simulates $\delta_2(f_4, q)$ for the rightmost component.

#### 3.4 Speedup Spec

Define the coordinate maps:

$$\psi(i, j) = 5i + j \qquad \text{(spatial, for compressed position $i < 0$, component $j \in \{0,\ldots,4\}$)}$$
$$\varphi(t, i, j) = t + 4|i| - j \qquad \text{(temporal, diagonal regime for $t \ge |i|$)}$$

The LeftIndepSpeedup spec (already formalized as `result_left_indep_speedup`) guarantees:

$$C_1.\mathsf{comp}_j(\mathsf{mixed}(w), t, i) = C_0.\mathsf{comp}([x^m \mid w], \varphi(t, i, j), \psi(i, j)) \qquad \text{for } i < 0,\; t \ge |i|.$$

#### 3.5 Timing Analysis

We verify that the original acceptance point maps to a valid compressed coordinate and that lock-in has time to propagate.

**Finding the acceptance coordinates.** The original acceptance point is $(2(m+n-1),\; -(2m+n-1))$. Setting $d = \lceil (2m+n-1)/5 \rceil$ and $j = 5d - (2m+n-1)$:

- $j \in \{0, 1, 2, 3, 4\}$ by construction of $d$. $\checkmark$
- $\varphi(t_0, -d, j) = 2(m+n-1)$ and $\psi(-d, j) = -(2m+n-1)$ when $t_0 = d + n - 1$. $\checkmark$

**Bound on $d$.** Since $m = 2^{\lceil \log_2 n \rceil}$ is a power of 2 with $n \le m < 2n$, and $2n-1$ is odd (not a power of 2 for $n \ge 2$), we have $m \le 2(n-1)$. Therefore:
$$2m + n - 1 \le 5(n-1) \implies d = \lceil (2m+n-1)/5 \rceil \le n - 1. \quad\checkmark$$

This ensures the acceptance position $-d$ lies within the compressed region $\{-1, \ldots, -(n-1)\}$.

#### 3.6 Lock-In Mechanism

The acceptance occurs at compressed position $-d$ at time $t_0 = d + n - 1$. Since $d \le n-1$, this may be to the right of the standard OCA acceptance position $-(n-1)$. The lock-in propagates the result leftward.

**Detecting acceptance via the deciding bit:**
- The deciding bit (marking original position 0) propagates through RegularToLeftIndep → Shift → LeftIndepSpeedup.
- Exactly one component across all compressed cells carries $\mathsf{Deciding}$: the one at position $-d$, component $j$, simulating original position 0.

**Lock-in rules:**
1. **Detect:** Each compressed cell checks all 5 components: if any has $(\mathsf{Deciding}, \mathsf{project}(q) = 1)$, set $\mathsf{flag} := \mathsf{Accept}$ (or $\mathsf{Reject}$ if $\mathsf{project}(q) = 0$).
2. **Latch:** Once $\mathsf{flag} \ne \mathsf{None}$, it persists.
3. **Propagate:** Each cell copies $\mathsf{flag}$ from its right neighbor (information flows leftward).

**Timing verification.** The signal propagates from $-d$ to $-(n-1)$: distance $n - 1 - d$ cells. Arrival time:
$$t_0 + (n - 1 - d) = (d + n - 1) + (n - 1 - d) = 2(n-1). \quad\checkmark$$

Therefore $C_1$ accepts $\mathsf{mixed}(w)$ at $(2(n-1),\; -(n-1))$ iff $C_0$ accepts at the original point. $\square$

---

## Illustrated Examples

The following diagrams show the compressed OCA execution. In each diagram:
- Positions $\ge 0$ hold **single** (uncompressed) cells of $w$ and $\#$.
- Positions $< 0$ hold **compressed** cells, each packing 5 original OCA cells as $(q_0\; q_1\; q_2\; q_3\; q_4)$.
- The subscript on each $\#_t$ or $x_t$ denotes the original OCA time step that component simulates.
- `·` = outside the OCA light cone (unreachable, value irrelevant).
- `★` = acceptance readout.
- `→` = lock-in propagation direction.

### Example: $n = 3$, $m = 4$

$w = \text{"abc"}$, $m = 2^{\lceil\log_2 3\rceil} = 4$, $N = m + n = 7$.

**Parameters:**
- Original OCA acceptance: $(2(m+n-1), -(2m+n-1)) = (12, -10)$.
- $d = \lceil 10/5 \rceil = 2$, $j = 10 - 10 = 0$, $t_0 = 2 + 2 = 4$.
- Lock-in: from $-2$ to $-(n-1) = -2$, distance $0$. Already at target.

```
pos:          -2                 -1           │  0    1    2
         ─────────────────────────────────────┼────────────────
t=0:    #₀ #₀ #₀ #₀ #₀    #₀ x₀ x₀ x₀ x₀   │  a₀   b₀   c₀
        [spatial]         [spatial]           │
                                              │
t=1:    #₅ #₅ #₅ #₅ #₅    #₅ x₄ x₃ x₂ x₁   │  a₁   b₁   ·
        [spatial]         [diagonal]          │
                                              │
t=2:   #₁₀ #₉ #₈ #₇ #₆    #₆ x₅ x₄ x₃ x₂   │  a₂   ·    ·
        [diagonal]        [diagonal]          │
                                              │
t=3:   #₁₁#₁₀ #₉ #₈ #₇    #₇ x₆ x₅ x₄ x₃   │  ·    ·    ·
        [diagonal]        [diagonal]          │
                                              │
t=4:  ★#₁₂#₁₁#₁₀ #₉ #₈    #₈ x₇ x₆ x₅ x₄   │  ·    ·    ·
        [diagonal]        [diagonal]          │
        ↑
        ACCEPT at (t=4, pos=-2, j=0)
        φ = 4 + 4·2 - 0 = 12 ✓
        ψ = -5·2 + 0 = -10 ✓
```

The OCA reads acceptance at $(t=4, \text{pos}=-2)$, which is $(2(n-1), -(n-1))$ for $n=3$. $\checkmark$

---

### Example: $n = 4$, $m = 4$

$w = \text{"abcd"}$, $m = 2^{\lceil\log_2 4\rceil} = 4$, $N = m + n = 8$.

**Parameters:**
- Original OCA acceptance: $(2 \cdot 7, -(2 \cdot 4 + 3)) = (14, -11)$.
- $d = \lceil 11/5 \rceil = 3$, $j = 15 - 11 = 4$, $t_0 = 3 + 3 = 6$.
- Lock-in: from $-3$ to $-(n-1) = -3$, distance $0$. Already at target.

```
pos:          -3                 -2                 -1           │  0    1    2    3
         ────────────────────────────────────────────────────────┼─────────────────────
t=0:    #₀ #₀ #₀ #₀ #₀    #₀ #₀ #₀ #₀ #₀    #₀ x₀ x₀ x₀ x₀   │  a₀   b₀   c₀   d₀
        [spatial]         [spatial]         [spatial]           │
                                                                │
t=1:    #₅ #₅ #₅ #₅ #₅    #₅ #₅ #₅ #₅ #₅    #₅ x₄ x₃ x₂ x₁   │  a₁   b₁   c₁   ·
        [spatial]         [spatial]         [diagonal]          │
                                                                │
t=2:   #₁₀#₁₀#₁₀#₁₀#₁₀   #₁₀ #₉ #₈ #₇ #₆    #₆ x₅ x₄ x₃ x₂   │  a₂   b₂   ·    ·
        [spatial]         [diagonal]        [diagonal]          │
                                                                │
t=3:   #₁₅#₁₄#₁₃#₁₂#₁₁   #₁₁#₁₀ #₉ #₈ #₇    #₇ x₆ x₅ x₄ x₃   │  a₃   ·    ·    ·
        [diagonal]        [diagonal]        [diagonal]          │
                                                                │
t=4:   #₁₆#₁₅#₁₄#₁₃#₁₂   #₁₂#₁₁#₁₀ #₉ #₈    #₈ x₇ x₆ x₅ x₄   │  ·    ·    ·    ·
        [diagonal]        [diagonal]        [diagonal]          │
                                                                │
t=5:   #₁₇#₁₆#₁₅#₁₄#₁₃   #₁₃#₁₂#₁₁#₁₀ #₉    ·  ·  ·  ·  ·    │  ·    ·    ·    ·
        [diagonal]        [diagonal]                            │
                                                                │
t=6:   #₁₈#₁₇#₁₆#₁₅#₁₄★   ·  ·  ·  ·  ·     ·  ·  ·  ·  ·    │  ·    ·    ·    ·
        [diagonal]                                              │
                          ↑
        ACCEPT at (t=6, pos=-3, j=4)
        φ = 6 + 4·3 - 4 = 14 ✓
        ψ = -5·3 + 4 = -11 ✓
```

The OCA reads acceptance at $(t=6, \text{pos}=-3) = (2(n-1), -(n-1))$ for $n=4$. $\checkmark$

---

### Example: $n = 5$, $m = 8$

$w = \text{"abcde"}$, $m = 2^{\lceil\log_2 5\rceil} = 8$, $N = m + n = 13$.

**Parameters:**
- Original OCA acceptance: $(2 \cdot 12, -(2 \cdot 8 + 4)) = (24, -20)$.
- $d = \lceil 20/5 \rceil = 4$, $j = 20 - 20 = 0$, $t_0 = 4 + 4 = 8$.
- Lock-in: from $-4$ to $-(n-1) = -4$, distance $0$. Already at target.

```
pos:          -4                 -3                 -2                 -1           │  0    1    2    3    4
         ───────────────────────────────────────────────────────────────────────────┼──────────────────────────
t=0:    #₀ #₀ #₀ #₀ #₀    #₀ #₀ #₀ #₀ #₀    #₀ #₀ x₀ x₀ x₀    x₀ x₀ x₀ x₀ x₀   │  a₀   b₀   c₀   d₀   e₀
        [spatial]         [spatial]         [spatial]         [spatial]           │
                                                                                  │
t=1:    #₅ #₅ #₅ #₅ #₅    #₅ #₅ #₅ #₅ #₅    #₅ #₅ x₅ x₅ x₅    x₅ x₄ x₃ x₂ x₁   │  a₁   b₁   c₁   d₁   ·
        [spatial]         [spatial]         [spatial]         [diagonal]          │
                                                                                  │
t=2:   #₁₀#₁₀#₁₀#₁₀#₁₀   #₁₀#₁₀#₁₀#₁₀#₁₀   #₁₀ #₉ x₈ x₇ x₆    x₆ x₅ x₄ x₃ x₂   │  a₂   b₂   c₂   ·    ·
        [spatial]         [spatial]         [diagonal]        [diagonal]          │
                                                                                  │
t=3:   #₁₅#₁₅#₁₅#₁₅#₁₅   #₁₅#₁₄#₁₃#₁₂#₁₁   #₁₁#₁₀ x₉ x₈ x₇    x₇ x₆ x₅ x₄ x₃   │  a₃   b₃   ·    ·    ·
        [spatial]         [diagonal]        [diagonal]        [diagonal]          │
                                                                                  │
t=4:   #₂₀#₁₉#₁₈#₁₇#₁₆   #₁₆#₁₅#₁₄#₁₃#₁₂   #₁₂#₁₁x₁₀ x₉ x₈    x₈ x₇ x₆ x₅ x₄   │  a₄   ·    ·    ·    ·
        [diagonal]        [diagonal]        [diagonal]        [diagonal]          │
                                                                                  │
t=5:   #₂₁#₂₀#₁₉#₁₈#₁₇   #₁₇#₁₆#₁₅#₁₄#₁₃   #₁₃#₁₂x₁₁x₁₀ x₉    x₉ x₈ x₇ x₆ x₅   │  ·    ·    ·    ·    ·
        [diagonal]        [diagonal]        [diagonal]        [diagonal]          │
                                                                                  │
t=6:   #₂₂#₂₁#₂₀#₁₉#₁₈   #₁₈#₁₇#₁₆#₁₅#₁₄   #₁₄#₁₃x₁₂x₁₁x₁₀    ·  ·  ·  ·  ·    │  ·    ·    ·    ·    ·
        [diagonal]        [diagonal]        [diagonal]                            │
                                                                                  │
t=7:   #₂₃#₂₂#₂₁#₂₀#₁₉   #₁₉#₁₈#₁₇#₁₆#₁₅    ·  ·  ·  ·  ·     ·  ·  ·  ·  ·    │  ·    ·    ·    ·    ·
        [diagonal]        [diagonal]                                              │
                                                                                  │
t=8:  ★#₂₄#₂₃#₂₂#₂₁#₂₀    ·  ·  ·  ·  ·     ·  ·  ·  ·  ·     ·  ·  ·  ·  ·    │  ·    ·    ·    ·    ·
        [diagonal]                                                                │
                     ↑
        ACCEPT at (t=8, pos=-4, j=0)
        φ = 8 + 4·4 - 0 = 24 ✓
        ψ = -5·4 + 0 = -20 ✓
```

The OCA reads acceptance at $(t=8, \text{pos}=-4) = (2(n-1), -(n-1))$ for $n=5$. $\checkmark$

---

### Example: $n = 9$, $m = 16$

$w$ has length 9, $m = 2^{\lceil\log_2 9\rceil} = 16$, $N = m + n = 25$.

**Parameters:**
- Original OCA acceptance: $(2 \cdot 24, -(2 \cdot 16 + 8)) = (48, -40)$.
- $d = \lceil 40/5 \rceil = 8$, $j = 40 - 40 = 0$, $t_0 = 8 + 8 = 16$.
- Lock-in: from $-8$ to $-(n-1) = -8$, distance $0$. Already at target.

```
pos:    -8       -7       -6       -5       -4       -3       -2       -1     │ 0  1  2  3  4  5  6  7  8
       ──────────────────────────────────────────────────────────────────────────┼──────────────────────────────
t=0:  ##### .. ##### .. ##### .. ##### .. ##xxx .. xxxxx .. xxxxx .. xxxxx   │ w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈
      [spat]   [spat]   [spat]   [spat]   [spat]   [spat]   [spat]   [spat]  │
       ...      ...      ...      ...      ...      ...      ...      ...     │     (ellided for space)
t=8:  diag     diag     diag     diag     diag     diag     diag     diag    │ w₈  ·  ·  ·  ·  ·  ·  ·  ·
       ...      ...      ...      ...      ...      ...      ...      ...     │
t=16:★#₄₈..    ·        ·        ·        ·        ·        ·        ·       │ ·   ·  ·  ·  ·  ·  ·  ·  ·
      ↑
      ACCEPT at (t=16, pos=-8, j=0)
      φ = 16 + 4·8 - 0 = 48 ✓
      ψ = -5·8 + 0 = -40 ✓
```

Here the compressed configuration has:
- Positions $-1$ through $-3$: all-$x$ cells (covering original positions $-1$ to $-15$; 15 of the 16 $x$'s)
- Position $-4$: mixed cell $(\#, \#, x, x, x)$ (covering positions $-16$ to $-20$; the remaining $x$ at $-16$, then $\#$'s at $-17$ to $-20$)
- Positions $-5$ through $-8$: all-$\#$ cells

The acceptance at $(t=16, \text{pos}=-8) = (2(n-1), -(n-1))$ for $n=9$. $\checkmark$

---

### Example: $n = 16$, $m = 16$ (Lock-in propagation needed)

$w$ has length 16, $m = 2^{\lceil\log_2 16\rceil} = 16$, $N = 32$.

**Parameters:**
- Original OCA acceptance: $(2 \cdot 31, -(2 \cdot 16 + 15)) = (62, -47)$.
- $d = \lceil 47/5 \rceil = 10$, $j = 50 - 47 = 3$, $t_0 = 10 + 15 = 25$.
- Lock-in: from $-10$ to $-(n-1) = -15$, distance $5$.
- Arrival time: $25 + 5 = 30 = 2(n-1)$. $\checkmark$

This is the first example where the lock-in must propagate. The acceptance is detected at position $-10$ at time $25$, and the flag travels leftward one cell per time step:

$$-10 \xrightarrow{t=26} -11 \xrightarrow{t=27} -12 \xrightarrow{t=28} -13 \xrightarrow{t=29} -14 \xrightarrow{t=30} -15$$

At $(t = 30, \text{pos} = -15) = (2(n-1), -(n-1))$, the lock-in flag has arrived. $\checkmark$

The lock-in does not cross any compressed/single boundary — positions $-10$ through $-15$ are all compressed cells, so propagation uses only the compressed transition rule.

---

## Understanding the Diagrams: Why the Construction Works

Each compressed cell at position $-d$ simulates 5 original OCA cells running at 5 different time offsets. The key phenomenon is visible in the diagrams:

1. **Spatial regime** ($t < d$): All 5 components within the cell evolve at original time $5t$ — they are synchronized because the cell hasn't yet been reached by information from the boundary (the rightmost single cell).

2. **Diagonal regime** ($t \ge d$): Information from the boundary has arrived. Component $j$ now runs at original time $t + 4d - j$. The components become desynchronized, with component 0 (leftmost) furthest ahead in original time.

The crucial insight is that in the diagonal regime, the original time $\varphi(t, -d, j) = t + 4d - j$ grows with both $t$ and $d$. So deeper compressed cells (larger $d$) simulate *later* original time steps. By choosing $d$ appropriately, the leftmost component of cell $-d$ reaches exactly the original acceptance time.

The lock-in then converts this spatially-distributed acceptance (which occurs at position $-d$, potentially far from $-(n-1)$) into a signal that arrives at exactly $(2(n-1), -(n-1))$.

---

## Lemma 4 (LeftIndepToRegular) — Already Formalized

*Given any left-independent CA $C_1$, there exists a CA $C_2$ such that*
$$C_2.\mathsf{comp}(c, t, i) = C_1.\mathsf{comp}(c, 2t, i - t).$$

**Application.** $C_1$ accepts $\mathsf{mixed}(w)$ at $(2(n-1), -(n-1))$. Setting $t = n-1$, $i = 0$:
$$C_2.\mathsf{comp}(\mathsf{mixed}(w), n-1, 0) = C_1.\mathsf{comp}(\mathsf{mixed}(w), 2(n-1), -(n-1)).$$

So $C_2$ accepts $\mathsf{mixed}(w)$ at $(n-1, 0)$. $\checkmark$

*Proof reference:* `result_left_indep_to_regular` in `results.lean`. $\square$

---

## Lemma 5 (Mirror Configuration) — Already Formalized

The CA $C_2$ operates on $\mathsf{mixed}(w)$, whose domain is $\mathbb{Z}$ with $n$ single cells at $\{0, \ldots, n-1\}$ and $\le n-1$ compressed cells at $\{-1, \ldots, -(n-1)\}$. Total meaningful cells: at most $2n - 1$.

The `mirrorConfigCA` construction simulates $C_2$ on a folded input of length $n$ by tracking both the forward (single/positive) and backward (compressed/negative) evolution in a product state:

$$Q'' = Q'_{\text{single}} \times Q'_{\text{compressed}}$$

Position $i$ in the folded CA simultaneously tracks:
- $C_2$'s computation at position $i$ (the $w$-zone), and
- $C_2$'s computation at position $-(i+1)$ (the compressed zone).

The `spec_interior` theorem guarantees correctness for positions in the interior of the light cone.

*Proof reference:* `mirrorConfigCA` in `basic_mirror.lean`. $\square$

---

## Lemma 6 (Two-Stage Advice is RT-Closed) — Already Formalized

The folded CA needs advice to determine:

1. **Which compressed cells contain $x$ vs $\#$.** The boundary falls at compressed position $-\lceil m/5 \rceil$, determined by $m = 2^{\lceil \log_2 n \rceil}$.

2. **Boundary markers.** Cells 0 and $n-1$ are marked to identify the word boundaries.

Note: The acceptance position and component ($d$, $j$) do **not** require advice. The "deciding" bit (marking original position 0) propagates through the simulation, so the correct component self-identifies. See Section 3.7.

The $x/\#$ boundary depends on $2^{\lceil \log_2 n \rceil}$, which is computable by a two-stage advice:

- **Stage 1 (CArt transducer):** Marks position $i$ iff $i+1$ is a power of 2. This is recognizable in real-time by marking the first two occurrences. (Already formalized as `exp_word_ca` in `exp_middle_two_stage.lean`.)

- **Stage 2 (FST):** A finite-state transducer scans right-to-left and computes $\lceil m/5 \rceil$ from the marked power-of-2 positions, filling in the $x/\#$ pattern.

The boundary markers (cells 0 and $n-1$) are trivially two-stage: the FST marks the first and last positions.

By `result_two_stage_is_rt_closed`, this advice is RT-closed, meaning it does not increase the complexity class. $\square$

---

## Lemma 7 (Border Normalization) — Formalized

*For any CA $C$ and border symbols $b_1, b_2 \in \Sigma$, there exists a CA $C'$ that simulates $C$ on bordered configurations.*

More precisely: $C'$ takes standard word input $\langle w \rangle$ and computes as if $C$ were running on $\mathsf{BorderedConfig}(b_1, [], w, b_2)$.

**Definition.** The bordered configuration $\mathsf{BorderedConfig}(b_1, v, w, b_2): \mathbb{Z} \to \Sigma$ is:
$$\mathsf{BorderedConfig}(b_1, v, w, b_2)(i) = \begin{cases}
w_i & \text{if } 0 \le i < |w|, \\
v_{|v|-1+i} & \text{if } -|v| \le i < 0, \\
b_2 & \text{if } i \ge |w|, \\
b_1 & \text{otherwise.}
\end{cases}$$

For the special case with empty $v$, this simplifies to: $w$ at positions $0$ to $|w|-1$, $b_2$ at $\ge |w|$, $b_1$ at $< 0$.

**Construction (`borderNormalizeCA`).** The state space is $\mathsf{Option}(C.Q) \times C.Q \times C.Q$ where:
- First component: `none` for border, `some q` for interior
- Second component: left border simulation (tracks position $-1$ in bordered config)
- Third component: right border simulation (tracks position $|w|$)

The key insight: each cell independently simulates both border evolutions. When a neighbor is `none` (border), the cell uses its local border simulation as the effective neighbor value.

**Specification.** For non-empty word $w$:
$$C'.\mathsf{trace}(\langle w \rangle) = C.\mathsf{trace}(\mathsf{BorderedConfig}(b_1, [], w, b_2))$$

*Proof reference:* `border_normalize` in `basic_border_normalization.lean`. $\square$

---

## Lemma 8 (Fold CA) — Formalized

*For any CA $C$, there exists a CA $C'$ that simulates $C$ on a folded (bi-infinite to right-infinite) configuration.*

**Definition.** The fold configuration $\mathsf{FoldConfig}(c): \mathbb{Z} \to \mathsf{Option}(\alpha \times \alpha)$ is:
$$\mathsf{FoldConfig}(c)(p) = \begin{cases}
\mathsf{none} & \text{if } p < 0, \\
\mathsf{some}(c(p), c(-p-1)) & \text{if } p \ge 0.
\end{cases}$$

This pairs position $p$ with position $-p-1$, folding the negative half onto the positive:
- Position 0: pairs $c(0)$ with $c(-1)$
- Position 1: pairs $c(1)$ with $c(-2)$
- Position $i$: pairs $c(i)$ with $c(-i-1)$

**Construction (`foldCA`).** The state space is $\mathsf{Option}(C.Q \times C.Q)$ where:
- `none` represents the boundary (negative positions)
- `some(fwd, bwd)` where `fwd` tracks position $i$, `bwd` tracks position $-i-1$

At position 0 (boundary), the reflection occurs: `fwd`'s left neighbor comes from `bwd` (the value at $-1$), and `bwd`'s right neighbor comes from `fwd` (the value at $0$).

**Specification.** For any configuration $c$ and $i \ge 0$:
$$C'.\mathsf{comp}(\mathsf{FoldConfig}(c), t, i) = C.\mathsf{comp}(c, t, i)$$

*Proof reference:* `fold_spec` in `basic_fold.lean`. $\square$

---

## Lemma 9 (LeftIndepSpeedupConfig) — Formalized

*For any left-independent CA with compression factor $k \ge 2$, there exists a compressed CA that simulates $k$ cells per compressed position.*

This generalizes the word-based `LeftIndepSpeedupQuiescent` to arbitrary configurations.

**State Space.** The compressed CA has three state types:
- `Single(q)`: uncompressed cell at position $i \ge 0$
- `Spatial(w : \mathrm{Fin}\;k \to Q)`: compressed cell where all $k$ components are synchronized (same original time)
- `Diagonal(w : \mathrm{Fin}\;k \to Q)`: compressed cell where components are staggered in time

**Compression.** Given a configuration $c$, define $\mathsf{compress}(c)$:
$$\mathsf{compress}(c)(i) = \begin{cases}
\mathsf{Single}(c(i)) & \text{if } i \ge 0, \\
\mathsf{Spatial}(\lambda j.\; c(k \cdot i + j)) & \text{if } i < 0.
\end{cases}$$

**Two Regimes.** At compressed position $i < 0$ and time $t$:
- **Spatial regime** ($t < -i$): All components at original time $k \cdot t$
- **Diagonal regime** ($t \ge -i$): Component $j$ at original time $t - (k-1) \cdot i - j$

**Specification.** For $i < 0$ and $t \ge -i$ (diagonal regime):
$$C'.\mathsf{comp}(\mathsf{compress}(c), t, i)(j) = C.\mathsf{comp}(c, (t - (k-1) \cdot i - j).\mathsf{toNat}, k \cdot i + j)$$

The spatial regime satisfies:
$$C'.\mathsf{nextt}(\mathsf{compress}(c), t, i) = \mathsf{Spatial}(\lambda j.\; C.\mathsf{nextt}(c, k \cdot t, k \cdot i + j))$$

**Fold Operations.** The three fold functions compute the transitions:
- `foldDiag`: diagonal $\to$ diagonal (chain of $\delta_2$)
- `foldSpatial`: spatial + spatial $\to$ spatial (full $k$-step triangle)
- `foldSwitch`: spatial + (single/diagonal) $\to$ diagonal (regime transition)

*Proof reference:* `spec`, `spec_spatial`, `spec_diagonal` in `speedup_left_independent_config.lean`. $\square$

---

## Completing the Proof

*Proof of the Theorem.* Let $L \subseteq \Sigma^*$ and suppose $L_x(L) \in \mathrm{CA(RT)}$. We construct a CA $C'$ that recognizes $L$ in real-time.

Let $w \in \Sigma^*$ with $|w| = n \ge 2$, and set $m := 2^{\lceil \log_2 n \rceil}$. By hypothesis there exists a CA $C$ accepting $L_x(L)$ in real-time, so $C$ accepts $\langle x^m w \rangle$ at $(m+n-1,\; 0)$ iff $w \in L$.

**Step 1.** Apply Lemma 1 (RegularToLeftIndep) to $C$. This yields a left-independent CA $C_0$ satisfying
$$C_0.\mathsf{comp}(c,\; 2t,\; i) = C.\mathsf{comp}(c,\; t,\; i+t).$$
Setting $t = m+n-1$ and $i = -(m+n-1)$, we obtain: $C_0$ accepts $\langle x^m w \rangle$ at $(2(m+n-1),\; -(m+n-1))$.

**Step 2.** Apply Lemma 2 (Shift) with $v = x^m$. Since $[x^m \mid w](i) = \langle x^m w \rangle(i + m)$:
$$C_0.\mathsf{comp}([x^m \mid w],\; 2(m+n-1),\; i) = C_0.\mathsf{comp}(\langle x^m w \rangle,\; 2(m+n-1),\; i + m).$$
Setting $i + m = -(m+n-1)$, i.e., $i = -(2m+n-1)$: $C_0$ accepts $[x^m \mid w]$ at $(2(m+n-1),\; -(2m+n-1))$.

**Step 3.** Apply Lemma 3 (LeftIndepSpeedup + Lock-in) with $k = 5$ to the left-independent CA $C_0$ on the configuration $[x^m \mid w]$. This constructs a left-independent CA $C_1$ over the mixed state space $Q'$, operating on $\mathsf{mixed}(w)$.

Set $d := \lceil (2m+n-1)/5 \rceil$ and $j := 5d - (2m+n-1)$. By the analysis in Section 3.5:
- $j \in \{0, 1, 2, 3, 4\}$;
- $d \le n-1$ (Section 3.6, using $m \le 2(n-1)$);
- the LeftIndepSpeedup spec gives $C_1.\mathsf{comp}_j(\mathsf{mixed}(w),\; d+n-1,\; -d) = C_0.\mathsf{comp}([x^m \mid w],\; 2(m+n-1),\; -(2m+n-1))$, since $\varphi(d+n-1, -d, j) = 2(m+n-1)$ and $\psi(-d, j) = -(2m+n-1)$.

The lock-in mechanism (Section 3.7) captures the acceptance result at $(d+n-1, -d)$ and propagates it leftward. Since $d \le n-1$, the signal travels $n - 1 - d$ cells, arriving at position $-(n-1)$ at time $(d+n-1) + (n-1-d) = 2(n-1)$.

Therefore: $C_1$ accepts $\mathsf{mixed}(w)$ at $(2(n-1),\; -(n-1))$.

**Step 4.** Apply Lemma 4 (LeftIndepToRegular) to the left-independent CA $C_1$. This yields a CA $C_2$ satisfying
$$C_2.\mathsf{comp}(c,\; t,\; i) = C_1.\mathsf{comp}(c,\; 2t,\; i-t).$$
Setting $t = n-1$ and $i = 0$:
$$C_2.\mathsf{comp}(\mathsf{mixed}(w),\; n-1,\; 0) = C_1.\mathsf{comp}(\mathsf{mixed}(w),\; 2(n-1),\; -(n-1)).$$
So $C_2$ accepts $\mathsf{mixed}(w)$ at $(n-1,\; 0)$.

**Step 5.** The configuration $\mathsf{mixed}(w)$ has $n$ meaningful single cells at positions $\{0, \ldots, n-1\}$ and at most $n-1$ compressed cells at positions $\{-1, \ldots, -(n-1)\}$. Apply Lemma 5 (mirrorConfigCA) to fold the negative positions onto the positive ones: position $i$ in the folded CA tracks both $C_2$'s state at position $i$ and at position $-(i+1)$. This yields a CA $C_3$ over state space $Q'' = Q'_{\text{single}} \times Q'_{\text{compressed}}$ that operates on a word of length $n$ and satisfies $C_3.\mathsf{comp}(\langle w \rangle, n-1, 0) = C_2.\mathsf{comp}(\mathsf{mixed}(w), n-1, 0)$ (by `spec_interior`, since position 0 at time $n-1$ is in the interior of the light cone of $\langle w \rangle$).

However, $C_3$ needs to know which compressed cells hold $x$ vs $\#$ (determined by $m$), plus boundary markers for cells 0 and $n-1$. These are provided as advice. Note that the acceptance position ($d$, $j$) does **not** require advice — the "deciding" bit self-identifies the correct component (see Section 3.7).

**Step 6.** By Lemma 6, all advice functions (x/# pattern and boundary markers) are two-stage (CArt transducer + FST), hence RT-closed by `result_two_stage_is_rt_closed`. This means there exists a CA $C'$ — without advice — that accepts $\langle w \rangle$ at $(n-1, 0)$ iff $C_3$ with advice accepts $\langle w \rangle$ at $(n-1, 0)$.

**Conclusion.** Tracing through the chain:
$$C'\ \text{accepts}\ w\ \text{at}\ (n-1, 0) \iff C_3\ \text{accepts}\ \langle w \rangle\ \text{at}\ (n-1, 0)$$
$$\iff C_2\ \text{accepts}\ \mathsf{mixed}(w)\ \text{at}\ (n-1, 0) \iff C_1\ \text{accepts}\ \mathsf{mixed}(w)\ \text{at}\ (2(n-1), -(n-1))$$
$$\iff C_0\ \text{accepts}\ [x^m \mid w]\ \text{at}\ (2(m+n-1), -(2m+n-1))$$
$$\iff C_0\ \text{accepts}\ \langle x^m w \rangle\ \text{at}\ (2(m+n-1), -(m+n-1))$$
$$\iff C\ \text{accepts}\ \langle x^m w \rangle\ \text{at}\ (m+n-1, 0) \iff w \in L.$$

Therefore $L \in \mathrm{CA(RT)}$. $\quad\blacksquare$

---

## Summary of Dependencies

| Component | Status | Location |
|-----------|--------|----------|
| RegularToLeftIndep | Formalized | `results.lean` (Result 2) |
| LeftIndepToRegular | Formalized | `results.lean` (Result 1) |
| LeftIndepSpeedup (word-based, spec) | Formalized | `speedup_left_independent.lean` (Result 3) |
| LeftIndepSpeedupConfig (config-based, spec) | Formalized | `speedup_left_independent_config.lean` |
| mirrorConfigCA (spec_interior) | Formalized | `basic_mirror.lean` |
| foldCA (fold_spec) | Formalized | `basic_fold.lean` |
| borderNormalizeCA (border_normalize) | Formalized | `basic_border_normalization.lean` |
| exp_middle two-stage advice | Formalized | `exp_middle_two_stage.lean` |
| Two-stage ⟹ RT-closed | Formalized | `is_two_stage_of_rt_closed_and_causal.lean` (Result 7) |
| Shift lemma | To formalize | Trivial (translation invariance) |
| Mixed state space (without lock-in) | Formalized | via `LeftIndepSpeedupConfig` |
| Lock-in mechanism | To formalize | New construction on top of speedup |
| x/# pattern advice | To formalize | Two-stage via existing machinery |
| Boundary markers (0, n-1) | To formalize | Trivial two-stage advice |

---

## Appendix: Verification of $d \le n - 1$ for Small $n$

| $n$ | $m = 2^{\lceil\log_2 n\rceil}$ | $2m+n-1$ | $d = \lceil\cdot/5\rceil$ | $j$ | $t_0 = d+n-1$ | $d \le n-1$? | Lock-in dist |
|-----|------|---------|-------|-----|--------|------------|------------|
| 2 | 2 | 5 | 1 | 0 | 2 | ✓ | 0 |
| 3 | 4 | 10 | 2 | 0 | 4 | ✓ | 0 |
| 4 | 4 | 11 | 3 | 4 | 6 | ✓ | 0 |
| 5 | 8 | 20 | 4 | 0 | 8 | ✓ | 0 |
| 6 | 8 | 21 | 5 | 4 | 10 | ✓ | 0 |
| 7 | 8 | 22 | 5 | 3 | 11 | ✓ | 1 |
| 8 | 8 | 23 | 5 | 2 | 12 | ✓ | 2 |
| 9 | 16 | 40 | 8 | 0 | 16 | ✓ | 0 |
| 10 | 16 | 41 | 9 | 4 | 18 | ✓ | 0 |
| 15 | 16 | 46 | 10 | 4 | 24 | ✓ | 4 |
| 16 | 16 | 47 | 10 | 3 | 25 | ✓ | 5 |
| 17 | 32 | 80 | 16 | 0 | 32 | ✓ | 0 |
| 32 | 32 | 95 | 19 | 0 | 50 | ✓ | 12 |
| 33 | 64 | 160| 32 | 0 | 64 | ✓ | 0 |

In every case, $d \le n - 1$ and $t_0 + (n - 1 - d) = 2(n-1)$. $\checkmark$
