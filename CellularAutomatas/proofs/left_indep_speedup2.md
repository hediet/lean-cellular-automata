# Left-Independent CA Compression (Lemma `linksunabhaengigSpeedup`)

## Context: Left-Independent Cellular Automata

A cellular automaton $C = (Q, \delta)$ is **left-independent** if its transition function $\delta(a, b, c)$ ignores the left argument $a$:

$$
\forall a, a', b, c \in Q: \delta(a, b, c) = \delta(a', b, c)
$$

This means information only flows leftward in the space-time diagram.

---

## Construction

**Given:**
- A left-independent CA $C = (Q, \delta)$
- A compression factor $k \geq 2$
- A state $\# \in Q$ that is both **passive** (quiescent: $\delta(\#, \#, \#) = \#$) and **initial** (cells at $p \leq 0$ start with $\#$)

**Construct:** A new left-independent CA $C' = (Q', \delta')$.

**State space $Q'$:**

```lean
inductive Q' where
  | single (q : Q) : Q'
  | compr (w : Fin k → Q) : Q'
```

**Border state:** `border' := compr (fun _ => #)`

This is quiescent: `δ'(_, border', border') = border'`.

**Initial configuration:** For input word at positions $0 \leq p < n$:

```
... border' border' | single(w₀) single(w₁) ... single(wₙ₋₁) | border' border' ...
       ← p < 0 →              ← 0 ≤ p < n →                     ← p ≥ n →
```

Note: `single #` exists in the type but is never used - all border cells use `compr`.

**Helper function** to extract the "effective single":

```lean
def asQ (s : Q') : Q := match s with
  | single q => q
  | compr w => w 0
```

**The folded transition function $\text{fold}(w, q)$:** For a word $w \in Q^*$ and next value $q \in Q$, define $\text{fold}(w, q) \in Q^{|w|}$ recursively (decreasing on $|w|$):

$$
\text{fold}(w, q) := \begin{cases}
[] & \text{if } |w| = 0 \\
[\delta(\#, w_0, q)] & \text{if } |w| = 1 \\
\text{fold}(w_{[0:|w|-1]}, r) \;{+\!\!+}\; [r] & \text{if } |w| > 1, \text{ where } r := \delta(\#, w_{|w|-1}, q)
\end{cases}
$$

This corresponds to the thesis notation $\delta^{wq} = \text{fold}(w, q)$.

Example: $\text{fold}([q_0, q_1], q_2) = \big(\delta(\#, q_0, \delta(\#, q_1, q_2)),\; \delta(\#, q_1, q_2)\big)$

**Transition function $\delta'$:**

$$
\begin{aligned}
\delta'(\_, \text{single } q_b, c) &:= \text{single } (\delta(\#, q_b, \text{asQ}(c))) \\
\delta'(\_, \text{compr } w_b, c) &:= \text{compr } (\text{fold}(w_b, \text{asQ}(c)))
\end{aligned}
$$

---

## Correctness Statement (The Specification)

Let $c : \mathbb{Z} \to Q$ be a configuration of $C$ with word at positions $0 \leq p < n$ and $c_p = \#$ for $p < 0$ or $p \geq n$.

Define the corresponding $C'$ configuration (with $\text{border}' := \text{compr } (\lambda\_. \#)$):

$$
c'(p) := \begin{cases}
\text{border}' & \text{if } p < 0 \text{ or } p \geq n \\
\text{single } (c_p) & \text{if } 0 \leq p < n
\end{cases}
$$

Then for all $i < 0$ and $t \geq 0$:

$$
\Delta^{t}_{C'}(c')_i = \text{compr } w \quad \text{where } w(j) := \Delta^{t + i - ki + k - j}_C(c)_{ki - k + j}
$$

**In code notation (0-indexed):** Define helper functions:

$$
\psi(i, j) := ki + j \qquad \phi(t, i, j) := t - (k-1)i - j
$$

For i = 0 (first word cell): ψ(0, j) = j, so components 0..k-1 map to positions 0..k-1.
For i = -1 (last compressed cell): ψ(-1, k-1) = -1, and ψ(-1, k-1) + 1 = 0 (first word position).

Then the specification becomes (for $\Delta^{t}_{C'}(c')_i = \text{compr } w$):

$$
w(j) = \Delta^{\phi(t,i,j)}_C(c)_{\psi(i,j)}
$$

**Concrete examples:**

For $k=2$ (components $j \in \{0, 1\}$):

$$
\Delta^{t}_{C'}(c')_i = \text{compr } \big(\Delta^{t-i+1}_C(c)_{2i-1},\; \Delta^{t-i}_C(c)_{2i}\big)
$$

For $k=3$ (components $j \in \{0, 1, 2\}$):

$$
\Delta^{t}_{C'}(c')_i = \text{compr } \big(\Delta^{t-2i+2}_C(c)_{3i-2},\; \Delta^{t-2i+1}_C(c)_{3i-1},\; \Delta^{t-2i}_C(c)_{3i}\big)
$$

---

## Proof Structure

### Key properties of $\psi$ and $\phi$ (0-indexed, used but not reproved):

| Property | Meaning |
|----------|---------|
| $\psi(i, j) < 0$ for $i < 0$ | Compressed positions stay negative |
| $\phi(0, i, j) \leq -\psi(i, j)$ | At $t=0$, we're in the passive zone |
| $\psi(0, 0) = 0$ | Boundary condition (first component of $i=0$ tuple) |
| $\psi(-1, k-1) + 1 = 0$ | Key edge case: last comp of $i=-1$ is adjacent to position 0 |
| $\psi(i+1, 0) = \psi(i, k-1) + 1$ | Position continuity across cells |
| $\psi(i, j+1) = \psi(i, j) + 1$ | Components are consecutive positions |
| $\phi(t, i+1, 0) = \phi(t, i, k-1)$ | Time continuity across cells |
| $\phi(t+1, i, j+1) = \phi(t, i, j)$ for $j+1 < k$ | Staircase time relation |
| $\phi(t, -1, k-1) = t$ | Edge case: at $i=-1$, $j=k-1$, time equals $t$ |

### Proof by outer induction on $t$:

**Base case ($t = 0$):**

At $t=0$, position $i < 0$ has state $\Delta^0_{C'}(c')_i = c'(i) = \text{compr } (\lambda\_. \#)$.

Since $\#$ is passive and initial, $\Delta^{t'}_C(c)_{i'} = \#$ for $0 \leq t' \leq -i'$ and $i' < 0$.

Since $\phi(0,i,j) \leq -\psi(i,j)$ and $\psi(i,j) \leq 0$, we have:

$$
w(j) = \# = \Delta^{\phi(0,i,j)}_C(c)_{\psi(i,j)}
$$

**Inductive case ($t \to t+1$):**

Let $x_a := \Delta^t_{C'}(c')_i = \text{compr } w_a$ (compressed tuple at middle) and $x_b := \Delta^t_{C'}(c')_{i+1}$ (right neighbor).

Define $q := \text{asQ}(x_b)$, i.e.:

$$
q := \begin{cases} q_b & \text{if } x_b = \text{single } q_b \\ w_b(0) & \text{if } x_b = \text{compr } w_b \end{cases}
$$

By IH: $q = \Delta^{\phi(t,i+1,0)}_C(c)_{\psi(i+1,0)}$

**Inner descending induction on $j$ (from $k-1$ down to $0$):**

*Case $j = k-1$:*

$$
\begin{aligned}
\big(\Delta^{t+1}_{C'}(c')_i\big)_{k-1} &= \delta'(\_, \text{compr } w_a, x_b)_{k-1} = \text{fold}(w_a, q)_{k-1} = \delta(\#, w_a(k{-}1), q) \\
&= \delta\big(\#, \Delta^{\phi(t,i,k-1)}_C(c)_{\psi(i,k-1)}, \Delta^{\phi(t,i+1,0)}_C(c)_{\psi(i+1,0)}\big) \\
&= \delta\big(\#, \Delta^{\phi(t,i,k-1)}_C(c)_{\psi(i,k-1)}, \Delta^{\phi(t,i,k-1)}_C(c)_{\psi(i,k-1)+1}\big) \\
&= \Delta^{\phi(t+1,i,k-1)}_C(c)_{\psi(i,k-1)}
\end{aligned}
$$

(Uses: $\psi(i+1,0) = \psi(i,k-1)+1$ and $\phi(t,i+1,0) = \phi(t,i,k-1)$, plus one step of $C$'s evolution)

*Case $j$ for $j < k-1$ (given IH for $j+1$):*

$$
\begin{aligned}
\big(\Delta^{t+1}_{C'}(c')_i\big)_{j} &= \text{fold}(w_a, q)_{j} = \delta\big(\#, w_a(j), \text{fold}(w_a, q)_{j+1}\big) \\
&= \delta\big(\#, \Delta^{\phi(t,i,j)}_C(c)_{\psi(i,j)}, \Delta^{\phi(t+1,i,j+1)}_C(c)_{\psi(i,j+1)}\big) \\
&= \delta\big(\#, \Delta^{\phi(t,i,j)}_C(c)_{\psi(i,j)}, \Delta^{\phi(t,i,j)}_C(c)_{\psi(i,j)+1}\big) \\
&= \Delta^{\phi(t+1,i,j)}_C(c)_{\psi(i,j)}
\end{aligned}
$$

(Uses: $\psi(i,j+1) = \psi(i,j)+1$ and $\phi(t+1,i,j+1) = \phi(t,i,j)$)

---

## Intuition

The construction "compresses" $k$ consecutive diagonal cells into a single tuple. The $\text{fold}$ function computes a "staircase" of $k$ transitions simultaneously, exploiting:

1. **Left-independence:** We can always substitute $\#$ for the left neighbor
2. **Passivity of $\#$:** The border region remains stable
3. **Diagonal structure:** Each component of the tuple corresponds to a cell on a different diagonal of the original CA's space-time diagram
