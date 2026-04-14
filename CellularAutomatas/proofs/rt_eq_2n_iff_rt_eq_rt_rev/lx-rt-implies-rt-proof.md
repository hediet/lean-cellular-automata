# Proof: $L_x(L) \in \mathcal{L}(\mathrm{CA_{RT}}) \implies L \in \mathcal{L}(\mathrm{CA_{RT}})$

This document describes the proof of the main theorem `lx_rt_implies_rt`, formalized in [`lx_rt_implies_rt.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/lx_rt_implies_rt.lean). The proof is completely sorry-free.

---

## 1. Setup

### Cellular Automaton

A CA is a tuple $C = (Q, \Sigma, \Gamma, \delta, \mathrm{embed}, \mathrm{project})$ where $\delta : Q^3 \to Q$ is the local rule, $\mathrm{embed} : \Sigma \to Q$, and $\mathrm{project} : Q \to \Gamma$. The split into input/output types lets CAs act as transducers.

A **configuration** is $c : \mathbb{Z} \to Q$. One step: $\mathrm{next}(c)_p = \delta(c_{p-1}, c_p, c_{p+1})$. We write $\Delta^t_C(c)$ for the $t$-fold iterate, and $\mathrm{comp}_C(c, t, i) = \mathrm{project}(\Delta^t_C(\mathrm{embed} \circ c)_i)$.

### Word Embedding (0-indexed)

A word $w$ of length $n$ occupies positions $0, \ldots, n{-}1$, with all others mapped to $\#$:
$$\langle w \rangle(p) = \begin{cases} w_p & \text{if } 0 \le p < |w| \\ \# & \text{otherwise} \end{cases}$$

In the formalization, the input alphabet is $\mathrm{Option}(\Sigma)$, so $\#$ corresponds to `none`.

### Real-Time Acceptance

A CA in $\mathrm{CA_{RT}}$ accepts word $w$ of length $n$ iff $\mathrm{comp}_C(\langle w \rangle, n-1, 0) = \mathrm{true}$.

### Left-Independent CA

A CA is **left-independent** if $\delta$ ignores its left argument:
$$\forall\, a, a', b, c: \; \delta(a, b, c) = \delta(a', b, c)$$

### The Language $L_x(L)$

For a language $L \subseteq \Sigma^*$:
$$L_x(L) = \{ \mathtt{none}^k \cdot w.\mathrm{map}(\mathtt{some}) \mid w \in L,\; k \geq |w| \}$$

This lifts $L$ to $\mathrm{Option}(\Sigma)$ by padding with `none` symbols before embedding words via `some`.

---

## 2. Theorem

```lean
theorem lx_rt_implies_rt {α : Type} [Alphabet α] (L : Language α) :
    L_x L ∈ ℒ (CA_rt (Option α)) → L ∈ ℒ (CA_rt α)
```

---

## 3. Proof Overview

Let $C$ be a CA accepting $L_x(L)$ in real-time, $w \in \Sigma^*$ with $n := |w|$, and $x := \mathtt{none}$.

**Define** $m := 2^{\lceil \log_2 n \rceil}$ (the smallest power of $2$ that is $\geq n$).

Since $L_x(L)$ contains $x^k \cdot w.\mathrm{map}(\mathtt{some})$ for *any* $k \geq n$, and $m \geq n$, we have $x^m w \in L_x(L) \iff w \in L$ (the converse holds because $\mathtt{none}$ and $\mathtt{some}(\cdot)$ are disjoint, making the split unique). Therefore:
$$w \in L \iff x^m w \in L_x(L) \iff C.\mathrm{comp}(\langle x^m w \rangle,\; m + n - 1,\; 0) = 1$$

The goal is to construct $C_{\mathrm{final}}$ that evaluates the right-hand side using only $\langle w \rangle$ as input. This is done through an 8-stage pipeline. The choice of $m$ as a power of $2$ is essential: it ensures $8 \mid m$ (compression alignment in $C_4$) and makes the boundary position $m/8$ detectable by a two-stage advice ($C_{\mathrm{final}}$).

| Construction | CA | is OCA | Configuration | Acceptance (time, pos) |
|-------------|-----|-----|---------------|------------|
| Hypothesis | $C$ | | $\langle x^m w \rangle$ | $(m{+}n{-}1,\; 0)$ |
| Regular → Left-Indep | $C_1$ | ✓ | $\langle x^m w \rangle$ | $(2(m{+}n{-}1),\; {-}(m{+}n{-}1))$ |
| Broadcast ($r = 7(n{-}1){-}2m$) | $C_2$ | ✓ | $\langle x^m w \rangle$ | $(2(m{+}n{-}1){+}r,\; {-}(m{+}n{-}1){-}r) = (9(n{-}1),\; m{-}8(n{-}1))$ |
| Shift | $C_2$ | ✓ | $[x^m \| w]$ where $[v \| w](i) := \langle v{\cdot}w \rangle(i + \lvert v\rvert)$ | $(9(n{-}1),\; {-}8(n{-}1))$ |
| 8-Compression | $C_4$ | ✓ | $\mathrm{compress\_left}_8([x^m \| w])$ <br><br> where $\mathrm{compress\_left}_k(c)(i) := \begin{cases} \mathrm{Single}(c(i)) & i \geq 0 \\ \mathrm{Spatial}(j \mapsto c(ki{+}j)) & i < 0 \end{cases}$ | $(2(n{-}1),\; {-}(n{-}1))$, component 0 |
| Left-Indep → Regular | $C_5$ | | $\mathrm{compress\_left}_8([x^m \| w])$ | $(n{-}1,\; 0)$ |
| Fold | $C_6$ | | $\mathrm{fold}(\mathrm{compress\_left}_8([x^m \| w]))$ <br><br> where $\mathrm{fold}(c)(i) := \begin{cases} \mathrm{some}(c(i),\; c({-}i{-}1)) & i \geq 0 \\ \mathrm{none} & i < 0 \end{cases}$ | $(n{-}1,\; 0)$ |
| Border Normalize | $C_7$ | | $\langle\mathrm{encoded\_word}(w)\rangle$ <br><br> where $\mathrm{encoded\_word}(w)_i := \mathrm{fold}(\mathrm{compress\_left}_8([x^m \| w]))(i)$ for $0 \leq i < n$ | $(n{-}1,\; 0)$ |
| Advice Elimination | $C_{\mathrm{final}}$ | | $\langle w \rangle$ <br><br> since $\mathrm{encoded\_word}(w) = (w \otimes \mathrm{adv}(w)).\mathrm{map}(\mathrm{encode})$ where $\mathrm{adv}(w)_i = (\_ \mapsto \mathtt{some}(x))$ if $i < m/k$, else $(\_ \mapsto \mathtt{none})$. The advice is two-stage and hence RT-closed, so it can be eliminated. | $(n{-}1,\; 0)$ |

Here $k = 8$ is the compression factor. The "OCA" column marks whether the CA is a one-way CA (left-independent). The broadcast requires $r \geq 0$, which holds since $m \leq 2(n{-}1)$.

The pipeline is valid for $n \geq 9$. For $n < 9$, $C_{\mathrm{final}}$ may disagree with $L$, but only on finitely many words. Since $\mathcal{L}(\mathrm{CA_{RT}})$ is closed under finite symmetric difference, $L \in \mathcal{L}(\mathrm{CA_{RT}})$.

---

## 4. Pipeline Details

### $C$: Hypothesis

Given CA $C$ accepting $L_x(L)$ in real-time. As argued above, for $w \in L$ with $n = |w|$ and $m = 2^{\lceil \log_2 n \rceil}$:
$$C.\mathrm{comp}(\langle x^m w \rangle,\; m + n - 1,\; 0) = 1 \iff w \in L$$

### $C_1$: Regular → Left-Independent

**File:** [`left_indep_from_regular.lean`](../CellularAutomatas/proofs/constructions/left_indep_from_regular.lean)

**Lemma.** For any CA $A$, there exists a left-independent CA $A'$ with $Q' = Q \cup (Q \times Q)$ such that:
$$\Delta^{2t}_{A'}(c)_i = \Delta^t_A(c)_{i+t}$$

Setting $t = m + n - 1$ and $i = -(m + n - 1)$:

$$C_1.\mathrm{comp}(\langle x^m w \rangle,\; 2(m+n-1),\; -(m+n-1)) = C.\mathrm{comp}(\langle x^m w \rangle,\; m+n-1,\; 0)$$

The acceptance point has moved from position $0$ to position $-(m+n-1)$, at twice the time. The CA is now left-independent.

### $C_2$: Broadcast

**File:** [`broadcast_oca.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/broadcast_oca.lean)

**Problem.** After $C_1$, acceptance is at position $-(m+n-1)$, which depends on $m$. We need an acceptance point depending only on $n$.

**Lemma (BroadcastOCA).** For any left-independent CA $A$, there exists a left-independent CA $A'$ such that:
$$A'.\mathrm{comp}(c,\; 2T + r,\; -T - r) = A.\mathrm{comp}(c,\; 2T,\; -T)$$

for all $r \geq 0$.

The construction propagates a signal leftward at half speed. The state space is $(Q, \mathrm{Signal}, \mathrm{Option}(\Gamma))$ where $\mathrm{Signal} \in \{0, 1, 2\}$:
- Positions inside the word start with signal 2 (fired) and store the projection.
- Border positions start with signal 0 (waiting).
- Signal propagates: $0 \to 1 \to 2$. At the $0 \to 1$ transition, the cell captures the projection from its right neighbor as a memo, then propagates it diagonally left.

Setting $T = m + n - 1$ and $r = 7(n-1) - 2m$ (see proof overview for derivation):

$$C_2.\mathrm{comp}(\langle x^m w \rangle,\; 9(n-1),\; m - 8(n-1)) = C_1.\mathrm{comp}(\langle x^m w \rangle,\; 2(m+n-1),\; -(m+n-1))$$

The time now depends only on $n$. The position still involves $m$, but that will be absorbed by the shift and compression.

### $C_2$ (cont.): Shift

**Lemma (Translation Invariance).** For any CA $A$:
$$A.\mathrm{comp}(c \circ (+s),\; t,\; p) = A.\mathrm{comp}(c,\; t,\; p + s)$$

Using the identity $[x^m \| w](i) = \langle x^m w \rangle(i + m)$ (shifted embedding), the observation point shifts by $-m$:

$$C_2.\mathrm{comp}([x^m \| w],\; 9(n-1),\; -8(n-1))$$

Now both time and position depend only on $n$.

### $C_4$: 8-Compression (Speedup)

**File:** [`speedup_left_independent_config.lean`](../CellularAutomatas/proofs/constructions/speedup_left_independent_config.lean)

**Lemma (LeftIndepSpeedupConfig).** For any left-independent CA $A$ and compression factor $k$, there exists a left-independent CA $A'$ over states $\mathrm{Single}(Q) \mid \mathrm{Spatial}(Q^k) \mid \mathrm{Diagonal}(Q^k)$ such that for $i < 0$ and $t \geq -i$:
$$A'.\mathrm{comp}(\mathrm{compress\_left}_k(c),\; t,\; i)_j = A.\mathrm{comp}(c,\; (t - (k{-}1)i - j),\; ki + j)$$

The compressed configuration packs $k$ cells into one for negative positions:
$$\mathrm{compress\_left}_k(c)(i) = \begin{cases} \mathrm{Single}(c(i)) & \text{if } i \geq 0 \\ \mathrm{Spatial}(j \mapsto c(ki + j)) & \text{if } i < 0 \end{cases}$$

The two tuple types capture different temporal alignments:
- **Spatial**: all $k$ components at the same original time.
- **Diagonal**: components staggered by 1 original timestep each.

Setting $k = 8$, $i = -(n-1)$, $j = 0$, $t = 2(n-1)$:

$$C_4.\mathrm{comp}_0(\mathrm{compress\_left}_8([x^m \| w]),\; 2(n-1),\; -(n-1)) = C_2.\mathrm{comp}([x^m \| w],\; 9(n-1),\; -8(n-1))$$

**Why $k = 8$?** We need $k \mid m$ so that the compression boundaries align with the $x^m$-prefix boundary. Since $m = 2^{\lceil \log_2 n \rceil}$ and $8 = 2^3$, we have $8 \mid m$ for all $n \geq 8$.

### $C_5$: Left-Independent → Regular

**File:** [`left_indep_to_regular.lean`](../CellularAutomatas/proofs/constructions/left_indep_to_regular.lean)

**Lemma.** For any left-independent CA $A$, there exists a regular CA $A'$ such that:
$$A'.\mathrm{comp}(c,\; t,\; i) = A.\mathrm{comp}(c,\; 2t,\; i - t)$$

This is the inverse of $C_1$. Setting $t = n - 1$, $i = 0$:

$$C_5.\mathrm{comp}(\mathrm{compress\_left}_8([x^m \| w]),\; n-1,\; 0) = C_4.\mathrm{comp}(\ldots,\; 2(n-1),\; -(n-1))$$

Acceptance is now at position 0, time $n-1$: **real-time format**.

### $C_6$: Fold

**File:** [`basic_fold.lean`](../CellularAutomatas/proofs/constructions/basic_fold.lean)

**Lemma.** For any CA $A$, there exists a CA $A'$ over $\mathrm{Option}(Q \times Q)$ such that for $i \geq 0$:
$$A'.\mathrm{comp}(\mathrm{fold}(c),\; t,\; i) = A.\mathrm{comp}(c,\; t,\; i)$$

The fold pairs positive and negative positions:
$$\mathrm{fold}(c)(i) = \begin{cases} \mathrm{some}(c(i),\; c(-i-1)) & \text{if } i \geq 0 \\ \mathrm{none} & \text{if } i < 0 \end{cases}$$

After folding, each cell at position $i \geq 0$ carries both the "right half" state $c(i)$ (the word $w$ encoded via `Single`) and the "left half" state $c(-(i+1))$ (the left-compressed $x^m$-prefix data). The left half becomes the **advice**.

### $C_7$: Border Normalization

**File:** [`basic_border_normalization.lean`](../CellularAutomatas/proofs/constructions/basic_border_normalization.lean)

**Lemma.** For any CA $A$ and border values $b_1, b_2$, there exists a CA $A'$ such that:
$$A'.\mathrm{trace}(\langle u \rangle,\; t) = A.\mathrm{trace}(\mathrm{BorderedConfig}(b_1, u, b_2),\; t)$$

This normalizes the folded configuration (which has non-standard border values) into a standard word embedding. After this step, $C_7$ operates on $\langle\mathrm{encoded\_word}(w)\rangle$ — the word embedding of the finite word of length $n$ extracted from positions $0, \ldots, n{-}1$ of the folded configuration:
$$\mathrm{encoded\_word}(w)_i = \mathrm{fold}(\mathrm{compress\_left}_k([x^m \| w]))(i) \quad \text{for } 0 \leq i < n$$

Each symbol pairs a letter of $w$ with advice data from the left-compressed prefix:

$$C_7.\mathrm{trace}(\mathrm{encoded\_word}(w),\; n-1)_0 = C.\mathrm{comp}(\langle x^m w \rangle,\; m+n-1,\; 0)$$

---

## 5. $C_{\mathrm{final}}$: Advice Elimination

### The Advice

After the pipeline $C_1$–$C_7$, $C_7$ accepts words of the form $w \otimes \mathrm{adv}(w)$, where the advice $\mathrm{adv}(w)$ at position $i$ encodes whether $i$ falls in the $x^m$-prefix region of the compressed configuration:

$$\mathrm{adv}(w)_i = \begin{cases} (\_ \mapsto \mathtt{some}(x)) & \text{if } i < m/k \\ (\_ \mapsto \mathtt{none}) & \text{if } i \geq m/k \end{cases}$$

This is called `xPrefixAdvice` in the formalization (`foldAdvice` in the pipeline).

### Two-Stage Structure

**File:** [`x_prefix_advice_two_stage.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/x_prefix_advice_two_stage.lean)

The advice is **two-stage**, meaning it factors into:

1. **CA stage** (`exp_prefix_CA`): A real-time CA transducer marks position $i$ with `true` iff $i + 1$ is a power of 2. These marks appear at positions $0, 1, 3, 7, 15, \ldots$

2. **FST stage** (`bFST`): A 5-state finite-state transducer scans right-to-left over the marks and determines whether each position falls inside the $x^m$-prefix region. The states are $\{\mathrm{init}, s_2, s_1, s_0, \mathrm{fill}\}$ with transitions:

   | State | On `true` | On `false` |
   |-------|-----------|------------|
   | init  | $s_2$     | $s_2$      |
   | $s_2$ | $s_1$     | $s_2$      |
   | $s_1$ | $s_0$     | $s_1$      |
   | $s_0$ | fill      | $s_0$      |
   | fill  | fill      | fill       |

   Output: `true` iff final state is `fill`.

   The FST outputs `true` at position $i$ iff sufficiently many power-of-2 marks appear in the suffix $[i, n{-}1]$, which is equivalent to $i < m/8$.

```lean
theorem xPrefixAdvice_is_two_stage (x : α) :
    (xPrefixAdvice x k_factor).is_two_stage_advice
```

### RT-Closedness

**File:** [`is_two_stage_of_rt_closed_and_causal.lean`](../CellularAutomatas/proofs/is_two_stage_of_rt_closed_and_causal.lean)

Two-stage advice is RT-closed:
$$\mathcal{L}(\mathrm{CA_{RT}}(\Sigma \times \Gamma) / \mathrm{adv}) = \mathcal{L}(\mathrm{CA_{RT}}(\Sigma))$$

```lean
theorem foldAdvice_rt_closed : e.foldAdvice.rt_closed
```

Since `foldAdvice` is two-stage, it is RT-closed, and can be eliminated:

```lean
theorem exists_CA_rt_of_rt_closed_advice :
    ∃ (C' : CA_rt α), C'.val.L = (C_rt.val + adv).L
```

---
 
## 6. Closing the Gap: Finite Symmetric Difference

The compression arithmetic in the pipeline requires $n \geq k + 1 = 9$ (so that $8 \mid m$ and positional bounds hold). For $n < 9$, $C_{\mathrm{final}}$ may not agree with $L$.

However, the alphabet $\Sigma$ is finite, so there are only finitely many words of length $< 9$. Thus $C_{\mathrm{final}}.L \;\triangle\; L$ is finite. Since $\mathcal{L}(\mathrm{CA_{RT}})$ is closed under finite symmetric difference (any finite language is in $\mathcal{L}(\mathrm{CA_{RT}})$), we conclude $L \in \mathcal{L}(\mathrm{CA_{RT}})$.

```lean
theorem ca_rt_closed_finite_symmDiff :
    C.L ∈ ℒ (CA_rt α) → (symmDiff C.L L).Finite → L ∈ ℒ (CA_rt α)
```

$\blacksquare$

---

## 7. Formalization Status

All components are **completely sorry-free**.

| CA | Construction | File |
|----|-------------|------|
| $C_1$ | RegularToLeftIndep | [`left_indep_from_regular.lean`](../CellularAutomatas/proofs/constructions/left_indep_from_regular.lean) |
| $C_2$ | BroadcastOCA | [`broadcast_oca.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/broadcast_oca.lean) |
| $C_2$ | Shift | Translation invariance (in [`ca_rt_utils.lean`](../CellularAutomatas/proofs/ca_rt_utils.lean)) |
| $C_4$ | 8-Compression | [`speedup_left_independent_config.lean`](../CellularAutomatas/proofs/constructions/speedup_left_independent_config.lean) |
| $C_5$ | LeftIndepToRegular | [`left_indep_to_regular.lean`](../CellularAutomatas/proofs/constructions/left_indep_to_regular.lean) |
| $C_6$ | Fold | [`basic_fold.lean`](../CellularAutomatas/proofs/constructions/basic_fold.lean) |
| $C_7$ | Border Normalize | [`basic_border_normalization.lean`](../CellularAutomatas/proofs/constructions/basic_border_normalization.lean) |
| $C_{\mathrm{final}}$ | Two-Stage Advice | [`x_prefix_advice_two_stage.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/x_prefix_advice_two_stage.lean) |
| — | Main theorem | [`lx_rt_implies_rt.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/lx_rt_implies_rt.lean) |
| — | Two-stage → RT-closed | [`is_two_stage_of_rt_closed_and_causal.lean`](../CellularAutomatas/proofs/is_two_stage_of_rt_closed_and_causal.lean) |
| — | Finite symm diff closure | [`ca_rt_finite_closure.lean`](../CellularAutomatas/proofs/ca_rt_finite_closure.lean) |
