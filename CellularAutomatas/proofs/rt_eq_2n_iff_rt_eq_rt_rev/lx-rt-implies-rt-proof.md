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

The proof transforms a CA $C$ accepting $L_x(L)$ into a CA $C_{\mathrm{final}}$ accepting $L$ through an 8-stage pipeline, followed by a finite-symmetric-difference closure argument.

| Stage | Construction | CA | Configuration | Acceptance |
|-------|-------------|-----|---------------|------------|
| 0 | Hypothesis | $C$ | $\langle x^m w \rangle$ | $(m{+}n{-}1,\; 0)$ |
| 1 | Regular → Left-Indep | $C_1$ | $\langle x^m w \rangle$ | $(2(m{+}n{-}1),\; {-}(m{+}n{-}1))$ |
| 2 | Broadcast | $C_2$ | $\langle x^m w \rangle$ | $(9(n{-}1),\; m - 8(n{-}1))$ |
| 3 | Shift | $C_2$ | $[x^m \| w]$ | $(9(n{-}1),\; {-}8(n{-}1))$ |
| 4 | 8-Compression | $C_4$ | $\mathrm{compress}_8([x^m \| w])$ | $(2(n{-}1),\; {-}(n{-}1))$, component 0 |
| 5 | Left-Indep → Regular | $C_5$ | $\mathrm{compress}_8([x^m \| w])$ | $(n{-}1,\; 0)$ |
| 6 | Fold | $C_6$ | $\mathrm{Fold}(\mathrm{compress}_8([x^m \| w]))$ | $(n{-}1,\; 0)$ |
| 7 | Border Normalize | $C_7$ | $\mathrm{encoded\_word}(w)$ | $(n{-}1,\; 0)$ |
| 8 | Advice Elimination | $C_{\mathrm{final}}$ | $\langle w \rangle$ | $(n{-}1,\; 0)$ |

Here $n = |w|$, $m = 2^{\lceil \log_2 n \rceil}$ (the next power of 2 $\geq n$), and $k = 8$ is the compression factor.

---

## 4. Pipeline (Stages 1–7)

### Stage 0: Hypothesis

Given CA $C$ accepting $L_x(L)$ in real-time. For $w \in L$, set $x = \mathtt{none}$ and $m = 2^{\lceil \log_2 n \rceil} \geq n$. Then:
$$C.\mathrm{comp}(\langle x^m w \rangle,\; m + n - 1,\; 0) = 1 \iff w \in L$$

### Stage 1: Regular → Left-Independent

**File:** [`left_indep_from_regular.lean`](../CellularAutomatas/proofs/constructions/left_indep_from_regular.lean)

**Lemma.** For any CA $A$, there exists a left-independent CA $A'$ with $Q' = Q \cup (Q \times Q)$ such that:
$$\Delta^{2t}_{A'}(c)_i = \Delta^t_A(c)_{i+t}$$

Setting $t = m + n - 1$ and $i = -(m + n - 1)$:

$$C_1.\mathrm{comp}(\langle x^m w \rangle,\; 2(m+n-1),\; -(m+n-1)) = C.\mathrm{comp}(\langle x^m w \rangle,\; m+n-1,\; 0)$$

The acceptance point has moved from position $0$ to position $-(m+n-1)$, at twice the time. The CA is now left-independent.

### Stage 2: Broadcast

**File:** [`broadcast_oca.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/broadcast_oca.lean)

**Problem.** After Stage 1, acceptance is at position $-(m+n-1)$, which depends on $m$. We need an acceptance point depending only on $n$.

**Lemma (BroadcastOCA).** For any left-independent CA $A$, there exists a left-independent CA $A'$ such that:
$$A'.\mathrm{comp}(c,\; 2T + r,\; -T - r) = A.\mathrm{comp}(c,\; 2T,\; -T)$$

for all $r \geq 0$.

The construction propagates a signal leftward at half speed. The state space is $(Q, \mathrm{Signal}, \mathrm{Option}(\Gamma))$ where $\mathrm{Signal} \in \{0, 1, 2\}$:
- Positions inside the word start with signal 2 (fired) and store the projection.
- Border positions start with signal 0 (waiting).
- Signal propagates: $0 \to 1 \to 2$. At the $0 \to 1$ transition, the cell captures the projection from its right neighbor as a memo, then propagates it diagonally left.

Setting $T = m + n - 1$ and $r = 7(n-1) - 2m$ (which is $\geq 0$ since $m \leq 2(n-1)$ for the relevant range):

$$C_2.\mathrm{comp}(\langle x^m w \rangle,\; 9(n-1),\; m - 8(n-1))$$

The time now depends only on $n$. The position still involves $m$, but that will be absorbed by the shift and compression.

### Stage 3: Shift

**Lemma (Translation Invariance).** For any CA $A$:
$$A.\mathrm{comp}(c \circ (+s),\; t,\; p) = A.\mathrm{comp}(c,\; t,\; p + s)$$

Using the identity $[x^m \| w](i) = \langle x^m w \rangle(i + m)$ (shifted embedding), the observation point shifts by $-m$:

$$C_2.\mathrm{comp}([x^m \| w],\; 9(n-1),\; -8(n-1))$$

Now both time and position depend only on $n$.

### Stage 4: 8-Compression (Speedup)

**File:** [`speedup_left_independent_config.lean`](../CellularAutomatas/proofs/constructions/speedup_left_independent_config.lean)

**Lemma (LeftIndepSpeedupConfig).** For any left-independent CA $A$ and compression factor $k$, there exists a left-independent CA $A'$ over states $\mathrm{Single}(Q) \mid \mathrm{Spatial}(Q^k) \mid \mathrm{Diagonal}(Q^k)$ such that for $i < 0$ and $t \geq -i$:
$$A'.\mathrm{comp}(\mathrm{compress}_k(c),\; t,\; i)_j = A.\mathrm{comp}(c,\; (t - (k{-}1)i - j),\; ki + j)$$

The compressed configuration packs $k$ cells into one for negative positions:
$$\mathrm{compress}_k(c)(i) = \begin{cases} \mathrm{Single}(c(i)) & \text{if } i \geq 0 \\ \mathrm{Spatial}(j \mapsto c(ki + j)) & \text{if } i < 0 \end{cases}$$

The two tuple types capture different temporal alignments:
- **Spatial**: all $k$ components at the same original time.
- **Diagonal**: components staggered by 1 original timestep each.

Setting $k = 8$, $i = -(n-1)$, $j = 0$, $t = 2(n-1)$:

$$C_4.\mathrm{comp}_0(\mathrm{compress}_8([x^m \| w]),\; 2(n-1),\; -(n-1)) = C_2.\mathrm{comp}([x^m \| w],\; 9(n-1),\; -8(n-1))$$

**Why $k = 8$?** We need $k \mid m$ so that the compression boundaries align with the $x^m$-prefix boundary. Since $m = 2^{\lceil \log_2 n \rceil}$ and $8 = 2^3$, we have $8 \mid m$ for all $n \geq 8$.

### Stage 5: Left-Independent → Regular

**File:** [`left_indep_to_regular.lean`](../CellularAutomatas/proofs/constructions/left_indep_to_regular.lean)

**Lemma.** For any left-independent CA $A$, there exists a regular CA $A'$ such that:
$$A'.\mathrm{comp}(c,\; t,\; i) = A.\mathrm{comp}(c,\; 2t,\; i - t)$$

This is the inverse of Stage 1. Setting $t = n - 1$, $i = 0$:

$$C_5.\mathrm{comp}(\mathrm{compress}_8([x^m \| w]),\; n-1,\; 0) = C_4.\mathrm{comp}(\ldots,\; 2(n-1),\; -(n-1))$$

Acceptance is now at position 0, time $n-1$: **real-time format**.

### Stage 6: Fold

**File:** [`basic_fold.lean`](../CellularAutomatas/proofs/constructions/basic_fold.lean)

**Lemma.** For any CA $A$, there exists a CA $A'$ over $\mathrm{Option}(Q \times Q)$ such that for $i \geq 0$:
$$A'.\mathrm{comp}(\mathrm{Fold}(c),\; t,\; i) = A.\mathrm{comp}(c,\; t,\; i)$$

The fold pairs positive and negative positions:
$$\mathrm{Fold}(c)(i) = \begin{cases} \mathrm{some}(c(i),\; c(-i-1)) & \text{if } i \geq 0 \\ \mathrm{none} & \text{if } i < 0 \end{cases}$$

After folding, each cell at position $i \geq 0$ carries both the "right half" state $c(i)$ (the word $w$ encoded via `Single`) and the "left half" state $c(-(i+1))$ (the compressed $x^m$-prefix data). The left half becomes the **advice**.

### Stage 7: Border Normalization

**File:** [`basic_border_normalization.lean`](../CellularAutomatas/proofs/constructions/basic_border_normalization.lean)

**Lemma.** For any CA $A$ and border values $b_1, b_2$, there exists a CA $A'$ such that:
$$A'.\mathrm{trace}(\langle u \rangle,\; t) = A.\mathrm{trace}(\mathrm{BorderedConfig}(b_1, u, b_2),\; t)$$

This normalizes the folded configuration (which has non-standard border values) into a standard word embedding. After this step, $C_7$ operates on `encoded_word(w)` — a word of length $n$ where each symbol pairs a letter of $w$ with advice data from the compressed prefix:

$$C_7.\mathrm{trace}(\mathrm{encoded\_word}(w),\; n-1)_0 = C.\mathrm{comp}(\langle x^m w \rangle,\; m+n-1,\; 0)$$

---

## 5. Stage 8: Advice Elimination

### The Advice

After Stages 1–7, $C_7$ accepts words of the form $w \otimes \mathrm{adv}(w)$, where the advice $\mathrm{adv}(w)$ at position $i$ encodes whether $i$ falls in the $x^m$-prefix region of the compressed configuration:

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

The pipeline assumes $m = 2^{\lceil \log_2 n \rceil}$ (exact next power of 2), while $L_x$ allows any $m \geq |w|$. Additionally, the compression arithmetic requires $n \geq 9$ ($= k + 1$ where $k = 8$).

These are handled by a **finite-symmetric-difference** closure argument:

1. **For large words** ($|w| \geq 9$): The pipeline CA $C_{\mathrm{final}}$ agrees with $L$ on all words of length $\geq 9$.
2. **For small words** ($|w| < 9$): There are only finitely many such words, so the symmetric difference $C_{\mathrm{final}}.L \;\triangle\; L$ is finite.
3. **Closure**: $\mathcal{L}(\mathrm{CA_{RT}})$ is closed under finite symmetric difference (since any finite language is in $\mathcal{L}(\mathrm{CA_{RT}})$).

```lean
theorem ca_rt_closed_finite_symmDiff :
    C.L ∈ ℒ (CA_rt α) → (symmDiff C.L L).Finite → L ∈ ℒ (CA_rt α)
```

Therefore $L \in \mathcal{L}(\mathrm{CA_{RT}})$. $\blacksquare$

---

## 7. Formalization Status

All components are **completely sorry-free**.

| Stage | Construction | File |
|-------|-------------|------|
| 1 | RegularToLeftIndep | [`left_indep_from_regular.lean`](../CellularAutomatas/proofs/constructions/left_indep_from_regular.lean) |
| 2 | BroadcastOCA | [`broadcast_oca.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/broadcast_oca.lean) |
| 3 | Shift | Translation invariance (in [`ca_rt_utils.lean`](../CellularAutomatas/proofs/ca_rt_utils.lean)) |
| 4 | 8-Compression | [`speedup_left_independent_config.lean`](../CellularAutomatas/proofs/constructions/speedup_left_independent_config.lean) |
| 5 | LeftIndepToRegular | [`left_indep_to_regular.lean`](../CellularAutomatas/proofs/constructions/left_indep_to_regular.lean) |
| 6 | Fold | [`basic_fold.lean`](../CellularAutomatas/proofs/constructions/basic_fold.lean) |
| 7 | Border Normalize | [`basic_border_normalization.lean`](../CellularAutomatas/proofs/constructions/basic_border_normalization.lean) |
| 8 | Two-Stage Advice | [`x_prefix_advice_two_stage.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/x_prefix_advice_two_stage.lean) |
| — | Main theorem | [`lx_rt_implies_rt.lean`](../CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/lx_rt_implies_rt.lean) |
| — | Two-stage → RT-closed | [`is_two_stage_of_rt_closed_and_causal.lean`](../CellularAutomatas/proofs/is_two_stage_of_rt_closed_and_causal.lean) |
| — | Finite symm diff closure | [`ca_rt_finite_closure.lean`](../CellularAutomatas/proofs/ca_rt_finite_closure.lean) |
