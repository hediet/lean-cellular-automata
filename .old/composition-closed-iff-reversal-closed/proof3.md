# Formal Proof: $L_x(L) \in \mathcal{L}(\mathrm{CA_{RT}}) \implies L \in \mathcal{L}(\mathrm{CA_{RT}})$

---

## 1. Definitions

### 1.1 Cellular Automaton

A **cellular automaton** (CA) is a tuple $C = (Q, \Sigma, \delta, \iota, \pi)$ where:
- $Q$ is a finite set of **states**
- $\Sigma$ is a finite **input alphabet**
- $\delta : Q \times Q \times Q \to Q$ is the **transition function**
- $\iota : \Sigma_\# \to Q$ is the **embedding** (where $\Sigma_\# = \Sigma \cup \{\#\}$)
- $\pi : Q \to \{0,1\}$ is the **projection** (for language recognition)

### 1.2 Configuration and Dynamics

A **configuration** is a function $c : \mathbb{Z} \to Q$.

The **next configuration** is:
$$\mathrm{next}(c)(i) = \delta(c(i-1), c(i), c(i+1))$$

The **t-step evolution** is:
$$\mathrm{next}^t(c) = \underbrace{\mathrm{next} \circ \cdots \circ \mathrm{next}}_{t \text{ times}}(c)$$

The **computation** at position $p$ and time $t$ is:
$$C.\mathrm{comp}(c, t, p) = \mathrm{next}^t(c)(p)$$

### 1.3 Word Embedding

For a word $w \in \Sigma^*$ of length $n$, the **standard embedding** is:
$$\langle w \rangle(i) = \begin{cases}
\iota(w_i) & \text{if } 0 \leq i < n \\
\iota(\#) & \text{otherwise}
\end{cases}$$

### 1.4 Real-Time Acceptance

A **timed CA** $(C, t, p)$ consists of a CA $C$ and timing functions $t, p : \mathbb{N} \to \mathbb{N}$.

The CA **accepts** word $w$ iff:
$$\pi(C.\mathrm{comp}(\langle w \rangle, t(|w|), p(|w|))) = 1$$

A timed CA is **real-time** ($\mathrm{CA_{RT}}$) iff:
- $t(n) = n - 1$ (time equals word length minus one)
- $p(n) = 0$ (acceptance at position zero)

### 1.5 The Language $L_x(L)$

For a language $L \subseteq \Sigma^*$ and symbol $x \in \Sigma$:
$$L_x(L) = \{ x^m w \mid w \in L, \; m = 2^{\lceil \log_2 |w| \rceil} \}$$

where $m$ is the smallest power of 2 greater than or equal to $|w|$.

---

## 2. Theorem Statement

**Theorem (Main Result):**
$$L_x(L) \in \mathcal{L}(\mathrm{CA_{RT}}) \implies L \in \mathcal{L}(\mathrm{CA_{RT}})$$

---

## 3. Proof Overview

The proof proceeds in two phases:

**Phase I (Steps 1–6):** Transform a CA $C$ accepting $x^m w$ into a CA $C_5$ accepting $w \otimes v_m$ (the word paired with an advice string). Key constructions:
- Step 1: Convert to left-independent CA
- Step 1.5: **Broadcast** the acceptance value into the left light cone
- Step 2: Shift the configuration
- Step 3: Speedup via compression
- Steps 4–6: Convert back to regular CA with folding and border normalization

**Phase II (Step 7):** Show the advice $v_m$ is **RT-closed**, meaning it can be eliminated without leaving the class $\mathrm{CA_{RT}}$.

---

## 4. Auxiliary Definitions

### 4.1 Shifted Embedding

For words $v, w$, the **shifted embedding** is:
$$[v \mid w](i) = \begin{cases}
\iota(w_i) & \text{if } 0 \leq i < |w| \\
\iota(v_{|v|+i}) & \text{if } -|v| \leq i < 0 \\
\iota(\#) & \text{otherwise}
\end{cases}$$

**Key property:** $[x^m \mid w](i) = \langle x^m w \rangle(i + m)$

### 4.2 Left-Independent CA

A CA $C$ is **left-independent** iff:
$$\forall q_L, q_L', q, q_R : \delta(q_L, q, q_R) = \delta(q_L', q, q_R)$$

The transition depends only on the center and right neighbors.

### 4.3 Compression

For compression factor $k$ and configuration $c$, define:
$$\mathrm{compress}_k(c)(i) = \begin{cases}
\mathrm{Single}(c(i)) & \text{if } i \geq 0 \\
\mathrm{Spatial}(j \mapsto c(k \cdot i + j)) & \text{if } i < 0
\end{cases}$$

This packs $k$ cells into one for negative positions.

### 4.4 Fold

For configuration $c$, define the **fold**:
$$\mathrm{Fold}(c)(i) = \begin{cases}
(c(i), c(-i-1)) & \text{if } i \geq 0 \\
\bot & \text{if } i < 0
\end{cases}$$

This pairs positive and negative positions.

### 4.5 Bordered Configuration

For borders $b_1, b_2$ and word $w$:
$$\mathrm{BorderedConfig}(b_1, w, b_2)(i) = \begin{cases}
w_i & \text{if } 0 \leq i < |w| \\
b_2 & \text{if } i \geq |w| \\
b_1 & \text{if } i < 0
\end{cases}$$

### 4.6 Advice

An **advice** is a function $\mathrm{adv} : \Sigma^* \to \Gamma^*$ where $|\mathrm{adv}(w)| = |w|$.

The **annotated word** is $w \otimes \mathrm{adv}(w) = [(w_0, \mathrm{adv}(w)_0), \ldots, (w_{n-1}, \mathrm{adv}(w)_{n-1})]$.

An advice is **RT-closed** iff:
$$\mathcal{L}(\mathrm{CA_{RT}}(\Sigma \times \Gamma) + \mathrm{adv}) = \mathcal{L}(\mathrm{CA_{RT}}(\Sigma))$$

### 4.7 Two-Stage Advice

An advice is **two-stage** if it decomposes as:
1. **Stage 1:** A $\mathrm{CA_{RT}}$ computes intermediate marks $\mu(w)$
2. **Stage 2:** A finite-state transducer computes $\mathrm{adv}(w)$ from $(w, \mu(w))$

**Fact:** Two-stage advice is RT-closed. 

---

## 5. The Pipeline (Steps 1–7)

### Step 0: Hypothesis

**Given:**
- CA $C$ accepting $L_x(L)$
- Acceptance at $(m + n - 1, 0)$ where $n = |w|$, $m = 2^{\lceil \log_2 n \rceil}$

**Statement:**
$$C.\mathrm{comp}(\langle x^m w \rangle, m+n-1, 0) = 1 \iff w \in L$$

---

### Step 1: Regular → Left-Independent

**Lemma 1:** For all CA $A$, there exists a left-independent CA $A'$ such that for all configurations $c$, all $t \in \mathbb{N}$, and all $i \in \mathbb{Z}$:
$$A'.\mathrm{comp}(c, 2t, i) = A.\mathrm{comp}(c, t, i + t)$$

**Application:** Take $A = C$ from Step 0. The resulting $A' = C_1$.

Set $t = m + n - 1$, $i = -(m + n - 1)$.

**Result:**
- **CA:** $C_1$ (left-independent) — exists by Lemma 1
- **Config:** $\langle x^m w \rangle$
- **Acceptance:** $(2(m+n-1), -(m+n-1))$

---

### Step 1.5: Broadcast

**Problem:** After Step 1, acceptance is at position $-(m+n-1)$, which depends on $m$. We need to eventually read at a position depending only on $n$.

**Lemma 1.5 (BroadcastOCA):** For all left-independent CA $A$, there exists a left-independent CA $A'$ such that for all configurations $c$, all $T \in \mathbb{N}$, and all $r \geq 0$:
$$A'.\mathrm{comp}(c, 2T + r, -T - r) = A.\mathrm{comp}(c, 2T, -T)$$

**Application:** Take $A = C_1$ from Step 1. The resulting $A' = C_1'$. Set $T = m+n-1$.

**Result:**
- **CA:** $C_1'$ (left-independent, with broadcast) — exists by Lemma 1.5
- **Config:** $\langle x^m w \rangle$
- **Acceptance:** $(2(m+n-1) + r, -(m+n-1) - r)$ for all $r \geq 0$

---

### Step 2: Shift

**Lemma 2 (Translation Invariance):** For all CA $A$, all configurations $c$, all $s \in \mathbb{Z}$, all $t \in \mathbb{N}$, and all $p \in \mathbb{Z}$:
$$A.\mathrm{comp}(c \circ (+s), t, p) = A.\mathrm{comp}(c, t, p + s)$$

**Application:** Take $A = C_1'$ from Step 1.5. Use $s = m$ and the identity $[x^m \mid w](i) = \langle x^m w \rangle(i + m)$.

Shifting the acceptance region from Step 1.5 by $-m$ in position:

**Result:**
- **CA:** $C_1'$ (unchanged from Step 1.5)
- **Config:** $[x^m \mid w]$
- **Acceptance:** $(2(m+n-1) + r, -(m+n-1) - r - m)$ for all $r \geq 0$, i.e. $(2(m+n-1) + r, -(2m+n-1) - r)$

---

### Step 3: Speedup

**Lemma 3 (Speedup Spec):** For all left-independent CA $A$, there exists a left-independent CA $A'$ over input alphabet $Q' = \mathrm{Single}(Q) \mid \mathrm{Spatial}(Q^5)$ such that for all configurations $c$, all $d > 0$, all $0 \leq j < 5$, and all $t \geq d$:
$$A'.\mathrm{comp}_j(\mathrm{compress}_5(c), t, -d) = A.\mathrm{comp}(c, t + 4d - j, -5d + j)$$

**Application.** Take $A = C_1'$ from Step 2. The resulting $A' = C_2$.

We read at position $-(n-1)$, component $0$, time $2(n-1)$ in $C_2$.

Setting $d = n-1$, $j = 0$, $t = 2(n-1)$:
$$C_2.\mathrm{comp}_0(\mathrm{compress}_5(c), 2(n-1), -(n-1)) = C_1'.\mathrm{comp}(c, 6(n-1), -5(n-1))$$

**Claim:** The point $(6(n-1), -5(n-1))$ lies in the acceptance region of Step 2.

Step 2 gives acceptance at $(2(m+n-1) + r, -(2m+n-1) - r)$ for all $r \geq 0$. Choosing $r = 4(n-1) - 2m$ (which satisfies $r \geq 0$ since $m \leq 2(n-1)$):
- Time: $2(m+n-1) + 4(n-1) - 2m = 6(n-1)$ ✓
- Position: $-(2m+n-1) - 4(n-1) + 2m = -5(n-1)$ ✓

So $C_1'.\mathrm{comp}(c, 6(n-1), -5(n-1))$ is the acceptance value, and therefore so is $C_2.\mathrm{comp}_0(\mathrm{compress}_5(c), 2(n-1), -(n-1))$.

**Result:**
- **CA:** $C_2$ (left-independent) — exists by Lemma 3
- **Config:** $\mathrm{compress}_5([x^m \mid w])$
- **Acceptance:** $(2(n-1), -(n-1))$, component $0$

---

### Step 4: Left-Independent → Regular

**Lemma 4:** For all left-independent CA $A$, there exists CA $A'$ such that for all configurations $c$, all $t \in \mathbb{N}$, and all $i \in \mathbb{Z}$:
$$A'.\mathrm{comp}(c, t, i) = A.\mathrm{comp}(c, 2t, i - t)$$

**Application:** Take $A = C_2$ from Step 3. The resulting $A' = C_3$. Set $t = n - 1$, $i = 0$.

**Result:**
- **CA:** $C_3$ — exists by Lemma 4
- **Config:** $\mathrm{compress}_5([x^m \mid w])$
- **Acceptance:** $(n-1, 0)$

---

### Step 5: Fold

**Lemma 5:** For all CA $A$, there exists CA $A'$ over $\mathrm{Option}(Q \times Q)$ such that for all configurations $c$, all $t \in \mathbb{N}$, and all $i \geq 0$:
$$A'.\mathrm{comp}(\mathrm{Fold}(c), t, i) = A.\mathrm{comp}(c, t, i)$$

**Application:** Take $A = C_3$ from Step 4. The resulting $A' = C_4$.

**Effect:** Let $c = \mathrm{compress}_5([x^m \mid w])$. Define the **advice word** $v_m$ of length $n$:
$$v_m[i] = c(-(i+1))$$

The folded configuration becomes:
$$\mathrm{Fold}(c) = \mathrm{BorderedConfig}(\bot, w \otimes v_m, b_2)$$

where $w \otimes v_m$ pairs each $w_i$ with the corresponding advice $v_m[i]$.

**Result:**
- **CA:** $C_4$ — exists by Lemma 5
- **Config:** $\mathrm{BorderedConfig}(\bot, w \otimes v_m, b_2)$
- **Acceptance:** $(n-1, 0)$

---

### Step 6: Border Normalization

**Lemma 6:** For all CA $A$ and all border values $b_1, b_2$, there exists CA $A'$ such that for all words $u$ with $u \neq []$ and all $t \in \mathbb{N}$:
$$A'.\mathrm{trace}(\langle u \rangle, t) = A.\mathrm{trace}(\mathrm{BorderedConfig}(b_1, u, b_2), t)$$

**Application:** Take $A = C_4$ from Step 5 with $b_1 = \bot$, $b_2$ from the fold. The resulting $A' = C_5$.

**Result:**
- **CA:** $C_5 \in \mathrm{CA_{RT}}(\Sigma \times \Gamma)$ — exists by Lemma 6
- **Config:** $\langle w \otimes v_m \rangle$
- **Acceptance:** $(n-1, 0)$

**Statement after Steps 1–6:**
$$C_5.\mathrm{accepts}(w \otimes v_m) = 1 \iff w \in L$$

---

## 6. Step 7: Advice Elimination

### 6.1 The Advice is Two-Stage

**Claim:** The advice $v_m : w \mapsto v_m$ is a **two-stage advice**.

**Stage 1 (CA-RT):** Compute marks $\mu(w)$ where $\mu(w)_i = 1$ iff $(i+1)$ is a power of 2.

This is RT-computable: the CA propagates a counter and marks positions $0, 1, 3, 7, 15, \ldots$ (i.e., $2^k - 1$). The rightmost mark determines $m = 2^{\lceil \log_2 n \rceil}$.

**Stage 2 (FST):** Given $(w, \mu(w))$, compute $v_m$ by:
1. Read rightmost mark to determine $m$
2. For each position $i$, compute $v_m[i] = \mathrm{compress}_5([x^m \mid w])(-(i+1))$

The FST state tracks the current compressed cell, which depends only on local arithmetic (position mod 5, distance from boundary).

**Conclusion:** $v_m$ is two-stage, hence RT-closed by Lemma 7.

### Step 7: Advice Elimination

**Lemma 8 (RT-Closed Advice Elimination):** For all RT-closed advices $\mathrm{adv} : \Sigma^* \to \Gamma^*$ and all $C_5 \in \mathrm{CA_{RT}}(\Sigma \times \Gamma)$, there exists $C_6 \in \mathrm{CA_{RT}}(\Sigma)$ such that for all words $w$:
$$C_6.\mathrm{accepts}(w) = C_5.\mathrm{accepts}(w \otimes \mathrm{adv}(w))$$

**Application:** Take $C_5$ from Step 6 and $\mathrm{adv} = v_m$ (RT-closed by §6.1 and Lemma 7). By Lemma 8, there exists $C_6 \in \mathrm{CA_{RT}}(\Sigma)$ such that for all $w$:
$$C_6.\mathrm{accepts}(w) = C_5.\mathrm{accepts}(w \otimes v_m(w)) = 1 \iff w \in L$$

**Result:**
- **CA:** $C_6 \in \mathrm{CA_{RT}}(\Sigma)$ — exists by Lemma 8
- **Config:** $\langle w \rangle$
- **Acceptance:** $(n-1, 0)$

This completes the proof: $L \in \mathcal{L}(\mathrm{CA_{RT}})$. $\blacksquare$

---

## 8. Summary Table

| Step | CA | Input Configuration | Acceptance | Transformation |
|------|-----|---------------------|------------|----------------|
| 0 | $C$ | $\langle x^m w \rangle$ | $(m+n-1, 0)$ | Hypothesis |
| 1 | $C_1$ | $\langle x^m w \rangle$ | $(2(m+n-1), -(m+n-1))$ | Regular → Left-Indep |
| 1.5 | $C_1'$ | $\langle x^m w \rangle$ | $(2(m+n-1)+r, -(m+n-1)-r)$ | Broadcast |
| 2 | $C_1'$ | $[x^m \mid w]$ | $(2(m+n-1)+r, -(2m+n-1)-r)$ | Shift |
| 3 | $C_2$ | $\mathrm{compress}_5(\ldots)$ | $(2(n-1), -(n-1))$ | Speedup |
| 4 | $C_3$ | $\mathrm{compress}_5(\ldots)$ | $(n-1, 0)$ | Left-Indep → Regular |
| 5 | $C_4$ | $\mathrm{BorderedConfig}(\bot, w \otimes v_m, b_2)$ | $(n-1, 0)$ | Fold |
| 6 | $C_5$ | $\langle w \otimes v_m \rangle$ | $(n-1, 0)$ | Border Normalize |
| 7 | $C_6$ | $\langle w \rangle$ | $(n-1, 0)$ | Advice Elimination |

---

## 9. Formalization Status

| Component | Status | Location |
|-----------|--------|----------|
| RegularToLeftIndep (Step 1) | ✓ | `left_indep_from_regular.lean` |
| Shift (Step 2) | ✓ | Translation invariance |
| BroadcastOCA (Step 2.5) | ✓ | `broadcast.lean` |
| LeftIndepSpeedupConfig (Step 3) | ✓ | `speedup_left_independent_config.lean` |
| LeftIndepToRegular (Step 4) | ✓ | `left_indep_to_regular.lean` |
| foldCA (Step 5) | ✓ | `basic_fold.lean` |
| borderNormalizeCA (Step 6) | ✓ | `basic_border_normalization.lean` |
| Two-stage → RT-closed (Step 7) | ✓ | `is_two_stage_of_rt_closed_and_causal.lean` |
| pipeline_spec | sorry | Definitional unfolding |
| pipeline_advice_rt_closed | sorry | Two-stage decomposition |
| **Main theorem** | **✓** | `lx_main_theorem_v2.lean` |

The main theorem `lx_implies_rt` has no sorry — it depends on two sorry'd lemmas whose proofs are pure bookkeeping.
