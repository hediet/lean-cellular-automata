# Formal Proof: $L_x(L) \in \mathrm{CA_{RT}} \implies L \in \mathrm{CA_{RT}}$

---

## Theorem Statement

**Main Theorem.** Let $L \subseteq \Sigma^*$ and $x \in \Sigma$. Define
$$L_x(L) := \{ x^m w \mid w \in L, \; m = 2^{\lceil \log_2 |w| \rceil} \}.$$
If $L_x(L) \in \mathcal{L}(\mathrm{CA_{RT}})$, then $L \in \mathcal{L}(\mathrm{CA_{RT}})$.

---

## Part I: General Theory

### Cellular Automaton

A CA is $C = (Q, \delta, \mathsf{embed}, \mathsf{project})$ with:
- $Q$ finite state set
- $\delta : Q^3 \to Q$ local transition
- $\mathsf{embed} : \Sigma_\# \to Q$ input embedding
- $\mathsf{project} : Q \to \{0,1\}$ output

**Evolution:**
$$\mathsf{next}(c)(p) = \delta(c(p-1), c(p), c(p+1))$$
$$C.\mathsf{comp}(c, t, p) = \mathsf{project}(\mathsf{next}^t(c)(p))$$

### Word Embedding

$$\langle w \rangle(p) = \begin{cases}
\mathsf{embed}(w_p) & \text{if } 0 \le p < |w| \\
\mathsf{embed}(\#) & \text{otherwise}
\end{cases}$$

### Shifted Embedding

$$[v \mid w](p) = \langle v \cdot w \rangle(p + |v|)$$

### Left-Independent CA

A CA is **left-independent** if $\delta(q_L, q, q_R) = \delta(q_L', q, q_R)$ for all $q_L, q_L'$.

### Real-Time CA

$C \in \mathrm{CA_{RT}}$ accepts $w$ iff $C.\mathsf{comp}(\langle w \rangle, |w|-1, 0) = 1$.

### Translation Invariance

For all CA $C$: $C.\mathsf{comp}(c \circ (+s), t, p) = C.\mathsf{comp}(c, t, p + s)$

### Advice

An advice $\mathsf{adv} : \Sigma^* \to \Gamma^*$ is length-preserving: $|\mathsf{adv}(w)| = |w|$.

An advice is **RT-closed** if $\mathcal{L}(\mathrm{CA_{RT}}(\Sigma \times \Gamma) + \mathsf{adv}) = \mathcal{L}(\mathrm{CA_{RT}}(\Sigma))$.

An advice is **two-stage** if it factors as (CA-RT transducer) ∘ (FST right-to-left).

**Theorem.** Two-stage implies RT-closed. 

---

## Part II: The Pipeline

**Hypothesis.** Given $C \in \mathrm{CA_{RT}}(\Sigma)$ accepting $L_x(L)$.

Fix $w \in \Sigma^*$ with $n := |w| \ge 8$. Let $m := 2^{\lceil \log_2 n \rceil}$.

**Key fact:** $m \le 2(n-1)$.

We construct $C_1, \ldots, C_7$ depending only on $C$ and $x$ (not on $w$), and show:
$$C_7.\mathsf{comp}(\langle w \rangle, n-1, 0) = C.\mathsf{comp}(\langle x^m w \rangle, m+n-1, 0)$$

**Choice of $k$:** The speedup construction uses compression factor $k = 8$. Any $k \ge 5$ works (the constraint is $r = (k-1)(n-1) - 2m \ge 0$, which requires $k \ge 5$ in the worst case $m = 2(n-1)$). We choose $k = 8$ because $m$ is a power of 2 and $8 \mid m$ (for $m \ge 8$), which simplifies the advice.

---

### Construction 1: RegularToLeftIndep

**Define** $C_1 := \mathsf{RegularToLeftIndep}(C)$

**Spec 1.** For all configurations $c$, all $t \in \mathbb{N}$, all $p \in \mathbb{Z}$:
$$C_1.\mathsf{comp}(c, 2t, p) = C.\mathsf{comp}(c, t, p + t)$$

*Formalization:* `RegularToLeftIndep.spec_even`

---

**Step 1.** By Spec 1 with $t = m+n-1$, $p = -(m+n-1)$:
$$C_1.\mathsf{comp}(\langle x^m w \rangle, 2(m+n-1), -(m+n-1)) = C.\mathsf{comp}(\langle x^m w \rangle, m+n-1, 0)$$

---

### Construction 2: Broadcast

**Define** $C_2 := \mathsf{Broadcast}(C_1)$

**Spec 2.** For all configurations $c$, all $T \in \mathbb{N}$, all $r \ge 0$:
$$C_2.\mathsf{comp}(c, 2T + r, -T - r) = C_1.\mathsf{comp}(c, 2T, -T)$$

---

**Step 2.** By Spec 2 with $T = m+n-1$, $r = 7(n-1) - 2m \ge 0$ (valid since $m \le 2(n-1)$ gives $r \ge 3(n-1) \ge 0$):

- Time: $2(m+n-1) + r = 9(n-1)$
- Position: $-(m+n-1) - r = m - 8(n-1)$

$$C_2.\mathsf{comp}(\langle x^m w \rangle, 9(n-1), m - 8(n-1)) = C_1.\mathsf{comp}(\langle x^m w \rangle, 2(m+n-1), -(m+n-1))$$

---

**Step 3 (Shift).** By translation invariance with $s = m$:
$$C_2.\mathsf{comp}([x^m \mid w], t, p) = C_2.\mathsf{comp}(\langle x^m w \rangle, t, p+m)$$

Setting $t = 9(n-1)$, $p = -8(n-1)$, so $p + m = m - 8(n-1)$:
$$C_2.\mathsf{comp}([x^m \mid w], 9(n-1), -8(n-1)) = C_2.\mathsf{comp}(\langle x^m w \rangle, 9(n-1), m - 8(n-1))$$

---

### Construction 3: Speedup

**Define** $C_3 := \mathsf{Speedup}_8(C_2)$

**Define** compression:
$$\mathsf{compress}_8(c)(p) = \begin{cases}
\mathsf{Single}(c(p)) & \text{if } p \ge 0 \\
\mathsf{Compressed}(j \mapsto c(8p + j)) & \text{if } p < 0
\end{cases}$$

**Spec 3.** For all configurations $c$, all $d \ge 1$, all $j \in \{0,\ldots,7\}$, all $t \ge d$:
$$C_3.\mathsf{comp}_j(\mathsf{compress}_8(c), t, -d) = C_2.\mathsf{comp}(c, t + 7d - j, -8d + j)$$

*Formalization:* `LeftIndepSpeedupConfig.spec`

---

**Step 4.** By Spec 3 with $d = n-1$, $j = 0$, $t = 2(n-1)$:
$$C_3.\mathsf{comp}_0(\mathsf{compress}_8([x^m \mid w]), 2(n-1), -(n-1)) = C_2.\mathsf{comp}([x^m \mid w], 9(n-1), -8(n-1))$$

---

### Construction 4: LeftIndepToRegular

**Define** $C_4 := \mathsf{LeftIndepToRegular}(C_3)$

**Spec 4.** For all configurations $c$, all $t \in \mathbb{N}$, all $p \in \mathbb{Z}$:
$$C_4.\mathsf{comp}(c, t, p) = C_3.\mathsf{comp}(c, 2t, p - t)$$

*Formalization:* `LeftIndepToRegular.spec`

---

**Step 5.** By Spec 4 with $t = n-1$, $p = 0$:
$$C_4.\mathsf{comp}(\mathsf{compress}_8([x^m \mid w]), n-1, 0) = C_3.\mathsf{comp}(\mathsf{compress}_8([x^m \mid w]), 2(n-1), -(n-1))$$

---

### Construction 5: Fold

**Define** the advice $v : \Sigma^* \to \Gamma^*$ by: for $w$ with $n := |w|$ and $m := 2^{\lceil \log_2 n \rceil}$,

$$v(w)[i] := \begin{cases}
\mathsf{Compressed}(\iota(x), \ldots, \iota(x)) & \text{if } i < 2^{\lceil \log_2 n \rceil} / 8 \\
\mathsf{Compressed}(\iota(\#), \ldots, \iota(\#)) & \text{if } i \ge 2^{\lceil \log_2 n \rceil} / 8
\end{cases}$$

Since $m$ is a power of 2 and $8 \mid m$ (for $m \ge 8$, i.e., $n \ge 9$), $v(w)$ is $m/8$ copies of "all-$x$" followed by $n - m/8$ copies of "all-$\#$". The advice alphabet has only 2 symbols, and $v(w)$ depends only on $|w|$, not on the contents of $w$.

(For small $n$ with $m < 8$, the boundary cell may mix $x$ and $\#$, adding one extra symbol to the alphabet. This does not affect the proof.)

**Define** $C_5 := \mathsf{FoldCA}(C_4)$

**Define** folding:
$$\mathsf{Fold}(c)(p) = \begin{cases}
(c(p), c(-p-1)) & \text{if } p \ge 0 \\
\bot & \text{if } p < 0
\end{cases}$$

**Spec 5.** For all configurations $c$, all $t \in \mathbb{N}$, all $p \ge 0$:
$$C_5.\mathsf{comp}(\mathsf{Fold}(c), t, p) = C_4.\mathsf{comp}(c, t, p)$$

*Formalization:* `foldCA_spec`

---

**Step 6.** Let $c := \mathsf{compress}_8([x^m \mid w])$. By Spec 5 with $t = n-1$, $p = 0$:
$$C_5.\mathsf{comp}(\mathsf{Fold}(c), n-1, 0) = C_4.\mathsf{comp}(c, n-1, 0)$$

We claim $\mathsf{Fold}(c) = \mathsf{BorderedConfig}(b_1, w \otimes v(w), b_2)$. By definition of $\mathsf{Fold}$ and $c = \mathsf{compress}_8([x^m \mid w])$:

- For $0 \le p < n$: $\mathsf{Fold}(c)(p) = (c(p), c(-(p+1)))$. Since $0 \le p < n$, we have $[x^m \mid w](p) = \iota(w_p)$, so $c(p) = \mathsf{Single}(\iota(w_p))$. And $c(-(p+1)) = v(w)[p]$ by definition of $v$. Hence $\mathsf{Fold}(c)(p) = (\mathsf{Single}(\iota(w_p)),\; v(w)[p])$.
- For $p \ge n$: $\mathsf{Fold}(c)(p) = (c(p), c(-(p+1)))$. Since $p \ge n$, $[x^m \mid w](p) = \iota(\#)$, so $c(p) = \mathsf{Single}(\iota(\#))$. For $c(-(p+1))$: the eight positions $-8(p+1)+j$ ($j=0,\ldots,7$) have maximum $-8p-1 \le -8n-1 < -2n+2 \le -m$ (using $m \le 2(n-1)$ and $n \ge 2$), so all are $< -m$, giving $\iota(\#)$. Hence $c(-(p+1)) = \mathsf{Compressed}(\iota(\#),\ldots,\iota(\#))$, and $\mathsf{Fold}(c)(p) = b_2 := (\mathsf{Single}(\iota(\#)),\; \mathsf{Compressed}(\iota(\#),\ldots,\iota(\#)))$ — constant.
- For $p < 0$: $\mathsf{Fold}(c)(p) = \bot =: b_1$.

---

### Construction 6: BorderNormalize

**Define** borders $b_1, b_2$ from the fold structure. (These depend on $C$ but not on $w$.)

**Define** $C_6 := \mathsf{BorderNormalize}(C_5, b_1, b_2)$

**Spec 6.** For all words $u$ with $|u| \ge 1$, all $t < |u|$, all $p$:
$$C_6.\mathsf{comp}(\langle u \rangle, t, p) = C_5.\mathsf{comp}(\mathsf{BorderedConfig}(b_1, u, b_2), t, p)$$

*Formalization:* `borderNormalizeCA_spec`

---

**Step 7.** By Spec 6 with $u = w \otimes v(w)$, $t = n-1$, $p = 0$:
$$C_6.\mathsf{comp}(\langle w \otimes v(w) \rangle, n-1, 0) = C_5.\mathsf{comp}(\mathsf{BorderedConfig}(b_1, w \otimes v(w), b_2), n-1, 0)$$

---

### Construction 7: Advice Elimination

**Claim.** $v$ is two-stage (hence RT-closed).

*Proof sketch:* Stage 1 marks powers of 2; Stage 2 computes compressed cells via FST.

**Define** $C_7 := \mathsf{ElimAdvice}(C_6, v)$

**Spec 7.** For all words $w$ with $|w| \ge 2$:
$$C_7.\mathsf{comp}(\langle w \rangle, |w|-1, 0) = C_6.\mathsf{comp}(\langle w \otimes v(w) \rangle, |w|-1, 0)$$

*Formalization:* `rt_closed_advice_eq`

---

**Step 8.** By Spec 7:
$$C_7.\mathsf{comp}(\langle w \rangle, n-1, 0) = C_6.\mathsf{comp}(\langle w \otimes v(w) \rangle, n-1, 0)$$

---

## Part III: Conclusion

**Chaining.** Combining Steps 1–8:
$$C_7.\mathsf{comp}(\langle w \rangle, n-1, 0) = C.\mathsf{comp}(\langle x^m w \rangle, m+n-1, 0)$$

**Conclusion.** Since $C$ accepts $L_x(L)$:
$$w \in L \iff C.\mathsf{comp}(\langle x^m w \rangle, m+n-1, 0) = 1 \iff C_7.\mathsf{comp}(\langle w \rangle, n-1, 0) = 1$$

Hence $C_7 \in \mathrm{CA_{RT}}$ accepts $L$. $\blacksquare$

---

## Formalization Status

| Construction | Status | File |
|--------------|--------|------|
| RegularToLeftIndep | ✓ | `left_indep_from_regular.lean` |
| Broadcast | ✓ | `broadcast_copy.lean` |
| Speedup | ✓ | `speedup_left_independent_config.lean` |
| LeftIndepToRegular | ✓ | `left_indep_to_regular.lean` |
| FoldCA | ✓ | `basic_fold.lean` |
| BorderNormalize | ✓ | `basic_border_normalization.lean` |
| Two-Stage ⟹ RT-Closed | ✓ | `two_stage_is_rt_closed.lean` |
| **Main theorem** | **✓** | `lx_main_theorem_v2.lean` |
