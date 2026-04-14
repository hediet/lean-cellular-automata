#set document(title: "Proof: Lx(L) ∈ L(CA_RT) ⟹ L ∈ L(CA_RT)")
#set page(margin: (x: 2.5cm, y: 2.5cm))
#set text(font: "New Computer Modern", size: 11pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.")
#set block(spacing: 1.2em)
#show heading.where(level: 1): set text(size: 16pt)
#show heading.where(level: 1): set block(above: 1.5em, below: 1em)
#show heading.where(level: 2): set text(size: 13pt)
#show heading.where(level: 2): set block(above: 2em, below: 0.8em)
#show heading.where(level: 3): set text(size: 11pt)
#show heading.where(level: 3): set block(above: 1.5em, below: 0.6em)

// Operator-style names
#let op(name) = math.upright(math.sans(name))
#let comp = op("comp")
#let trace = op("trace")
#let embed = op("embed")
#let project = op("project")
#let next = op("next")
#let fold = op("fold")
#let compressLeft = op("compress_left")
#let encodedWord = op("encoded_word")
#let adv = op("adv")
#let encode = op("encode")
#let Single = op("Single")
#let Spatial = op("Spatial")
#let Diagonal = op("Diagonal")
#let Signal = op("Signal")
#let BorderedConfig = op("BorderedConfig")
#let noneOp = op("none")
#let some = op("some")
#let CAfinal = $C_op("final")$

// Lean code block
#let lean(body) = {
  text(size: 9pt, fill: luma(80))[Lean: #raw(body, lang: "lean")]
}

// Lean file reference
#let leanfile(name) = {
  text(size: 9pt, fill: luma(80))[`#name`]
}

= Proof: $L_x (L) in cal(L)(op("CA")_op("RT")) ==> L in cal(L)(op("CA")_op("RT"))$

This document describes the proof of the main theorem `lx_rt_implies_rt`, formalized in `lx_rt_implies_rt.lean`. The proof is completely sorry-free.

== Setup

=== Cellular Automaton

A CA is a tuple $C = (Q, Sigma, Gamma, delta, embed, project)$ where $delta : Q^3 -> Q$ is the local rule, $embed : Sigma -> Q$, and $project : Q -> Gamma$. The split into input/output types lets CAs act as transducers.

A _configuration_ is $c : ZZ -> Q$. One step: $next(c)_p = delta(c_(p-1), c_p, c_(p+1))$. We write $Delta^t_C (c)$ for the $t$-fold iterate, and $comp_C (c, t, i) = project(Delta^t_C (embed compose c)_i)$.

=== Word Embedding (0-indexed)

A word $w$ of length $n$ occupies positions $0, dots, n-1$, with all others mapped to $hash$:
$ angle.l w angle.r (p) = cases(w_p & "if" 0 <= p < |w|, hash & "otherwise") $

In the formalization, the input alphabet is $op("Option")(Sigma)$, so $hash$ corresponds to `none`.

=== Real-Time Acceptance

A CA in $op("CA")_op("RT")$ accepts word $w$ of length $n$ iff $comp_C (angle.l w angle.r, n-1, 0) = op("true")$.

=== Left-Independent CA (OCA)

A CA is _left-independent_ if $delta$ ignores its left argument:
$ forall a, a', b, c: quad delta(a, b, c) = delta(a', b, c) $
These correspond to _one-way CAs (OCA)_.

=== The Language $L_x (L)$

For a language $L subset.eq Sigma^*$:
$ L_x (L) = { (#noneOp)^k dot w.op("map")(some) mid w in L, k >= |w| } $

This lifts $L$ to $op("Option")(Sigma)$ by padding with `none` symbols before embedding words via `some`.

== Theorem

#lean("theorem lx_rt_implies_rt {α : Type} [Alphabet α] (L : Language α) :
    L_x L ∈ ℒ (CA_rt (Option α)) → L ∈ ℒ (CA_rt α)")

== Proof Overview

Let $C$ be a CA accepting $L_x (L)$ in real-time, $w in Sigma^*$ with $n := |w|$, and $x := noneOp$.

*Define* $m := 2^(ceil(log_2 n))$ (the smallest power of $2$ that is $>= n$).

Since $L_x (L)$ contains $x^k dot w.op("map")(some)$ for _any_ $k >= n$, and $m >= n$, we have $x^m w in L_x (L) <==> w in L$ (the converse holds because $noneOp$ and $some(dot)$ are disjoint, making the split unique). Therefore:
$ w in L <==> x^m w in L_x (L) <==> C.comp(angle.l x^m w angle.r, m + n - 1, 0) = 1 $

The goal is to construct $CAfinal$ that evaluates the right-hand side using only $angle.l w angle.r$ as input. This is done through an 8-step pipeline. The choice of $m$ as a power of $2$ is essential: it ensures $8 divides m$ (compression alignment in $C_4$) and makes the boundary position $m\/8$ detectable by a two-stage advice ($CAfinal$).

#figure(
  table(
    columns: (auto, auto, auto, 1fr, auto),
    align: (left, center, center, left, left),
    stroke: 0.5pt,
    table.header[*Construction*][*CA*][*OCA*][*Configuration*][*Acceptance $(t, p)$*],
    [Hypothesis], $C$, [], $angle.l x^m w angle.r$, [$(m+n-1, 0)$],
    [Regular → OCA], $C_1$, [✓], $angle.l x^m w angle.r$, [$(2(m+n-1), -(m+n-1))$],
    [Broadcast \ ($r = 7(n-1) - 2m$)], $C_2$, [✓], $angle.l x^m w angle.r$, [$(2(m+n-1)+r,$ $-(m+n-1)-r)$ $= (9(n-1),$ $m-8(n-1))$],
    [Shift], $C_2$, [✓], [$[x^m || w]$ \ where $[v || w](i) := angle.l v w angle.r (i + |v|)$], [$(9(n-1), -8(n-1))$],
    [8-Compression], $C_4$, [✓], [$compressLeft_8 ([x^m || w])$ \ \ where $compressLeft_k (c)(i) :=$ \ $Single(c(i))$ if $i >= 0$ \ $Spatial(j |-> c(k i + j))$ if $i < 0$], [$(2(n-1), -(n-1))$, \ component 0],
    [OCA → Regular], $C_5$, [], $compressLeft_8 ([x^m || w])$, [$(n-1, 0)$],
    [Fold], $C_6$, [], [$fold(compressLeft_8 ([x^m || w]))$ \ \ where $fold(c)(i) :=$ \ $some(c(i), c(-i-1))$ if $i >= 0$ \ $noneOp$ if $i < 0$], [$(n-1, 0)$],
    [Border Normalize], $C_7$, [], [$angle.l encodedWord(w) angle.r$ \ \ where $encodedWord(w)_i :=$ \ $fold(compressLeft_8 ([x^m || w]))(i)$ \ for $0 <= i < n$], [$(n-1, 0)$],
    [Advice Elimination], $CAfinal$, [], [$angle.l w angle.r$ \ \ since $encodedWord(w) = (w times.circle adv(w)).op("map")(encode)$ \ where $adv(w)_i = (\_ |-> some(x))$ if $i < m\/k$, \ else $(\_ |-> noneOp)$. \ The advice is two-stage and hence RT-closed, so it can be eliminated.], [$(n-1, 0)$],
  ),
  caption: [Pipeline overview. Here $k = 8$ is the compression factor. "OCA" marks one-way (left-independent) CAs. The broadcast requires $r >= 0$, which holds since $m <= 2(n-1)$.]
)

The pipeline is valid for $n >= 9$. For $n < 9$, $CAfinal$ may disagree with $L$, but only on finitely many words. Since $cal(L)(op("CA")_op("RT"))$ is closed under finite symmetric difference, $L in cal(L)(op("CA")_op("RT"))$.

== Pipeline Details

=== $C$: Hypothesis

Given CA $C$ accepting $L_x (L)$ in real-time. As argued above, for $w in L$ with $n = |w|$ and $m = 2^(ceil(log_2 n))$:
$ C.comp(angle.l x^m w angle.r, m + n - 1, 0) = 1 <==> w in L $

=== $C_1$: Regular → OCA

#leanfile("left_indep_from_regular.lean")

*Lemma.* For any CA $A$, there exists a left-independent CA $A'$ with $Q' = Q union (Q times Q)$ such that:
$ Delta^(2t)_(A') (c)_i = Delta^t_A (c)_(i+t) $

Setting $t = m + n - 1$ and $i = -(m + n - 1)$:
$ C_1.comp(angle.l x^m w angle.r, 2(m+n-1), -(m+n-1)) = C.comp(angle.l x^m w angle.r, m+n-1, 0) $

The acceptance point has moved from position $0$ to position $-(m+n-1)$, at twice the time. The CA is now left-independent.

=== $C_2$: Broadcast

#leanfile("broadcast_oca.lean")

*Problem.* After $C_1$, acceptance is at position $-(m+n-1)$, which depends on $m$. We need an acceptance point depending only on $n$.

*Lemma (BroadcastOCA).* For any left-independent CA $A$, there exists a left-independent CA $A'$ such that:
$ A'.comp(c, 2T + r, -T - r) = A.comp(c, 2T, -T) $
for all $r >= 0$.

The construction propagates a signal leftward at half speed. The state space is $(Q, Signal, op("Option")(Gamma))$ where $Signal in {0, 1, 2}$:
- Positions inside the word start with signal 2 (fired) and store the projection.
- Border positions start with signal 0 (waiting).
- Signal propagates: $0 -> 1 -> 2$. At the $0 -> 1$ transition, the cell captures the projection from its right neighbor as a memo, then propagates it diagonally left.

Setting $T = m + n - 1$ and $r = 7(n-1) - 2m$ (see proof overview for derivation):
$ C_2.comp(angle.l x^m w angle.r, 9(n-1), m - 8(n-1)) = C_1.comp(angle.l x^m w angle.r, 2(m+n-1), -(m+n-1)) $

The time now depends only on $n$. The position still involves $m$, but that will be absorbed by the shift and compression.

=== $C_2$ (cont.): Shift

*Lemma (Translation Invariance).* For any CA $A$:
$ A.comp(c compose (+s), t, p) = A.comp(c, t, p + s) $

Using the identity $[x^m || w](i) = angle.l x^m w angle.r (i + m)$ (shifted embedding), the observation point shifts by $-m$:
$ C_2.comp([x^m || w], 9(n-1), -8(n-1)) $

Now both time and position depend only on $n$.

=== $C_4$: 8-Compression (Speedup)

#leanfile("speedup_left_independent_config.lean")

*Lemma (LeftIndepSpeedupConfig).* For any left-independent CA $A$ and compression factor $k$, there exists a left-independent CA $A'$ over states $Single(Q) | Spatial(Q^k) | Diagonal(Q^k)$ such that for $i < 0$ and $t >= -i$:
$ A'.comp(compressLeft_k (c), t, i)_j = A.comp(c, (t - (k-1)i - j), k i + j) $

The compressed configuration packs $k$ cells into one for negative positions:
$ compressLeft_k (c)(i) = cases(Single(c(i)) & "if" i >= 0, Spatial(j |-> c(k i + j)) & "if" i < 0) $

The two tuple types capture different temporal alignments:
- *Spatial*: all $k$ components at the same original time.
- *Diagonal*: components staggered by 1 original timestep each.

Setting $k = 8$, $i = -(n-1)$, $j = 0$, $t = 2(n-1)$:
$ C_4.comp_0 (compressLeft_8 ([x^m || w]), 2(n-1), -(n-1)) = C_2.comp([x^m || w], 9(n-1), -8(n-1)) $

*Why $k = 8$?* We need $k divides m$ so that the compression boundaries align with the $x^m$-prefix boundary. Since $m = 2^(ceil(log_2 n))$ and $8 = 2^3$, we have $8 divides m$ for all $n >= 8$.

=== $C_5$: OCA → Regular

#leanfile("left_indep_to_regular.lean")

*Lemma.* For any left-independent CA $A$, there exists a regular CA $A'$ such that:
$ A'.comp(c, t, i) = A.comp(c, 2t, i - t) $

This is the inverse of $C_1$. Setting $t = n - 1$, $i = 0$:
$ C_5.comp(compressLeft_8 ([x^m || w]), n-1, 0) = C_4.comp(dots, 2(n-1), -(n-1)) $

Acceptance is now at position 0, time $n-1$: *real-time format*.

=== $C_6$: Fold

#leanfile("basic_fold.lean")

*Lemma.* For any CA $A$, there exists a CA $A'$ over $op("Option")(Q times Q)$ such that for $i >= 0$:
$ A'.comp(fold(c), t, i) = A.comp(c, t, i) $

The fold pairs positive and negative positions:
$ fold(c)(i) = cases(some(c(i), c(-i-1)) & "if" i >= 0, #noneOp & "if" i < 0) $

After folding, each cell at position $i >= 0$ carries both the "right half" state $c(i)$ (the word $w$ encoded via `Single`) and the "left half" state $c(-(i+1))$ (the left-compressed $x^m$-prefix data). The left half becomes the *advice*.

=== $C_7$: Border Normalization

#leanfile("basic_border_normalization.lean")

*Lemma.* For any CA $A$ and border values $b_1, b_2$, there exists a CA $A'$ such that:
$ A'.trace(angle.l u angle.r, t) = A.trace(BorderedConfig(b_1, u, b_2), t) $

This normalizes the folded configuration (which has non-standard border values) into a standard word embedding. After this step, $C_7$ operates on $angle.l encodedWord(w) angle.r$ --- the word embedding of the finite word of length $n$ extracted from positions $0, dots, n-1$ of the folded configuration:
$ encodedWord(w)_i = fold(compressLeft_k ([x^m || w]))(i) quad "for" 0 <= i < n $

Each symbol pairs a letter of $w$ with advice data from the left-compressed prefix:
$ C_7.trace(encodedWord(w), n-1)_0 = C.comp(angle.l x^m w angle.r, m+n-1, 0) $

== $CAfinal$: Advice Elimination

=== The Advice

After the pipeline $C_1$--$C_7$, $C_7$ accepts words of the form $w times.circle adv(w)$, where the advice $adv(w)$ at position $i$ encodes whether $i$ falls in the $x^m$-prefix region of the compressed configuration:
$ adv(w)_i = cases((\_ |-> some(x)) & "if" i < m\/k, (\_ |-> noneOp) & "if" i >= m\/k) $

This is called `xPrefixAdvice` in the formalization (`foldAdvice` in the pipeline).

=== Two-Stage Structure

#leanfile("x_prefix_advice_two_stage.lean")

The advice is *two-stage*, meaning it factors into:

+ *CA stage* (`exp_prefix_CA`): A real-time CA transducer marks position $i$ with `true` iff $i + 1$ is a power of 2. These marks appear at positions $0, 1, 3, 7, 15, dots$

+ *FST stage* (`bFST`): A 5-state finite-state transducer scans right-to-left over the marks and determines whether each position falls inside the $x^m$-prefix region. The states are ${op("init"), s_2, s_1, s_0, op("fill")}$ with transitions:

#figure(
  table(
    columns: 3,
    align: (left, center, center),
    stroke: 0.5pt,
    table.header[*State*][*On `true`*][*On `false`*],
    [init], $s_2$, $s_2$,
    [$s_2$], [$s_1$], [$s_2$],
    [$s_1$], [$s_0$], [$s_1$],
    [$s_0$], [fill], [$s_0$],
    [fill], [fill], [fill],
  ),
  caption: [FST transition table. Output: `true` iff final state is `fill`.]
)

The FST outputs `true` at position $i$ iff sufficiently many power-of-2 marks appear in the suffix $[i, n-1]$, which is equivalent to $i < m\/8$.

#lean("def xPrefixAdvice_is_two_stage (x : α) :
    (xPrefixAdvice x k_factor).is_two_stage_advice")

=== RT-Closedness

#leanfile("is_two_stage_of_rt_closed_and_causal.lean")

Two-stage advice is RT-closed:
$ cal(L)(op("CA")_op("RT") (Sigma times Gamma) \/ adv) = cal(L)(op("CA")_op("RT") (Sigma)) $

Since `foldAdvice` is two-stage, it is RT-closed, and can be eliminated:

#lean("theorem exists_CA_rt_of_rt_closed_advice :
    ∃ (C' : CA_rt α), C'.val.L = (C_rt.val + adv).L")

== Closing the Gap: Finite Symmetric Difference

The compression arithmetic in the pipeline requires $n >= k + 1 = 9$ (so that $8 divides m$ and positional bounds hold). For $n < 9$, $CAfinal$ may not agree with $L$.

However, the alphabet $Sigma$ is finite, so there are only finitely many words of length $< 9$. Thus $CAfinal .L triangle.t L$ is finite. Since $cal(L)(op("CA")_op("RT"))$ is closed under finite symmetric difference (any finite language is in $cal(L)(op("CA")_op("RT"))$), we conclude $L in cal(L)(op("CA")_op("RT"))$.

#lean("theorem ca_rt_closed_finite_symmDiff :
    C.L ∈ ℒ (CA_rt α) → (symmDiff C.L L).Finite → L ∈ ℒ (CA_rt α)")

$qed$

== Formalization Status

All components are *completely sorry-free*.

#figure(
  table(
    columns: 3,
    align: (left, left, left),
    stroke: 0.5pt,
    table.header[*CA*][*Construction*][*File*],
    [$C_1$], [RegularToLeftIndep], leanfile("left_indep_from_regular.lean"),
    [$C_2$], [BroadcastOCA], leanfile("broadcast_oca.lean"),
    [$C_2$], [Shift], leanfile("ca_rt_utils.lean"),
    [$C_4$], [8-Compression], leanfile("speedup_left_independent_config.lean"),
    [$C_5$], [LeftIndepToRegular], leanfile("left_indep_to_regular.lean"),
    [$C_6$], [Fold], leanfile("basic_fold.lean"),
    [$C_7$], [Border Normalize], leanfile("basic_border_normalization.lean"),
    [$CAfinal$], [Two-Stage Advice], leanfile("x_prefix_advice_two_stage.lean"),
    [---], [Main theorem], leanfile("lx_rt_implies_rt.lean"),
    [---], [Two-stage → RT-closed], leanfile("is_two_stage_of_rt_closed_and_causal.lean"),
    [---], [Finite symm diff closure], leanfile("ca_rt_finite_closure.lean"),
  ),
  caption: [Formalization files. All are sorry-free.]
)
