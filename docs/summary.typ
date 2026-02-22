#set document(title: "Formalized Cellular Automata Theory in Lean 4")
#set page(margin: (x: 2.5cm, y: 2.5cm))
#set text(font: "New Computer Modern", size: 11pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: none)
#set block(spacing: 1.2em)
#show heading.where(level: 1): set text(size: 16pt)
#show heading.where(level: 1): set block(above: 1.5em, below: 1em)
#show heading.where(level: 2): set text(size: 13pt)
#show heading.where(level: 2): set block(above: 2em, below: 0.8em)
#show heading.where(level: 3): set text(size: 11pt)
#show heading.where(level: 3): set block(above: 1.5em, below: 0.6em)

// Operator-style names for multi-character math identifiers
#let op(name) = math.upright(math.sans(name))
#let trace = op("trace")
#let tracert = op("trace_rt")
#let comp = op("comp")
#let embed = op("embed")
#let project = op("project")
#let next = op("next")

// Sorry status badge
#let sorry-status(body) = {
  h(1fr)
  text(size: 9pt, style: "italic", fill: luma(100))[#body]
}
// Lean reference
#let lean(body) = {
  text(size: 9pt, fill: luma(80))[Lean: #raw(body)]
}

= Formalized Cellular Automata Theory in Lean 4

This project formalizes key results about cellular automata that recognize languages, focusing on *real-time* recognition, *one-way (left-independent) CAs*, and *advice mechanisms*. All results compile with Lean 4 and Mathlib4; proofs are axiom-verified (only `Quot.sound`, `Classical.choice`, and `propext` are used).

== Setup and Non-Standard Definitions

=== Cellular Automaton

A CA is a one-dimensional cellular automaton with radius-1 neighborhood, given as a tuple $C = (Q, Sigma, Gamma, delta, embed, project)$ with state set $Q$, input alphabet $Sigma$, output alphabet $Gamma$, local transition $delta : Q^3 -> Q$, and maps $embed: Sigma -> Q$, $project: Q -> Gamma$. The split into input/output types lets CAs act as transducers.

A *configuration* is a map $c : ZZ -> Q$. One step: $next(c)_p = delta(c_(p-1), c_p, c_(p+1))$. We write $Delta^t_C (c)$ for the $t$-fold iterate, and $comp_C (c, t, i) = project(Delta^t_C (embed compose c)_i)$.

=== Word Embedding (0-indexed)

Words are embedded into configurations with *0-based indexing*: a word $w$ of length $n$ occupies positions $0, 1, dots, n-1$, with all other positions set to the border symbol $hash$. Formally:

$ angle.l w angle.r (p) = cases(w_p & "if" 0 <= p < |w|, hash & "otherwise") $

For language-recognizing CAs the input alphabet is $Sigma_hash = Sigma union {hash}$, so $embed(hash)$ gives the border state. Note that in this formalization, the border state has *no a priori constraints* — it need not be quiescent or dead. This is more general than many textbook definitions, which assume $delta(hash, hash, hash) = hash$. Results 4 and 5 below show that a passive or dead border can always be imposed without changing the recognized language, so this generalization is conservative and the language classes agree with the standard ones.

=== Trace

The *trace* of $C$ on configuration $c$ is the temporal output sequence at position 0:

$ trace_C (c) : NN -> Gamma, quad t |-> comp_C (c, t, 0) $

=== Real-Time Trace

The *real-time trace* is the word-to-word transduction where position $i$ reads out time $i$:

$ tracert_C (w) = (trace_C (angle.l w angle.r)(0), trace_C (angle.l w angle.r)(1), dots, trace_C (angle.l w angle.r)(n-1)) $

This is the central notion for composing CA transducers: $tracert_C : Sigma^* -> Gamma^*$ is a length-preserving map.

=== Left-Independent (One-Way) CA

A CA is *left-independent* if $delta$ ignores its left argument:
$ forall a, a', b, c: quad delta(a, b, c) = delta(a', b, c) $
These correspond to *one-way CAs (OCA)*. The *left-independent light cone* at position $p$ and time $t$ for a word of length $n$ is ${p mid -t <= p < n}$.

=== Real-Time Language Class $cal(L)(op("CA")_op("rt"))$

A CA *accepts* a word $w$ of length $n$ by reading a designated cell at a designated time. A *timed CA* specifies functions $t(n)$ (time) and $p(n)$ (position) and accepts $w$ iff $comp_C (angle.l w angle.r, t(|w|), p(|w|)) = op("true")$.

For the standard classes:
- $op("CA")$: read position 0, i.e. $p(n) = 0$.
- $op("CA")_op("rt")$: read position 0 at time $n - 1$ (real-time).
- $op("OCA")$: left-independent CA reading at position 0.
- $op("OCA")_op("rt")$: left-independent, real-time.

The class $cal(L)(op("CA")_op("rt"))$ is the set of languages recognized by real-time CAs. Note the 0-indexed embedding: a word of length $n$ occupies positions $0, dots, n-1$, and at time $n - 1$ the information from the rightmost cell has just reached position 0.

=== Advice Functions

An *advice* is a length-preserving map $f : Sigma^* -> Gamma^*$ with $|f(w)| = |w|$.

- *RT-closed:* $f$ is RT-closed if $cal(L)(op("CA")_op("rt") (Sigma times Gamma) \/ f) = cal(L)(op("CA")_op("rt") (Sigma))$, i.e.~the advice does not increase the power of real-time CAs.
- *Causal (prefix-stable):* $f(w_([0..i))) = f(w)_([0..i))$ for all $w, i$.
- *Two-stage:* $f$ factors as $f = M compose tracert_C$, where $C$ is a CA real-time transducer and $M$ is a finite-state transducer scanning right-to-left.

== Part I: Classical Constructions (existing literature, sorry-free)

#line(length: 100%, stroke: 0.5pt + luma(180))

The following results are well-known in the literature (see e.g.~Kutrib, Malcher et al.). The proofs here sometimes differ from the classical ones, as certain constructions were adapted to be more amenable to formal verification in Lean 4. All proofs are *completely sorry-free*.

=== Result 1: Left-Independent ↔ Regular Simulation

Given a left-independent CA $C$, construct a regular CA $C'$ such that:

$ Delta^t_(C') (c)_i = Delta^(2t)_C (c)_(i-t) $

Conversely, given any CA $C$, construct a left-independent $C'$ with $Q' = Q union (Q times Q)$ such that:

$ Delta^(2t)_(C') (c)_i = Delta^t_C (c)_(i+t) $

This establishes the equivalence of OCA and CA up to a constant factor of 2 in time.

#lean("result_left_indep_to_regular, result_regular_to_left_indep")

=== Result 2: $k$-Step Left-Independent Speedup

Given a left-independent CA $C = (Q, delta)$ and $k >= 2$, construct a left-independent $C' = (Q^k, delta')$ compressing $k$ consecutive diagonal cells into one tuple. Define coordinate maps:

$ psi(i, j) = k i + j, quad phi(t, i, j) = t - (k-1)i - j $

Then for $i < 0$ and $0 <= j < k$:

$ comp_(C') (w, t, i)_j = comp_C (w, phi(t,i,j), psi(i,j)) $

The proof proceeds by outer induction on $t$ and inner descending induction on $j$ within each time step.

#lean("result_left_indep_speedup")

=== Result 3: General $k$-Step RT Speedup

For any CA $C$ and constant $k$, construct $C'$ such that:

$ trace_(C') (w)(i) = trace_C (w)(i + k) $

This achieves a constant additive speedup by chaining QuiescentBorder and DeadBorder constructions.

#lean("SpeedupKSteps.spec")

=== Result 4: Quiescent Border for Left-Independent CAs

Given a left-independent CA $C$, construct $C'$ whose border is *quiescent* ($delta(hash, hash, hash) = hash$), while $comp_(C') = comp_C$ inside the left-independent light cone. Together with Result 5, this shows that the unconstrained border in our formalization is without loss of generality.

#lean("result_quiescent_border_left_indep")

=== Result 5: Dead Border

Given any CA $C$, construct $C'$ whose border state $hash$ is *dead* (absorbing: $delta(dot, hash, dot) = hash$), while preserving the trace: $trace_(C') (w)(t) = trace_C (w)(t)$ for all $t < c dot |w|$, where $c$ is a constant depending on $C'$. In particular, the trace is preserved for any linear-time computation. Uses a zigzag folding of cells into lanes.

#lean("result_dead_border")

=== Result 6: Exponential Word Length is RT-Recognizable

The language ${ w mid |w| = 2^n "for some" n }$ is in $cal(L)(op("CA")_op("rt"))$. The construction uses a signal-bouncing technique: a signal is sent from the left border, bounces off the right border, and its return time encodes the word length.

#lean("exp_word_length_rt")

== Part II: Advice Theory (likely novel, sorry-free)

#line(length: 100%, stroke: 0.5pt + luma(180))

The following results are likely *novel* and form the core contribution of this project. They develop a structural theory of _advice_ for cellular automata, establishing closure properties of RT transducers and two-stage advice, and classifying causal RT-closed advice as RT transducers.

=== Result 7: RT transducers are closed under composition #sorry-status[sorry-free]

Given CA transducers $C_1 : Sigma -> Gamma_1$ and $C_2 : Gamma_1 -> Gamma_2$, there exists a CA $C$ with $tracert_C = tracert_(C_2) compose tracert_(C_1)$. This is the most technically challenging result in the project, requiring the full machinery of dead border, passive border, $k$-step speedup, and left-independent ↔ regular simulation. The proof uses a multi-stage pipeline:

$ op("AddBorder") -> op("CompressToDiag") -> op("SimFrom") Lambda -> op("DecompressTriple") -> op("SpeedupKSteps") $

#lean("result_rt_transducers_closed_under_composition")

=== Result 8: Two-stage advice is RT-closed #sorry-status[sorry-free]

If $f$ is two-stage, then $cal(L)(op("CA")_op("rt") (Sigma times Gamma) \/ f) = cal(L)(op("CA")_op("rt") (Sigma))$. This follows from Result 7: the CA component is RT-closed, and the right-to-left FST can be absorbed into the receiving CA.

#lean("result_two_stage_is_rt_closed")

=== Result 9: Prefix-membership advice is two-stage #sorry-status[sorry-free]

For any $L in cal(L)(op("CA")_op("rt"))$, the advice $f_L$ defined by

$ f_L (w)_i = [w_([0..i+1)) in L] $

is itself a two-stage advice (and hence an RT transducer): $f_L = tracert_C$ for a suitable CA $C$ that runs the recognizer for $L$ and outputs the acceptance bit at each step.

#lean("result_advice_prefix_mem_is_two_stage_advice")

=== Result 10: RT-closed $and$ causal $==>$ CArt advice #sorry-status[sorry-free]

If an advice $f$ is both RT-closed and causal (prefix-stable), then $f$ is a CArt advice, i.e., computable by a single CA RT transducer. The proof constructs $C$ by observing that causality lets one reduce $f$ to a product of prefix-membership advices (one for each output symbol $c in Gamma$, via the language $L_c = {w mid f(w)_(|w|) = c}$), each of which is an RT transducer by Result 9.

#lean("result_is_cart_advice_of_rt_closed_and_causal")

=== Result 11: Two-stage advice is closed under composition #sorry-status[sorry-free]

Given two-stage advices $f_1 : Sigma^* -> Gamma_1^*$ and $f_2 : Gamma_1^* -> Gamma_2^*$, the composition $f_2 compose f_1$ is again two-stage. The proof works by commuting the FST of $f_1$ past the CA of $f_2$ using a "backwards FSM" construction that absorbs the FST into the CA's state space.

#lean("result_two_stage_closed_under_composition")

=== Result 12: Middle advice is _not_ two-stage #sorry-status[sorry-free]

The advice $f_"mid"$ that marks position $floor(n\/2)$ (i.e., $f_"mid" (w)_i = [i = floor(|w|\/2)]$) cannot be expressed as a two-stage advice. The proof uses a bottleneck argument: the FST has finitely many states, but the middle position requires information about the full word length, which the CA's real-time trace at the midpoint cannot encode in bounded state.

#lean("result_middle_not_two_stage_advice")

== Incomplete Results (with sorry)

#line(length: 100%, stroke: 0.5pt + luma(180))

=== Exponential-Middle Advice is Two-Stage #sorry-status[4 sorry remaining]

The advice that marks the largest power-of-2 position $<= n\/2$ is conjectured to be two-stage. The two-stage decomposition (a CA transducer marking powers of 2, composed with an FST selecting the last "true") is fully constructed. The 4 remaining `sorry`s are in combinatorial counting lemmas.

#lean("exp_middle_two_stage_advice")

=== Unproven Conjectures #sorry-status[8 sorry in results_unproven.lean]

The following are stated but unproven:

- *Constant speedup:* $cal(L)({C in op("CA") mid t(n) = n + k - 1}) = cal(L)(op("CA")_op("rt"))$
- *CA linear time = 2n:* $cal(L)(op("CA")_op("lt")) = cal(L)(op("CA")_(2n))$
- *OCA linear time = 2n:* $cal(L)(op("OCA")_op("lt")) = cal(L)(op("OCA")_(2n))$
- *OCAr linear time = CA rt:* $cal(L)(op("OCA")^r_op("lt")) = cal(L)(op("CA")_op("rt"))$
- *Reversal closure implies lt = rt:* $cal(L)(op("CA")) = cal(L)(op("CA")^r) ==> cal(L)(op("CA")) = cal(L)(op("CA")_op("lt"))$
- *Advice shift-left preserves two-stage*
- *CartTraceFstAdvice classification*

== Open Question

Is every RT-closed advice two-stage, without the causality assumption? We conjecture that no such counterexample exists. However, if a non-two-stage RT-closed advice did exist, its RT-closedness proof would probably require a fundamentally different, non-geometric simulation construction — and it could be promising to investigate whether such a construction can be shown to be generally uncomputable.

== Project Statistics

#table(
  columns: (1fr, auto, auto, auto),
  align: (left, center, center, center),
  stroke: 0.5pt + luma(180),
  inset: 6pt,
  table.header[*Category*][*Files*][*Sorry-free*][*With sorry*],
  [Core proofs & utilities], [7], [7], [0],
  [Main theorems], [5], [4], [*1*],
  [Basic CA constructions], [10], [10], [0],
  [Speedup constructions], [3], [3], [0],
  [Direction conversions], [2], [2], [0],
  [Composition pipeline], [8], [8], [0],
  [Framework & scripts], [4], [4], [0],
  table.hline(),
  [*Total*], [*39*], [*38*], [*1*],
)

Total `sorry` count: *4* in proof files (`exp_middle_two_stage.lean`) + *8* in `results_unproven.lean` (conjectured theorems). The 10 results in `results.lean` are *completely sorry-free*.
