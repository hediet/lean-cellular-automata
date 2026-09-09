# Uniform local simulation: expected membership proofs

## Status and purpose

The opaque-state program model and its composition theorems are formalized in
[`uniform_local`](../CellularAutomatas/proofs/uniform_local.lean). Membership of
general CART, RTL finite-state-transducer, packet-readout, and two-stage advice
in this model is **not yet formalized**.

This note records a high-level proof plan. The existing simulation constructions
make these membership results look very likely, but an implementation audit and
representation proofs are still required. Formalization is deferred until a
more important theorem needs these results.

Composition notation is mathematical: $B \circ A$ means first $A$, then $B$.
In Lean this is `A.compose B`.

## 1. The intended statements

A local program is fixed before the target CA $C$ is supplied. Its primitive
state representation is

$$
  \mathrm{Control} \times Q_C^r,
$$

with finite target-independent control and a fixed finite number of opaque
target-state registers. The program may copy states and use $C$'s embedding,
transition, and projection. It may branch on ground values and projected
outputs, but cannot inspect or enumerate $Q_C$.

The distinction between implementation and correctness is essential:

- `CellAutomaton.IsUniformlyLocal f` asserts that a program compiles to $f$.
- `CellAutomaton.PreservesRtEndpointOn A D f` asserts, for every target $C$ and
  nonempty $w \in D$,

  $$
    \operatorname{trace}_{f(C)}(w,|w|-1)
      = \operatorname{trace}_C(A(w),|w|-1).
  $$

- `Advice.IsUniformlyLocallySimulatable A` requires such a program for each
  finite alphabet lift $\pi:\Sigma\to\alpha$ and finite output alphabet,
  simulating the input-retaining advice

  $$
    w \longmapsto w \mathbin{\mathrm{zip}} A(\operatorname{map}\pi(w)).
  $$

The program is chosen before the universally quantified target CA. There is no
empty-word endpoint obligation, full-diagram decoding requirement, or external
length/timing oracle.

The desired results are:

1. RTL FST advice is uniformly locally simulatable.
2. A locally clocked packet readout has a uniform endpoint simulator on its
   promised domain, including its input-retaining alphabet lifts.
3. Global packet-readout advice, hence CART advice, is uniformly locally
   simulatable.
4. Two-stage advice is uniformly locally simulatable.
5. As a subsequent corollary, finite-stage advice is uniformly locally
   simulatable, using the domain-relative packet result at intermediate images.

## 2. First test case: RTL finite-state transducers

Fix an RTL FST $M$ and let $C$ be the arbitrary target. The existing
[`backwards_fsm` construction](../CellularAutomatas/proofs/advice_theory/compose_trace_rt/compose_two_stage.lean)
stores a transported input symbol and a table

$$
  F:Q_M\to Q_C.
$$

Each table entry speculates about the FST state at the right boundary of the
target's current dependency interval. The transition advances these guesses
using $M$ and applies $C$'s transition to the corresponding three target-state
entries.

This storage fits the program model: the transported symbol is finite control,
and the table is $|Q_M|$ opaque registers. The FST is fixed independently of
$C$, so its state space and transition may be used in ground control logic.
Selecting a register with a control-dependent index can be expanded into a
finite tree of branches; it does not require target-state inspection.

At time $|w|-1$ at the origin, the transported symbol is the final input
symbol. The actual suffix state needed by the invariant can therefore be
computed from this symbol and $M$'s terminal state. Select that table entry and
apply $C$'s projection. This avoids computing the entire suffix-state sequence.

The existing construction exposes its opaque table as an intermediate output.
Do not copy that interface into the new program: keep the table in registers
and fuse selection into the final projection. Reuse its state invariant to
prove endpoint correctness.

For the strong advice statement, replace $M$ by the fixed lifted,
input-retaining FST. Its output pairs each original symbol with its advice
symbol. The same argument then applies.

## 3. Main reusable bridge: the packet consumer

For a fixed normalized packet producer $P$ of advice $A$ on a domain $D$,
[`PacketProducer.trace_final`](../CellularAutomatas/proofs/advice_theory/local_horizon/producer.lean)
already establishes

$$
  \operatorname{trace}_{P.\mathrm{consumer}(C)}(w,|w|-1)
    = \operatorname{trace}_C(A(w),|w|-1)
$$

for every target $C$ and every nonempty valid input.

The missing result is an implementation bridge: construct a fixed local
program whose compiled CA has the same relevant behavior as this consumer.
An all-input, all-time output equivalence would be convenient; an invariant
implying the required valid-input endpoint equality would also suffice.
Literal equality of CA structures is not necessary.

### Representation idea

The producer is fixed before $C$ and can therefore be included in finite
control, together with its clock, packet buffers, readiness flags, and bounded
phase counters.

The target-dependent part of the
[`consumer construction`](../CellularAutomatas/proofs/advice_theory/marked_prefix/lt/consumer.lean)
uses normalization, packed speedup, bounded histories, asynchronous advancement,
and [final readout](../CellularAutomatas/proofs/advice_theory/marked_prefix/lt/readout.lean).
Represent its stored target states by a fixed finite register array. Store
target outputs in finite control, since the output alphabet is fixed before
the target.

Translate operations as follows:

- target initialization becomes an `embed` expression;
- copying or selecting a stored target state becomes register access and
  finite branching;
- a bounded accelerated update becomes a finite expression containing nested
  target transitions;
- readiness, tags, and packet processing remain ground finite-control logic;
- observable target output is obtained only through `project`.

Prove initialization, transition, and projection compatibility with the
existing consumer. Induction over time then transfers its endpoint theorem.
The difficult deadline and asynchronous-progress arguments should not need to
be reproved.

### Details that must be checked, not assumed

- The register count, control type, and expression syntax must be independent
  of the target's internal state space.
- Optional and nested state records require explicit tags and register
  representations. Invalid registers need legal initial values, for example
  $C.\mathrm{embed}(\mathrm{none})$, not arbitrary access to `default : C.Q`.
- Any use of target-state equality, enumeration, or arbitrary state-dependent
  functions in the existing implementation would need removal or a different
  implementation with a proved invariant.
- Dynamic selection from finite tables must be expressed by finite branching.
- Wrappers that change their output alphabet are not automatically covered by
  the current same-output `Program.compose` constructor. Their relevant state
  and output operations must be encoded together or handled by additional
  proved representation lemmas.
- Re-encoding must preserve exact timing, especially initialization, source
  event consumption, serialization, and the short nonempty inputs.
- Intermediate output buffering is allowed; exposing opaque target states as
  ground values is not.

These are proof-engineering obligations, not completed lemmas. No general
flattening theorem for arbitrary composed programs is being assumed.

## 4. Promises, input retention, and CART

For a machine whose packet contract holds only on $D$, the correctness result
must remain restricted to $D$. The program still runs on every input; its
correctness proof does not give guarantees outside the promise.

Use the existing
[input-retaining normalization](../CellularAutomatas/proofs/advice_theory/local_horizon/normalize.lean)
to pair raw input packets with advice packets and handle exterior padding.
Use the existing
[alphabet-lifting construction](../CellularAutomatas/proofs/advice_theory/local_horizon/closure.lean)
to run the fixed producer on relabeled inputs. Both are target-independent,
so their finite state can be included in the program's control.

Applying the consumer bridge to these producers gives the strong lifted,
input-retaining endpoint statement. For a global contract, this proves
advice-level ULS.

Every CART already has a
[global packet presentation](../CellularAutomatas/proofs/advice_theory/local_horizon/cart.lean).
CART membership should therefore be a short specialization after the generic
packet result. A direct encoding of CART composition is another route, but
would establish less reusable infrastructure.

This discussion concerns locally clocked packet readouts, not the separate
proposal of externally sampling a CA at a length-dependent time.

## 5. Composition consequences

For two-stage advice $A=M\circ C$, combine CART membership and FST membership
with the already formalized
[advice-level ULS composition theorem](../CellularAutomatas/proofs/uniform_local/composition.lean).
No interchange law or packet-layer collapse is needed.

Compiler order is contravariant: if $f$ eliminates $A$ and $g$ eliminates $B$,
then $f\circ g$ eliminates $B\circ A$.

For the [finite-stage hierarchy](../CellularAutomatas/proofs/advice_theory/three_stage.lean),
induct over a pipeline presentation. Each packet stage is correct on the image
of the entire preceding pipeline. Use the promised-domain endpoint theorem,
preserving the necessary input tracks through lifts, and the existing
[domain-compatible simulation composition theorem](../CellularAutomatas/proofs/uniform_local/correctness.lean).
The image promise is discharged by the preceding pipeline; it is not promoted
to a global packet contract.

If completed, this would show

$$
  \mathrm{TwoStage}
    \subseteq \mathrm{ThreeStage}
    \subseteq \mathrm{FiniteStage}
    \subseteq \mathrm{ULS}.
$$

It would not show that three-stage advice is composition-closed, that finite
packet depth collapses, or that every ULS advice has a finite-stage
presentation.

## 6. Suggested implementation order

1. Add finite register-selection syntax helpers and their evaluation lemmas.
2. Encode the FST endpoint simulator as a small test of the model.
3. Establish reusable state-representation lemmas for the packet consumer's
   finite control and opaque registers.
4. Encode that consumer and transfer its existing exact endpoint theorem.
5. Add promised-domain, input-retaining alphabet lifts.
6. Derive global packet, CART, two-stage, and finite-stage membership.

The expectation is high confidence in the underlying constructions, with the
largest remaining task being the packet consumer's representation proof.
Until these steps are checked in Lean, the membership claims remain proof
plans rather than exported theorems.
