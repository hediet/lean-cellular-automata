# Finite RT Disclosure

## Status and motivation

This note records a proposed generalization of the theorem

$$
\text{weakly RT-closed}+\text{causal}
\Longrightarrow
\text{CART advice}
\Longrightarrow
\text{two-stage advice}.
$$

The original motivation was the search for an explicit uniformly RT-closed
advice that is not two-stage. The complementary approach developed here is to
find progressively weaker conditions than causality under which RT-closure
still forces a two-stage representation.

The main observation is that an advised real-time recognizer can extract a
finite piece of information from an advice word. If the advice is weakly
RT-closed, that finite observation can be computed without advice. Running the
resulting ordinary recognizer temporally then computes the same observation on
every input prefix. This produces a causal CART trace containing one finite
"disclosure" per prefix.

The proposed abstraction is **finite RT disclosure**:

1. use the advice to compute one finite observation of every complete word;
2. apply the same observation to every prefix;
3. reconstruct the full advice from the resulting disclosure word with a
   finite-state right-to-left scan.

The general theorem should be

$$
\boxed{
\text{weakly RT-closed}+\text{finite RT disclosure}
\Longrightarrow
\text{two-stage}.
}
$$

This theorem is not itself a solution of the RT-closed versus two-stage
question. Among weakly RT-closed advice, finite RT disclosure is equivalent to
being two-stage. Its purpose is to isolate the missing information-flow
principle and provide a reusable route for concrete generalizations such as
bounded anticipation and finite-state future dependence.

## Repository context

An `Advice α Γ` is a length-preserving function

$$
A:\alpha^*\longrightarrow\Gamma^*.
$$

An advised recognizer sees

$$
w\otimes A(w).
$$

`Advice.weak_rt_closed` says that every real-time recognizer over
`α × Γ`, when used with `A`, has an equivalent unadvised real-time recognizer
over `α`.

`Advice.rt_closed` is stronger: for every finite alphabet `β` and every map

$$
\pi:\beta\longrightarrow\alpha,
$$

the lifted advice

$$
w\longmapsto A(\operatorname{map}(\pi,w))
$$

is weakly RT-closed.

A two-stage advice has the form

$$
A
=
\operatorname{scanr}_M
\circ
\operatorname{trace}_{\mathrm{rt},C},
$$

where `C` is a real-time CA transducer and `M` is a finite-state transducer
scanning right-to-left.

The repository already proves:

- every two-stage advice is uniformly RT-closed;
- every causal weakly RT-closed advice is a CART advice and hence two-stage;
- middle-marker advice is not two-stage;
- weak RT-closure of the unary middle marker is tied to the open
  real-time/linear-time collapse.

The existing causal proof is in
`CellularAutomatas/proofs/advice_theory/is_two_stage_of_rt_closed_and_causal.lean`.

## Finite advised observations

Let `Δ` be a finite alphabet. A function

$$
q:\alpha^*\longrightarrow\Delta
$$

is an **RT probe using advice `A`** when every fiber

$$
q^{-1}(d)=\{w:q(w)=d\}
$$

is recognized by a real-time CA using `A`.

Equivalently, for every `d : Δ`, there is a recognizer over `α × Γ` satisfying

$$
w\text{ is accepted using }A
\quad\Longleftrightarrow\quad
q(w)=d.
$$

The output of a probe is finite. It may nevertheless be a global property of
the complete annotated word. Examples include:

- the final advice symbol;
- the final `k` advice symbols for fixed `k`;
- a fixed-width advice window;
- any finite RT-computable aggregate of the annotated input;
- a finite table of several such observations.

A finite family of probes can be combined into a single product-valued probe,
so it is enough to work with one finite output alphabet `Δ`.

## The prefix-disclosure advice

Given a probe `q`, define its disclosure word by applying it to every nonempty
prefix:

$$
D_q(w)_i=q(w_0\cdots w_i).
$$

Thus, for

$$
w=a_0a_1\cdots a_{n-1},
$$

the disclosure word is

$$
D_q(w)
=
q(a_0)\,
q(a_0a_1)\,
\cdots\,
q(a_0\cdots a_{n-1}).
$$

This definition evaluates the advice separately on every prefix. In general,

$$
A(a_0\cdots a_i)
$$

need not equal the corresponding prefix of `A(w)`. This distinction is exactly
where non-causal behavior appears.

`D_q` is length-preserving and causal by construction.

## The leakage lemma

### Statement

If `A` is weakly RT-closed and `q` is an RT probe using `A`, then `D_q` is a
CART advice.

### Natural proof

For every `d : Δ`, let `R_d` be an advised RT recognizer for the fiber

$$
\{w:q(w)=d\}.
$$

Weak RT-closure supplies an ordinary RT recognizer `E_d` over `α` with the same
language.

Run all `E_d` in parallel. On every word, exactly one fiber is true, so their
Boolean outputs determine the unique value `q(w)`. Project the product state to
that value. This gives a finite-output ordinary CA `C_q` whose final output on
`w` is `q(w)`.

Now run `C_q` on a longer word `w` and inspect position zero at time `i`. The
past light cone of `(0,i)` contains input positions at most `i`. Consequently
the state is identical to the final state of `C_q` on the prefix

$$
w_0\cdots w_i,
$$

whose real-time acceptance time is exactly `i`. Therefore

$$
\operatorname{trace}_{\mathrm{rt},C_q}(w)_i
=
q(w_0\cdots w_i)
=
D_q(w)_i.
$$

Hence

$$
D_q=\operatorname{trace}_{\mathrm{rt},C_q}.
$$

The empty word causes no problem: both advice words are empty, while the probe
value on the empty word never appears in the disclosure word.

## Finite RT disclosure

An advice `A` has **finite RT disclosure** if there exist:

- a finite alphabet `Δ`;
- an RT probe `q : α* → Δ` using `A`;
- a finite-state transducer `M : Δ → Γ` scanning right-to-left;

such that

$$
A(w)=M.\operatorname{scanr}(D_q(w))
$$

for every word `w`.

Operationally:

1. regard every prefix as a separate complete input;
2. ask the same finite advised question `q` about each prefix;
3. collect the answers into a length-preserving diary;
4. scan the diary from right to left using finite memory;
5. emit the original advice word.

The word "finite" means constant information per prefix, not finitely many
prefixes. A length-`n` input yields `n` disclosure symbols, but each symbol lies
in one fixed finite alphabet.

## Main theorem

### Statement

$$
\boxed{
A.\mathrm{weak\_rt\_closed}
\;\land\;
A.\mathrm{finite\_rt\_disclosure}
\Longrightarrow
A.\mathrm{is\_two\_stage\_advice}.
}
$$

The corresponding theorem with uniform `rt_closed` is an immediate corollary,
because uniform RT-closure implies weak RT-closure by taking the identity
refinement.

### Natural proof

Let `q` and `M` witness finite RT disclosure.

By the leakage lemma, there is a CART `C_q` satisfying

$$
\operatorname{trace}_{\mathrm{rt},C_q}=D_q.
$$

The reconstruction hypothesis gives

$$
A=M.\operatorname{scanr}\circ D_q.
$$

Combining the equations,

$$
\begin{aligned}
A
&=M.\operatorname{scanr}\circ D_q\\
&=M.\operatorname{scanr}
  \circ\operatorname{trace}_{\mathrm{rt},C_q}.
\end{aligned}
$$

This is exactly a two-stage representation.

## Why this is not literally a tautology

Two-stage advice requires an **unadvised** CART trace. Finite disclosure only
requires that the probe be computable by a recognizer that is allowed to use
the advice itself.

For example, every causal advice has finite disclosure: take

$$
q(w)=A(w)_{|w|-1}.
$$

An advised RT machine can obtain this symbol, and causality gives

$$
D_q(w)=A(w).
$$

Nevertheless an arbitrary causal advice need not be two-stage. For instance,
one can define a causal advice whose symbol at position `i` records membership
of the prefix through `i` in a noncomputable language. Such advice cannot be
generated by a finite CA.

Thus finite disclosure alone does not imply two-stage. RT-closure performs the
substantive conversion from advised observations to an unadvised trace.

## Why the abstraction does not yet solve the main question

Every two-stage advice has finite RT disclosure. If

$$
A=M.\operatorname{scanr}
\circ\operatorname{trace}_{\mathrm{rt},C},
$$

choose `q(w)` to be the final output of `C` on `w`. Locality gives

$$
D_q(w)=\operatorname{trace}_{\mathrm{rt},C}(w),
$$

so the same `M` reconstructs `A`.

Consequently, among weakly RT-closed advice,

$$
\boxed{
\text{finite RT disclosure}
\Longleftrightarrow
\text{two-stage}.
}
$$

Therefore the conjecture

$$
\text{uniformly RT-closed}
\Longrightarrow
\text{finite RT disclosure}
$$

is logically equivalent to the desired implication

$$
\text{uniformly RT-closed}
\Longrightarrow
\text{two-stage}.
$$

The abstraction is useful as a factorization and proof interface, not as an
automatic reduction in logical strength.

## Concrete consequence: bounded anticipation

The disclosure mechanism gives a genuine extension of the existing causal
theorem.

### Definition

Advice `A` has anticipation bounded by `k` if, whenever `p` is a prefix of `w`
and

$$
i+k<|p|,
$$

then

$$
A(p)_i=A(w)_i.
$$

Thus an output at position `i` stabilizes once the input is known through
position `i+k`. Causality is the case `k=0`.

This is strictly weaker than causality. For example, the advice that outputs
the next input symbol, using a default symbol at the end, has anticipation one
but is not causal.

### Disclosure probe

Let `q_k(w)` be the final at most `k+1` symbols of `A(w)`, padded to a fixed
finite type when necessary.

This is an advised RT observation. Shift the advice symbols toward the left
boundary and maintain a fixed-size buffer of the most recently arriving
symbols. At time `|w|-1`, the buffer contains the required suffix.

The diary `D_{q_k}` records the last `k+1` advice symbols of every prefix.

### Reconstruction

For an interior position satisfying

$$
i+k<|w|,
$$

the disclosure at time `i+k` contains

$$
A(w_0\cdots w_{i+k})_i.
$$

Bounded anticipation identifies this value with `A(w)_i`.

For the final `k` positions, the final disclosure symbol contains the needed
values directly.

A right-to-left transducer stores at most `k` later disclosure symbols and the
distance from the right boundary capped at `k`. It can therefore select the
correct component at every position.

This proves

$$
\boxed{
\text{weakly RT-closed}+\text{bounded anticipation}
\Longrightarrow
\text{two-stage}.
}
$$

Equivalently, any weakly RT-closed advice that is not two-stage must have
unbounded anticipation.

## Possible stronger concrete properties

The unrestricted existential notion of finite disclosure should not be the
only target. More explicit probe classes may yield useful intermediate
theorems.

### Finite-context disclosure

Fix finitely many continuation words and fixed offsets. At every prefix `p`,
disclose values of the form

$$
A(pz_j)_{\text{a fixed position relative to the }p\mid z_j\text{ cut}}.
$$

Appending each `z_j` costs only a constant amount of space and time. If these
observations can be de-advised and their constant delay removed, their prefix
diaries become CART traces.

This may cover advice with finite-state future dependence.

### Finite future index

Define an equivalence relation on suffixes by

$$
z\equiv_A z'
\quad\Longleftrightarrow\quad
\forall x,\;
\operatorname{take}_{|x|}A(xz)
=
\operatorname{take}_{|x|}A(xz').
$$

Causality means that this relation has one class. If it has finitely many
classes, prepending a letter induces a finite right-to-left transition on the
classes.

Choose one representative `z_s` for each class. At a prefix `p`, one would like
to disclose the finite table

$$
s\longmapsto A(pz_s)_{|p|-1}.
$$

A right-to-left scan computes the class of the actual suffix and selects the
corresponding table entry.

The unresolved technical step is proving cleanly that weak RT-closure of `A`
makes all these fixed-context prefix tables CART-computable with exact timing.
This appears plausible because every representative is fixed and only
constant delay must be removed, but it has not yet been audited or formalized.

### Bounded disclosure bandwidth

The information-flow interpretation is that a constant amount of advice
information is disclosed at each prefix time. Bounded anticipation schedules
the output at position `i` for disclosure near time `i+k`.

For arbitrary advice, the trivial strategy waits for the complete word, but
then all `n` advice symbols may become newly necessary at the final time. One
finite probe cannot emit this unbounded burst.

This suggests the structural question:

$$
\boxed{
\text{Does uniform RT-closure force bounded disclosure bandwidth?}
}
$$

A uniformly RT-closed non-two-stage counterexample would have to resist every
finite RT probe and every finite-state backward reconstruction.

## Proposed Lean interface

The following declarations fit the current repository APIs. They are proposed
statements only; they have not yet been added.

```lean
namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

structure Advice.RtProbe
    (adv : Advice α Γ) (Δ : Type) where
  value : Word α → Δ
  recognizer : Δ → CA_rt (α × Γ)
  spec : ∀ d w,
    w ∈ (recognizer d + adv).L ↔ value w = d

def Advice.RtProbe.disclosure
    {Δ : Type} [Alphabet Δ]
    {adv : Advice α Γ}
    (probe : adv.RtProbe Δ) :
    Advice α Δ :=
  {
    f := fun w =>
      (List.range w.length).map fun i =>
        probe.value (w.take (i + 1))
  }

structure Advice.IsFiniteRtDisclosure
    (adv : Advice α Γ) where
  Δ : Type
  [alphabetΔ : Alphabet Δ]
  probe : adv.RtProbe Δ
  M : FiniteStateTransducer Δ Γ
  spec : ∀ w,
    M.scanr (probe.disclosure w) = adv w

attribute [instance]
  Advice.IsFiniteRtDisclosure.alphabetΔ

abbrev Advice.finite_rt_disclosure
    (adv : Advice α Γ) :=
  adv.IsFiniteRtDisclosure
```

The main constructive result should be:

```lean
def is_two_stage_of_weak_rt_closed_and_finite_rt_disclosure
    (adv : Advice α Γ)
    (hclosed : adv.weak_rt_closed)
    (hdisclosure : adv.finite_rt_disclosure) :
    adv.is_two_stage_advice
```

The uniform convenience corollary should be:

```lean
def is_two_stage_of_rt_closed_and_finite_rt_disclosure
    (adv : Advice α Γ)
    (hclosed : adv.rt_closed)
    (hdisclosure : adv.finite_rt_disclosure) :
    adv.is_two_stage_advice
```

The first theorem is stronger because only weak RT-closure is used.

## Lean implementation strategy

The proof should generalize the existing causal construction.

1. For every `d : Δ`, use `hclosed.map (probe.recognizer d)` to obtain an
   ordinary RT recognizer for the fiber of `probe.value`.
2. Form their finite product with `ProdCA`.
3. Project the Boolean result vector to the unique `d` whose recognizer accepts.
   The existing `first_true_or_default` construction can likely be generalized
   from `Γ` to `Δ`.
4. Regard the resulting finite-output CA as a `CArtTransducer α Δ`.
5. Prove its trace equals `probe.disclosure`.
   The central locality identity is the same one used in the causal proof:
   time `i` on `w` equals real-time completion on `w.take (i+1)`.
6. Build a `TwoStageAdvice` from that CART and `hdisclosure.M`.
7. Use `hdisclosure.spec` to prove equality with `adv`.
8. Obtain the uniform corollary by specializing `rt_closed` to the identity
   refinement.

The focused implementation should live under
`CellularAutomatas/proofs/advice_theory/`, likely in a file named
`finite_rt_disclosure.lean`.

## Validation plan

After implementation:

1. build the focused proof file;
2. add the stable declarations to `CellularAutomatas/results.lean` if the proof
   has no unfinished dependencies;
3. build `CellularAutomatas/results.lean`;
4. run `lake build verify_proofs`;
5. inspect the final theorem's axioms;
6. confirm that only the repository's accepted foundations are used.

## Open questions for the next session

1. Is the proposed `RtProbe` API the best fit, or should a probe directly be a
   finite-output advised CA rather than a family of Boolean fiber recognizers?
2. Can the existing `PrefixStableProof.cart_adv` construction be generalized
   with minimal duplication?
3. Is the exact locality lemma already available for arbitrary CA projections,
   or should it be factored out of the causal proof?
4. Can bounded anticipation be formalized immediately as the first non-causal
   corollary?
5. Can fixed-context disclosure be proved using existing fixed-suffix and
   additive-speedup constructions?
6. Does uniform RT-closure provide a canonical probe through decorated
   alphabets, or is that conjecture equivalent in difficulty to the original
   RT-closed versus two-stage problem?

No claim is made here that uniform RT-closure implies finite RT disclosure.
That remains the central unresolved structural question.
