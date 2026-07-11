# Cellular Automata in Lean 4

How much global computation can emerge from a finite-state, radius-one local
rule in exactly $n-1$ parallel steps? What changes if information may flow in
only one direction, if the output is read at the other end of the word, or if
the input comes with a structured annotation?

This repository formalizes those questions for one-dimensional cellular
automata in Lean 4. A CA is used both as a **language recognizer** and as a
**real-time transducer** whose temporal trace is itself a word function. The
development builds the required machines explicitly and proves their
space-time behavior cell by cell.

Two technical results anchor the project. The first is a machine-checked
reconstruction of the **Ibarra-Jiang theorem**, relating the real-time versus
linear-time problem to closure under reversal. The second is **closure of
real-time CA traces under composition**, the main construction behind the
advice theory. The surrounding simulation, border, speedup, and advice library
exists largely to make these two concise statements work at exact time bounds.

The curated theorem API is
[`CellularAutomatas/results.lean`](CellularAutomatas/results.lean). A longer
mathematical tour and reading guide is in [`docs/summary.md`](docs/summary.md).

## The Setting

A finite word occupies positions $0,\ldots,n-1$ of a bi-infinite
configuration, surrounded by a border symbol. Every cell updates from its
left, current, and right states. Acceptance is specified by **when** and
**where** a Boolean output is read.

At the core is a finite state type `Q`, a radius-one local rule `δ`, and maps
between input symbols, states, and observable outputs. `δ left center right`
returns the next center state. A `Config Q` is a function `ℤ → Q`, while a
`Trace Q` is a function `ℕ → Q`; all cells update simultaneously:

```lean
structure CellAutomaton (α β : Type) where
  Q : Type
  [alphabetQ : Alphabet Q]
  δ : Q → Q → Q → Q
  embed : α → Q
  project : Q → β

def CellAutomaton.next (C : CellAutomaton α β) (c : Config C.Q) : Config C.Q :=
  fun p => C.δ (c (p - 1)) (c p) (c (p + 1))

def CellAutomaton.nextt (C : CellAutomaton α β) (c : Config C.Q) : Trace (Config C.Q) :=
  fun t => Nat.iterate C.next t c

def CellAutomaton.comp (C : CellAutomaton α β) (c : Config C.Q) : Trace (Config β) :=
  fun t p => C.project (C.nextt c t p)
```

Thus `C.comp c t p` is the observable output at position `p` after `t` local
updates. Words are embedded into a bi-infinite bordered configuration before
evaluation. Recognition adds only an observation schedule and a Boolean
output:

```lean
structure AcceptanceSchema where
  t : ℕ → ℕ
  p : ℕ → ℤ

abbrev LCellAutomaton (α : Type) := CellAutomaton (Option α) Bool

structure tCellAutomaton (𝒮 : AcceptanceSchema) (α : Type) extends LCellAutomaton α

variable {𝒮 : AcceptanceSchema} {α : Type}

def tCellAutomaton.accepts (C : tCellAutomaton 𝒮 α) (w : Word α) : Bool :=
  C.comp w (𝒮.t w.length) (𝒮.p w.length)

def tCellAutomaton.L (C : tCellAutomaton 𝒮 α) : Language α :=
  { w | C.accepts w }
```

Here `Option α` supplies the border symbol, while `𝒮.t` and `𝒮.p` choose when
and where the Boolean result is read.

The main language classes are

$$
\begin{aligned}
\mathcal L(CA_{\mathrm{rt}}(\alpha))
  &:\quad \text{unrestricted CAs read at position }0\text{ after }n-1\text{ steps}, \\
\mathcal L(CA_{\mathrm{lt}}(\alpha))
  &:\quad \text{unrestricted CAs read after }c(n-1)\text{ steps for some constant }c, \\
\mathcal L(OCA_{\mathrm{rt}}(\alpha)),\;\mathcal L(OCA_{\mathrm{lt}}(\alpha))
  &:\quad \text{the corresponding one-way classes, where }\delta\text{ ignores its left input}.
\end{aligned}
$$

The suffixes `rt`, `lt`, and `2n` denote real time, linear time, and
$2(n-1)$ time. `CAr` denotes a CA whose output is read at the right end,
position $n-1$, instead of at position $0$.

The formalization does not assume that the border is passive. Instead, it
proves constructions that impose quiescent or absorbing borders while
preserving the relevant computation. This makes boundary behavior an explicit
theorem rather than a hidden premise.

## Key Results

The simulation, speedup, separation, and reversal results below belong to
established cellular-automata theory; several are folklore in the precise
coordinate-level form used here. The contribution of this development is a
uniform, machine-checked treatment in which timing, borders, and observation
positions are all explicit. The geometric results below lead into the two
centerpieces: the Ibarra-Jiang equivalence and real-time trace composition.

### One-way versus unrestricted CAs

One-way and unrestricted CAs simulate one another along diagonals of the
space-time diagram, with a factor-two change in coordinates
(`result_left_indep_to_regular`, `result_regular_to_left_indep`). These
simulations turn into exact language-class identities when paired with the
right observation position:

$$
\mathcal L(OCA_{2n}) = \mathcal L(CAr_{rt}),
$$

and an OCA run for $2(n-1)$ steps and observed at $-(n-1)$ recognizes exactly
$\mathcal L(CA_{rt})$ (`oca_2n_left_neg_np1_eq_ca_rt`).

Nevertheless, one-way real time is strictly weaker:

$$
\mathcal L(OCA_{rt}) \subsetneq \mathcal L(CA_{rt}).
$$

Every unary real-time OCA language is regular, while an unrestricted CA can
recognize the powers-of-two length language in real time. The resulting
separation is `oca_rt_proper_subset_ca_rt`.

### Centerpiece I: Ibarra-Jiang

Both unrestricted and one-way linear time collapse to time $2(n-1)$:

$$
\mathcal L(CA_{lt}) = \mathcal L(CA_{2n}), \qquad
\mathcal L(OCA_{lt}) = \mathcal L(OCA_{2n}).
$$

The OCA construction compresses a diagonal window into each cell; the general
CA construction combines spatial compression with timing machinery. Spatial
flip then connects left-reading, right-reading, and language reversal.

These speedup and reversal identities culminate in a formalization of
[Ibarra and Jiang's 1988 theorem](https://doi.org/10.1016/0304-3975(88)90040-0).
Uniformly over all finite alphabets,

$$
\mathcal L(CA_{rt}) = \mathcal L(CA_{lt})
\quad\Longleftrightarrow\quad
\mathcal L(CA_{rt}) = \mathcal L^R(CA_{rt}).
$$

This is `result_rt_eq_lt_iff_rt_eq_rt_rev`. The quantification over all
alphabets matters: the hard direction pads words over `Option α`, applies
reversal closure twice, and then removes the padding.

### Centerpiece II: real-time traces compose

For a CA $C$, `C.trace_rt` records the outputs seen at position $0$ during the
first $n$ steps. The second centerpiece constructs a real-time CA satisfying

$$
\mathrm{trace}_{\mathrm{rt},C} =
\mathrm{trace}_{\mathrm{rt},C_2} \circ
\mathrm{trace}_{\mathrm{rt},C_1}.
$$

This is not ordinary sequential execution: $C_2$ cannot wait for the complete
output of $C_1$. The proof rearranges the first trace onto space-time
diagonals, simulates $C_2$ from those events, decompresses the result, and
removes a constant delay. The exported theorem is
`result_rt_transducers_closed_under_composition`.

This composition theorem drives two-stage advice and its closure properties.
In turn, two-stage advice eliminates the final spatial marker in the hard
direction of the Ibarra-Jiang formalization, tying the two centerpieces
together.

## Advice Theory

Advice itself is a standard idea in complexity theory. The CA-specific theory
developed here appears, to the best of our knowledge, to be novel: in
particular the weak and uniform notions of RT-closure, two-stage advice, their
composition theory, and the connection between advice elimination and the
real-time versus linear-time problem. This is a cautious provenance statement,
not a definitive claim of priority over all existing literature.

An `Advice α Γ` is a length-preserving annotation $`f : \alpha^* \to \Gamma^*`$.
A recognizer using $`f`$ receives the pointwise zip of $`w`$ and $`f(w)`$.
`weak_rt_closed` fixes the input alphabet $`\alpha`$: every real-time recognizer
using $`f`$ can be replaced by an equivalent unadvised recognizer over $`\alpha`$.
The uniform `rt_closed` notion also requires this after every finite refinement
or relabeling $`\pi : \beta \to \alpha`$. On a $`\beta`$-word $`w`$, the lifted advice
is $`f(\pi_*(w))`$, where $`\pi_*`$ applies $`\pi`$ pointwise. For example,
$`\beta = \alpha \times S`$ may add a finite auxiliary track and $`\pi`$ may forget
it; uniform closure says that the advice remains eliminable on these decorated
inputs.

The key representation is **two-stage advice**:

$$
f = \mathrm{scanr}_M \circ \mathrm{trace}_{\mathrm{rt},C},
$$

where $`C`$ is a real-time CA transducer and $`M`$ is a finite-state transducer
scanning right-to-left. Concretely, let
$`u = \mathrm{trace}_{\mathrm{rt},C}(w) = u_0\ldots u_{n-1}`$. The word
$`\mathrm{scanr}_M(u)`$ also has length $`n`$. Starting with the initial
state at the right edge, it computes

$$
s_n = M.q_0, \qquad
s_i = M.\delta(s_{i+1}, u_i), \qquad
(\mathrm{scanr}_M(u))_i = M.f(s_i).
$$

Thus the output at position $`i`$ may depend on the entire suffix
$`u_i\ldots u_{n-1}`$, but only through one of finitely many states. Here
`scanr` is an extensional right fold over the intermediate word, not a claim
that a CA first materializes $`u`$ and then spends $`n`$ additional steps scanning
it. The RT-closure theorem is precisely what allows a recognizer using this
two-stage advice to absorb the finite-state suffix pass into a real-time CA.

The formalized theory proves:

- two-stage advice is uniformly RT-closed;
- two-stage advice and uniformly RT-closed advice are closed under
  composition;
- prefix-membership advice for any real-time language is two-stage;
- causal weakly RT-closed advice is computed by a single CA real-time trace;
- the advice marking the middle position is **not** two-stage; and
- the related exponential-middle marker **is** two-stage.

Advice also gives a structural reformulation of the real-time versus
linear-time problem. `Advice.compress2` annotates each position with two
consecutive input symbols. The project proves

$$
\mathcal L(CA_{rt}) = \mathcal L(CA_{lt})
\quad\Longleftrightarrow\quad
\mathrm{compress2}\text{ is weakly RT-closed}.
$$

Thus the time-collapse question is equivalent to asking whether a specific
spatial compression can always be eliminated from real-time recognition. Over
a unary alphabet, the same question is equivalent to weak RT-closure of the
middle-marker advice.

## Why This Formalization Is Hard

The local rule of a CA is tiny; proofs about composed space-time constructions
are not. A paper proof can draw a signal and say “shift it,” “fold the tape,” or
“pack several cells together.” Lean requires an explicit finite state type,
transition rule, decoder, and invariant showing exactly which original cell is
represented at every time and position.

The main sources of difficulty are:

- **Exact geometry:** time lives in $\mathbb N$, positions in $\mathbb Z$, and
  packed cells in finite index types. Every diagonal simulation must align
  shifts, $n-1$ conventions, reversals, and compression factors exactly.
- **Borders and small inputs:** the model does not assume a passive border, so
  constructions must normalize boundary behavior and prove that stray signals
  cannot enter the relevant light cone. Empty and short words need separate
  repairs rather than asymptotic hand-waving.
- **Parallel composition:** in real time, one CA cannot finish before the next
  begins. Composing traces requires a diagonal rearrangement, simulation from
  staggered events, decompression, and removal of a constant delay.
- **The hard reversal direction:** the Ibarra-Jiang reconstruction pads over
  `Option α`, applies reversal closure across alphabets, and strips the padding
  through a multi-stage pipeline whose final spatial marker is eliminated
  using two-stage advice.

The value of the development is therefore not just the final class equalities.
It is a reusable, checked construction library for locality, borders, speedup,
folding, traces, finite-state postprocessing, and advice elimination. The
stable exports are also checked by an explicit axiom policy. The
[proof walkthrough](CellularAutomatas/proofs/rt_eq_2n_iff_rt_eq_rt_rev/lx-rt-implies-rt-proof.md)
follows the hard padding-elimination pipeline stage by stage.

## Build and Verification

The exact Lean version is pinned in [`lean-toolchain`](lean-toolchain).

```bash
# Curated stable results
lake build ./CellularAutomatas/results.lean

# Axiom policy for the configured stable modules
lake build verify_proofs

# Entire library, including WIP and open-question declarations
lake build
```

The verifier checks the configured modules against `Quot.sound`,
`Classical.choice`, and `propext`. The stable results module is free of `sorry`;
explicitly unfinished material remains separated in `open_questions.lean`,
`verification_candidates.lean`, `proofs/wip/`, and
`proofs/advice_theory/rt_lt_advice.lean`.

## Repository Map

| Path | Purpose |
|---|---|
| [`CellularAutomatas/defs.lean`](CellularAutomatas/defs.lean) | Core automata, language classes, advice, and reversal definitions |
| [`CellularAutomatas/results.lean`](CellularAutomatas/results.lean) | Curated stable theorem API |
| [`CellularAutomatas/proofs/constructions/`](CellularAutomatas/proofs/constructions/) | Automata constructions, simulation, borders, and speedups |
| [`CellularAutomatas/proofs/language/`](CellularAutomatas/proofs/language/) | Language-class inclusions and equivalences |
| [`CellularAutomatas/proofs/advice_theory/`](CellularAutomatas/proofs/advice_theory/) | Advice computability and closure theory |
| [`docs/summary.md`](docs/summary.md) | Longer mathematical and architectural guide |
| [`docs/bachelor-thesis/`](docs/bachelor-thesis/) | Thesis sources and bibliography |

The project depends on [Mathlib](https://github.com/leanprover-community/mathlib4).
