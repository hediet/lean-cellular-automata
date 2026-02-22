# Cellular Automata in Lean 4

A formalization of one-dimensional cellular automata theory in Lean 4 + Mathlib4, covering real-time language recognition, one-way (left-independent) CAs, and a structural theory of *advice* for cellular automata.

## What's Formalized

The project contains **39 Lean source files** with **38 completely sorry-free**. All 10 main results in `results.lean` are fully verified (only axioms used: `Quot.sound`, `Classical.choice`, `propext`).

### Part I — Classical Constructions (existing literature, sorry-free)

These are well-known results from the cellular automata literature (see e.g. Kutrib, Malcher, et al.). The proofs were sometimes adapted for formal verification.

| # | Result | Lean theorem |
|---|--------|-------------|
| 1 | **Left-independent ↔ regular CA simulation** — OCA and CA are equivalent up to factor 2 in time | `result_left_indep_to_regular`, `result_regular_to_left_indep` |
| 2 | **k-step left-independent speedup** — compress k diagonal cells into one tuple | `result_left_indep_speedup` |
| 3 | **General k-step RT speedup** — constant additive speedup via dead/quiescent border chaining | `SpeedupKSteps.spec` |
| 4 | **Quiescent border** — left-independent CAs can be given a quiescent border without changing computation | `result_quiescent_border_left_indep` |
| 5 | **Dead border** — any CA can be given a dead (absorbing) border, preserving the trace for linear time | `result_dead_border` |
| 6 | **Exponential word length is RT-recognizable** — {w : \|w\| = 2^n} ∈ L(CA_rt) via signal bouncing | `exp_word_length_rt` |

### Part II — Advice Theory (likely novel, sorry-free)

These results develop a structural theory of *advice* for cellular automata. The notion of two-stage advice, the composition pipeline, the closure results, and the classification theorems appear to be **new**. They establish closure properties of RT transducers and two-stage advice, and classify causal RT-closed advice.

| # | Result | Lean theorem |
|---|--------|-------------|
| 7 | **RT transducers closed under composition** — multi-stage pipeline: AddBorder → CompressToDiag → SimFromΛ → DecompressTriple → SpeedupKSteps | `result_rt_transducers_closed_under_composition` |
| 8 | **Two-stage advice is RT-closed** — L(CA_rt(Σ×Γ)/f) = L(CA_rt(Σ)) for two-stage f | `result_two_stage_is_rt_closed` |
| 9 | **Prefix-membership advice is two-stage** — for L ∈ L(CA_rt), the prefix-membership advice f_L is a two-stage advice | `result_advice_prefix_mem_is_two_stage_advice` |
| 10 | **RT-closed ∧ causal ⟹ CArt advice** — causal RT-closed advice is computable by a single RT transducer | `result_is_cart_advice_of_rt_closed_and_causal` |
| 11 | **Two-stage advice closed under composition** — via backwards FSM construction | `result_two_stage_closed_under_composition` |
| 12 | **Middle advice is NOT two-stage** — bottleneck argument on FST state count | `result_middle_not_two_stage_advice` |

### Incomplete / Conjectured

- **Exponential-middle advice is two-stage** (4 `sorry` in combinatorial counting lemmas; construction is complete)
- Several classical time-hierarchy results stated in `results_unproven.lean` (8 `sorry`)
- **Open question:** Is every RT-closed advice two-stage (without causal assumption)?

## Project Structure

```
CellularAutomatas/
  defs.lean                  Core definitions (CA, word embedding, trace, advice, FST, two-stage)
  internal_defs.lean         Internal types (BetaUnionSq, triple_at)
  results.lean               10 main theorems — all sorry-free
  results_unproven.lean      Conjectured results (sorry)
  open_questions.lean        Open problems
  proofs/
    basic.lean               Core lemmas (locality, causality of trace_rt)
    border.lean              Border behavior lemmas
    causal.lean              Causality composition and properties
    ca_rt_utils.lean         Real-time CA utilities and advice helpers
    finite_state_transducers.lean   FST library (scanr, composition, product)
    word_ops.lean            Word operations and zip properties
    int_lemmas.lean          Integer arithmetic lemmas
    middle_not_two_stage.lean       Proof: middle advice is not two-stage
    advice_prefix_mem_rt_closed.lean  Proof: prefix-membership → two-stage
    is_two_stage_of_rt_closed_and_causal.lean  Proof: RT-closed ∧ causal → CArt
    two_stage_is_rt_closed.lean     Proof: two-stage → RT-closed
    exp_middle_two_stage.lean       Proof (incomplete): exp-middle is two-stage
    constructions/
      basic_ca_id.lean       Identity CA
      basic_ca_left_edge_marker.lean  Left edge detection CA
      basic_compose_k_steps.lean     Sequential CA composition
      basic_exp_word.lean    RT recognition of {2^n} via signal bouncing
      basic_flip.lean        Mirror (flip) a CA
      basic_mark_border.lean Border detection CA
      basic_product_ca.lean  Product/zip of CAs
      trace_id.lean          Identity trace CA
      cart_fix_empty_word.lean  Fix empty-word edge case
      left_indep_to_regular.lean    Left-independent → regular (×2 time)
      left_indep_from_regular.lean  Regular → left-independent (×2 time)
      speedup_compressed.lean       k-step spatial compression
      speedup_k_step.lean          k-step additive speedup via iterated SpBD
      speedup_left_independent.lean Diagonal compression for left-indep CAs
      border_quiescent.lean        Quiescent border for left-indep CAs
      border_dead.lean             Dead border via zigzag folding
      composition/                 RT transducer composition pipeline (8 files)
    framework/
      particle.lean          Declarative particle framework for CA construction
  scripts/
    verify_proofs.lean       Axiom verification script
    VerifyConfig.lean        Verification configuration
    dependencies.lean        Dependency graph generator
docs/
  summary.md                 Detailed research summary with math
visualization/               Interactive space-time diagram viewer (TypeScript/React)
```

## Building

Requires [Lean 4](https://leanprover.github.io/) and [Lake](https://github.com/leanprover/lean4/tree/master/src/lake).

```bash
lake build
```

The build compiles all 39 Lean files (~3081 jobs including Mathlib dependencies). The axiom verifier runs automatically and confirms only `Quot.sound`, `Classical.choice`, and `propext` are used in `results.lean`.

## Dependencies

- [Lean 4](https://leanprover.github.io/) (see `lean-toolchain` for exact version)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)

## Documentation

See [docs/summary.md](docs/summary.md) for the full research summary with mathematical notation and detailed descriptions of all results.