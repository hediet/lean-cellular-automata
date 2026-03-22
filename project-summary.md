# Project Summary: Formalized Cellular Automata Theory in Lean 4

## 1. Overview

This project is a machine-checked formalization of one-dimensional cellular automata (CA) theory in **Lean 4** with **Mathlib4**. It covers:

- Classical constructions for real-time language recognition (border normalization, speedup, left-independent ↔ regular equivalence).
- A novel structural theory of **advice** for cellular automata — defining two-stage advice, proving closure properties, and establishing a classification of causal RT-closed advice.
- A complete, sorry-free proof that **real-time CA transducers are closed under composition**, via a multi-stage pipeline of 8 interacting constructions.

### Scale

| Metric | Value |
|---|---|
| Lean source files | 46 |
| Lines of Lean code | 9,745 |
| Theorems and lemmas | 470 |
| Main results (in `results.lean`) | 10 (all sorry-free) |
| Files with sorry | 3 (`exp_middle_two_stage.lean`: 4, `results_unproven.lean`: 10, `open_questions.lean`: 2) |
| Sorry-free proof files | 38 of 39 |
| Axioms used | `Quot.sound`, `Classical.choice`, `propext` (verified by automated checker) |
| Build jobs (incl. Mathlib) | 3,081 |

---

## 2. Definitions and Formalization Choices

### 2.1 Cellular Automaton (`CellAutomaton`)

Defined in `CellularAutomatas/defs.lean` (489 lines). A CA is a structure:

```
structure CellAutomaton (α β : Type) where
  Q : Type                    -- state set (finite, decidable eq, inhabited)
  δ : Q → Q → Q → Q          -- local transition (left, center, right)
  embed : α → Q               -- input embedding
  project : Q → β             -- output projection
```

The split into input type `α` and output type `β` with explicit `embed`/`project` maps makes CAs naturally act as **transducers** (not just recognizers). This design is essential for the composition results.

A **configuration** is `Config α := ℤ → α` (bi-infinite tape indexed by integers). One step: `next(c)(p) = δ(c(p-1), c(p), c(p+1))`. Time evolution: `nextt c t = next^t(c)`.

The **computation** at position `i` and time `t` projects the state: `comp(c, t, i) = project(nextt(c, t)(i))`.

### 2.2 Word Embedding (0-indexed)

Words are embedded with **0-based indexing**: a word `w` of length `n` occupies positions `0, 1, ..., n-1`, with all other positions mapped to `none` (the border symbol `#`):

```
word_to_config w p = if 0 ≤ p < w.length then some w[p] else none
```

For language recognition, the input type is `α? := Option α`, so `embed(none)` gives the border state. Crucially, **no a priori constraints** are placed on the border state — it need not be quiescent or dead. Results 4 and 5 show this generalization is conservative.

### 2.3 Trace and Real-Time Trace

- **Trace:** `trace(C, c)(t) = comp(C, c, t, 0)` — temporal output at position 0.
- **Real-time trace:** `trace_rt(C, w) = [trace(C, ⟬w⟭)(0), ..., trace(C, ⟬w⟭)(n-1)]` — reads position 0 at each time step up to `n-1`. This is the central notion for composing transducers: `trace_rt : Word α → Word β` is length-preserving and **causal** (proved in `basic.lean`).

### 2.4 CA Classes

Timed CAs (`tCellAutomaton`) add timing/position functions `t(n)` and `p(n)`. The classes defined:

| Class | Constraint | Time |
|---|---|---|
| `CA α` | read position 0 | arbitrary |
| `CA_rt α` | read position 0 | `t(n) = n - 1` |
| `CA_2n α` | read position 0 | `t(n) = 2n` |
| `CA_lt α` | read position 0 | `t(n) = c·n` (some `c`) |
| `CAr α` | read position `n` | arbitrary |
| `OCA α` | left-independent + position 0 | arbitrary |
| `OCA_rt α` | left-independent + position 0 | `t(n) = n - 1` |

### 2.5 Advice

An **advice** is a length-preserving map `f : Word α → Word Γ`:

```
structure Advice (α Γ : Type) where
  f : Word α → Word Γ
  len : ∀ w, (f w).length = w.length
```

Properties:
- **Causal (prefix-stable):** `f(w.take i) = (f w).take i`
- **RT-closed:** `ℒ(CA_rt(α × Γ) / f) = ℒ(CA_rt α)` — the advice doesn't increase recognition power.

### 2.6 Finite-State Transducer

```
structure FiniteStateTransducer (α β : Type) where
  Q : Type
  δ : Q → α → Q                -- transition
  q0 : Q                       -- initial state
  f : Q → β                    -- output
```

The FST processes words **right-to-left** via `scanr` (fold-right). This is the natural direction for two-stage advice: the CA sweeps left-to-right in real-time, then the FST post-processes right-to-left.

### 2.7 Two-Stage Advice

```
structure TwoStageAdvice (α Γ : Type) where
  β : Type                           -- intermediate alphabet
  C : CArtTransducer α β             -- CA real-time transducer (left-to-right)
  M : FiniteStateTransducer β Γ      -- FST (right-to-left post-processing)
```

The advice is `M.scanr ∘ C.trace_rt`. This captures: the CA computes a global annotation in real-time, and the FST applies bounded right-to-left look-ahead.

---

## 3. Verified Results — Part I: Base Constructions

All results in this section are **completely sorry-free**.

### Result 1: Left-Independent ↔ Regular CA Simulation

**Files:** `proofs/constructions/left_indep_to_regular.lean` (80 lines), `proofs/constructions/left_indep_from_regular.lean` (176 lines)

**Statement:** Given a left-independent CA `C`, construct `C'` with `Δ^t_{C'}(c, i) = Δ^{2t}_C(c, i-t)`. Conversely, given any CA `C`, construct a left-independent `C'` with `Δ^{2t}_{C'}(c, i) = Δ^t_C(c, i+t)`.

**Construction details:**
- **Left-indep → regular** (`LeftIndepToRegular`): The new state `Q' = Q × Q` stores two consecutive diagonal values. Since the original is left-independent, the left neighbor can be recovered from stored state. Proof by induction on `t`, using `nextt_shift` and `nextt_add`.
- **Regular → left-indep** (`RegularToLeftIndep`): State `Q' = single Q | pair Q Q | dead`. Even time steps produce `single(comp_C(c, t, i+t))`, odd steps produce `pair(...)`. Left-independence follows because the new δ ignores the left argument. Proof by mutual induction on even/odd time steps.

**Lean theorems:**
```
theorem result_left_indep_to_regular (C h_left_indep c t i) :
    e.C.comp c t i = C.comp c (2 * t) (i - t)

theorem result_regular_to_left_indep (C c t i) :
    e.C.comp c (2*t) i = .single (C.comp c t (i + t))
```

### Result 2: k-Step Left-Independent Speedup

**File:** `proofs/constructions/speedup_left_independent.lean` (696 lines — the largest proof file)

**Statement:** Given a left-independent CA `C` and `k ≥ 2`, construct `C'` with state `Fin k → Q` compressing k consecutive diagonal cells. Coordinate maps:

- `ψ(i, j) = k·i + j` (spatial position)
- `φ(t, i, j) = t - (k-1)·i - j` (time)

For `i < 0` and `0 ≤ j < k`: `comp_{C'}(w, t, i)(j) = comp_C(w, φ(t,i,j), ψ(i,j))`.

**Construction details:** The construction has two variants:
1. `LeftIndepSpeedupQuiescent` — assumes quiescent border, uses a `fold` operation that builds k-tuples via `foldAux` with snoc construction.
2. `LeftIndepSpeedup` — no border assumption; composes with `QuiescentBorderLeftIndep` internally.

**Proof technique:** Outer induction on `t`, inner descending induction on `j` (from `k-1` down to `0`). The `j = k-1` base case reads from the fold's latest entry; the step case `j < k-1` propagates from the already-proven `j+1` entry. Extensive algebraic lemmas for the `ψ`/`φ` position/time mappings.

### Result 3: Quiescent Border for Left-Independent CAs

**File:** `proofs/constructions/border_quiescent.lean` (422 lines)

**Statement:** Given a left-independent CA `C`, construct `C'` with quiescent border `δ(#, #, #) = #`, preserving computation inside the left-independent light cone.

**Construction:** State `Q' = border | state(s, tracked_border)` where `tracked_border` records the iterated border state `δδt(C.border, t)`. Outside the cone, cells remain `border`; inside, cells track the original state plus the current border iteration.

Defines `WordConeLeftIndep w t = { i : ℤ | -t ≤ i < w.length }` — the causal cone for left-independent computation.

**Key properties preserved:**
- `C'.quiescent C'.border` (quiescent border)
- `C'.left_independent` (left-independence)
- `C'.comp w t i = if i ∈ cone then C.comp w t i else project(border)`

### Result 4: Dead Border

**File:** `proofs/constructions/border_dead.lean` (772 lines — second largest proof file)

**Statement:** Given any CA `C` and constant `c`, construct `C'` with completely dead (absorbing) border: `δ(a, #, b) = #` for all `a, b`. The trace is preserved: `C'.trace w t = C.trace w t` for all `t < c · |w|`.

**Construction:** Zigzag lane folding: the infinite tape is folded into `c` lanes indexed by `ℤ`. Even lanes read left-to-right, odd lanes right-to-left. Each lane of width `|w|` simulates one "fold" of the infinite tape. The `unfold` operation reconstructs the original position from the lane coordinates. The border of the folded tape is dead because the outermost lanes are padded with a guaranteed-dead state.

**Proof technique:** Establishes an invariant `inv` by induction on `t`: `unfold(C'.nextt w t, |w|, p) = C.nextt w t p` for `|p| < c·|w| - t`. Heavily uses integer division/modulo lemmas from `int_lemmas.lean`. The coordinate geometry proofs (`map_coord_prev`, `map_coord_next`) handle 6 cases each (left/right neighbor for even/odd lanes at various fold boundaries).

### Result 5: General k-Step RT Speedup

**File:** `proofs/constructions/speedup_k_step.lean` (194 lines)

**Statement:** For any CA `C` and `k`, construct `C'` with `trace_{C'}(w)(i) = trace_C(w)(i + k)`.

**Construction:** Iterated `SpBD` (Speedup with Border + DeadBorder):
- `Sp C` — one-step speedup: state `(Q, Q → Q)` tracks original state and a parametric function. `trace(Sp C, w, t) = trace(C, w, t+1)`.
- `SpB C` — `Sp` composed with marking the border (via `composeKSteps`).
- `SpBD C` — `SpB` composed with `DeadBorder` (ensures dead border for next iteration).
- `SpBDk c k C` — `SpBD` iterated `k` times.

Proof by induction on `k` for the main `SpBDk_trace_eq` theorem.

### Result 6: Exponential Word Length Recognition

**File:** `proofs/constructions/basic_exp_word.lean` (817 lines — largest file)

**Statement:** The language `{ w | ∃ n, |w| = 2^n }` is in `ℒ(CA_rt(Unit))`.

**Construction:** A signal-mirror CA: a **signal** is emitted from position 0 at time 0. A **mirror** moves rightward at speed 1/3. The signal bounces between position 0 and the mirror. The bounce times satisfy `bounce_time(k+1) = bounce_time(k) + 2·mirror_pos(k)`, which gives `bounce_time(k) = 2^k - 1`. The CA accepts iff the signal returns to position 0 at time `|w| - 1`.

**Proof technique:**
- `signal_invariant` — induction on `t`: the signal position matches a trajectory function `sig_traj`.
- `ca_mirror_matches` — the mirror evolves independently at the right side.
- `sig_traj_at_bounce` — induction on `k`: proves bounce times are `2^k - 1`.
- Composed with `leftEdgeCA` (detects `|w| > 0`) to handle arbitrary lengths.

---

## 4. Verified Results — Part II: Advice Theory

These results form the **core contribution** and are likely **novel**. All main theorems are sorry-free.

### Result 7: RT Transducers Closed Under Composition

**File:** `proofs/constructions/composition/compose_cart.lean` (359 lines) + 7 supporting files (1,824 lines total)

**Statement:** Given `C₁ : α? → β` and `C₂ : β? → γ`, construct `C` with `trace_rt(C) = trace_rt(C₂) ∘ trace_rt(C₁)`.

This is the most technically challenging result. The difficulty: CA `C₂` needs the *entire* output word of `C₁` as input, but in the real-time setting, each cell only observes local information. The key idea is to:

1. **Compress** `C₁`'s trace onto a diagonal (3 values per cell),
2. **Speed up** `C₂` by factor 3 to consume these triples,
3. **Simulate** the sped-up `C₂` using diagonal signals from `C₁`,
4. **Decompress** the triple outputs back to individual values,
5. **Speed up** by a constant to correct the time offset.

**Pipeline (8 sub-constructions):**

```
C₁ → AddBorder
        │
        ▼
    CompressToΛ  =  CompressToDiag ⨂ diag_right ⨂ diag_left
        │                │              │            │
        │         CAgfSpeedup     leftEdgeCA    diag_base
        │         (Reg→LI→         + idCA        + flip
        │          Speedup→Reg)
        ▼
    SimFromΛ  (simulates C₂ from diagonal triggers)
        │
        ▼
    DecompressTriple  (interleaves triple outputs)
        │
        ▼
    SpeedupKSteps(k=6)  (constant time correction)
        │
        ▼
    C.trace_rt = C₂.trace_rt ∘ C₁.trace_rt
```

**Sub-construction details:**

| File | Construction | Lines | Role |
|---|---|---|---|
| `compose_cart.lean` | `Composition` | 359 | Master pipeline assembly |
| `compress_to_diag.lean` | `CompressToDiag` | 244 | Extracts triples from speedup diagonal with 4-step history tracking |
| `sim_from_lambda.lean` | `SimFromΛ` | 338 | Simulates `C₂` using diagonal triggers; counter mod 3 + optional (new, old) state |
| `decompress_triple.lean` | `DecompressTriple` | 270 | Interleaves `(β³)?` into individual `β` over 3 time steps |
| `diag.lean` | `diag_left`, `diag_right` | 277 | Diagonal signal CAs: fire at `p ≤ 0, t = 3 + 2|p|` |
| `speedup_compressed.lean` | `CAgfSpeedup` | 148 | 3× speedup: Reg→LI→Speedup(3)→Reg with `g1`/`g2` decoders |
| `trace_kx.lean` | `TraceKx`, `SpeedupAndTraceKx` | 155 | k-fold shift register + spatial compression |
| `compose_two_stage.lean` | `backwards_fsm` | 279 | Backwards FSM for two-stage composition |

**Lean theorem:**
```
theorem result_rt_transducers_closed_under_composition
    (C1 : CellAutomaton α? β) (C2 : CellAutomaton β? γ) :
    (C2.compose_trace_rt C1).trace_rt = C2.trace_rt ∘ C1.trace_rt
```

### Result 8: Two-Stage Advice is RT-Closed

**File:** `proofs/two_stage_is_rt_closed.lean` (100 lines)

**Statement:** If `f` is a two-stage advice, then `ℒ(CA_rt(Σ × Γ) / f) = ℒ(CA_rt(Σ))`.

**Proof:** Given a receiving CA `C_r ∈ CA_rt(Σ × Γ)` using advice `f = M ∘ trace_rt(C_a)`, construct a combined CA that:
1. Runs `C_a` (the advice transducer) and a trace-identity CA in parallel.
2. Composes with `C_r` using Result 7.
3. Handles the empty word via `fix_empty`.

The reverse direction (`CA_rt(Σ) ⊆ CA_rt(Σ × Γ) / f`) is trivial: just ignore the advice channel.

### Result 9: Prefix-Membership Advice is Two-Stage

**File:** `proofs/advice_prefix_mem_rt_closed.lean` (40 lines)

**Statement:** For `L ∈ ℒ(CA_rt)`, the advice `f_L(w)_i = [w[0..i+1) ∈ L]` is two-stage.

**Proof:** Direct construction: the CA stage *is* the real-time recognizer for `L` (reading the acceptance bit at each step), and the FST stage is the identity (`M_id`). The two-stage advice then equals `M_id.scanr ∘ C.trace_rt = C.trace_rt`, which is exactly the prefix-membership function.

### Result 10: RT-Closed ∧ Causal ⟹ CArt Advice

**File:** `proofs/is_two_stage_of_rt_closed_and_causal.lean` (147 lines)

**Statement:** If advice `f : Σ* → Γ*` is both RT-closed and causal, then `f = trace_rt(C)` for some CA `C`.

**Proof:** For each output symbol `c ∈ Γ`, define language `L_c = { w | f(w)_{|w|-1} = c }`. By RT-closedness, each `L_c ∈ ℒ(CA_rt)`. Use `ProdCA` to run recognizers for all `L_c` in parallel. Define `first_true_or_default` to extract the matching symbol. By causality, `trace_rt` at position `i` only depends on `w[0..i+1)`, so the constructed transducer agrees with `f`. This also implies `f` is two-stage (with identity FST).

### Result 11: Two-Stage Advice Closed Under Composition

**File:** `proofs/constructions/composition/compose_two_stage.lean` (279 lines)

**Statement:** Given two-stage `f₁ = M₁ ∘ trace_rt(C₁)` and `f₂ = M₂ ∘ trace_rt(C₂)`, the composition `f₂ ∘ f₁` is two-stage.

**Proof:** The problem: `f₂ ∘ f₁ = M₂ ∘ trace_rt(C₂) ∘ M₁ ∘ trace_rt(C₁)`. We need two-stage form `M' ∘ trace_rt(C')`, but `trace_rt(C₂) ∘ M₁` puts a CA *after* an FST — the wrong order.

The **backwards FSM** construction resolves this: build `C'` that parametrically simulates `C₂` for *every possible* FSM state of `M₁`, storing the results in the state space. Then `M'` selects the correct simulation using the actual FSM state computed by `M₁`. Formally:

```
C₂ ∘ M₁ = M'(M₁, C₂) ∘ C'(M₁, C₂)
```

The key invariant (`inv`, induction on `t`): `C'.nextt` at each position `p` stores a function `M₁.Q → C₂.Q` mapping each possible FSM state to the corresponding `C₂` state.

### Result 12: Middle Advice is NOT Two-Stage

**File:** `proofs/middle_not_two_stage.lean` (216 lines)

**Statement:** The advice marking position `⌊n/2⌋` cannot be expressed as `M ∘ trace_rt(C)`.

**Proof:** A counting/pigeonhole argument:

1. **Bottleneck lemma** (`two_stage_restriction_cardinality`): The FST `M` has `|M.Q|` states, so it can produce at most `|M.Q|` distinct output prefixes for any given `trace_rt(C)(w)`.
2. **Distinct suffixes** (`distinct_prefixes_from_markers`): For word length `2K`, varying the right half of the word can place the middle marker at `K` different positions in the left half, producing `K` distinct advice outputs on the same prefix.
3. **Contradiction** (`middle_reachable_card`): For `K > |M.Q|`, there are more distinct outputs than FST states — contradiction.

---

## 5. Incomplete and Conjectured Results

### 5.1 Exponential-Middle Advice is Two-Stage (4 sorry)

**File:** `proofs/exp_middle_two_stage.lean` (438 lines)

The advice marking position `2^k` where `2^{k+1} ≤ n` is conjectured to be two-stage. The construction is **complete**:
- **CA stage:** `exp_prefix_CA` marks positions `i` where `i+1` is a power of 2.
- **FST stage:** `select_second_FST` scans right-to-left, counting `true` entries and selecting the second one.

The 4 remaining `sorry`s are in **combinatorial counting lemmas**:
- `countPow2After_eq` — counting power-of-2 positions after index `i`
- `exp_middle_idx_char` (2 sorry) — characterizing when `i+1 = exp_middle_idx(n)`
- `trace_drop_count_eq_countPow2After` — relating trace counts to `countPow2After`

These are straightforward (the statements are precise), but the list manipulation proofs are tedious.

### 5.2 Unproven Conjectures (`results_unproven.lean`)

| Conjecture | Sorry | Status |
|---|---|---|
| Constant speedup: `ℒ({C ∈ CA \| t(n) = n+k-1}) = ℒ(CA_rt)` | 1 | Classical result, not yet formalized |
| `ℒ(CA_lt) = ℒ(CA_2n)` | 1 | Classical result |
| `ℒ(OCA_lt) = ℒ(OCA_2n)` | 1 | Classical result |
| `ℒ(OCAr_lt) = ℒ(CA_rt)` | 1 | Classical result |
| Reversal closure → lt = rt | 1 | Classical result |
| Exp-middle is two-stage | 1 | Delegates to `exp_middle_two_stage.lean` |
| Shift-left preserves two-stage | 1 | "Peeking into the future" speedup |
| CartTraceFstAdvice classification | 1 | Characterization via RT-closed causal components |

### 5.3 Open Questions (`open_questions.lean`)

1. **Is every RT-closed advice two-stage?** (without the causal assumption)
2. **Does lt = rt?** (`CA_rt = CA_lt`)

The first is the central open question of the project. The conjecture is that no counterexample exists. A non-two-stage RT-closed advice would require a "non-geometric" simulation — potentially one that is computably unrecoverable.

---

## 6. Supporting Infrastructure

### 6.1 Core Lemma Libraries

| File | Lines | Contents |
|---|---|---|
| `proofs/basic.lean` | 431 | `nextt_congr` (locality), `nextt_shift`, `nextt_locality`, `nextt_add`, `trace_rt_is_causal`, `scan_temporal_independence`, `CA_rt_L_iff`, `ℒ_CA_rt_iff` |
| `proofs/border.lean` | 133 | `dead_border_prop`, `initial_border_prop`, `dead_implies_left_dead`, `border_stays_right` |
| `proofs/causal.lean` | ~50 | `IsCausal.empty`, `IsCausal.comp`, `IsCausal.take_of_concat`, `IsCausal.eq_iff` |
| `proofs/word_ops.lean` | ~70 | `advice_eq_iff`, `Word.fst`/`snd`, `Word.zip_fst`/`zip_snd` |
| `proofs/int_lemmas.lean` | 111 | Integer division/modulo lemmas for `DeadBorder` coordinate geometry |
| `proofs/ca_rt_utils.lean` | 142 | `ca_to_two_stage`, `zip_two_stage`, `advice_rt_closed_iff`, `exists_CA_rt_of_rt_closed` |

### 6.2 Basic CA Constructions

| File | Lines | Construction |
|---|---|---|
| `basic_ca_id.lean` | ~40 | Identity CA: `comp c t p = c p` |
| `basic_ca_left_edge_marker.lean` | ~80 | Detects left edge: output `true` iff border is to the left |
| `basic_compose_k_steps.lean` | 199 | Sequential composition: run `C₁` for `k` steps, then switch to `C₂` |
| `basic_exp_word.lean` | 817 | Signal-bouncing CA for `{2^n}` |
| `basic_flip.lean` | ~50 | Mirror a CA: `flip(C).comp c t p = C.comp (flip_config c) t (-p)` |
| `basic_mark_border.lean` | ~60 | Border detection: output whether current cell is border |
| `basic_product_ca.lean` | 137 | Product/zip of CAs: run two CAs in parallel with combined state |
| `trace_id.lean` | ~50 | Identity trace CA: `trace_rt = id` |
| `cart_fix_empty_word.lean` | ~40 | Fix edge case of empty word acceptance |

### 6.3 Finite-State Transducer Library

**File:** `proofs/finite_state_transducers.lean` (411 lines)

Comprehensive library of FST combinators:
- `M_id` — identity FST
- `M_projQ` — project to state
- `M_prod` / `M_prod2` — product of two FSTs
- `M_map` — map output
- `comp` — composition
- `map_output` — post-process output
- `compose_spec2` — `(M₂ ∘ M₁).scanr = M₂.scanr ∘ M₁.scanr`

Key structural lemmas: `scanr_foldr_state`, `scanr_append_take` (prefix independence), `scanr_cons`, `scanr_get'_eq1`/`eq2` (element-wise characterization).

### 6.4 Particle Framework

**File:** `proofs/framework/particle.lean` (166 lines)

A declarative framework for constructing CAs from "particle" specifications. Defines `ParticleCA`, `Movable` typeclass, `DeadSignal`, `SlowSignal`. Includes an `expParticleCA` example. Definitions only — no proofs yet. This is infrastructure for future constructions.

### 6.5 Axiom Verification

**Files:** `scripts/verify_proofs.lean`, `scripts/VerifyConfig.lean`

Automated verification that `results.lean` only depends on the three standard axioms: `Quot.sound`, `Classical.choice`, `propext`. The verifier walks the dependency tree of all constants in the module and checks against the allowed list.

### 6.6 Dependency Graph Generator

**File:** `scripts/dependencies.lean` (182 lines)

Generates a JSON dependency graph of all constants in the `CellularAutomatas` namespace. Output format: `{ "constants": { "name": { "dependencies": [...], "axioms": [...] } } }`.

---

## 7. File Dependency Structure

```
defs.lean (489 lines)
├── internal_defs.lean
│
├── proofs/basic.lean ← proofs/word_ops.lean, constructions/basic_product_ca.lean
│   │
│   ├── proofs/border.lean
│   ├── proofs/causal.lean
│   ├── proofs/int_lemmas.lean
│   ├── proofs/ca_rt_utils.lean
│   └── proofs/finite_state_transducers.lean
│
├── constructions/
│   ├── basic_ca_id.lean
│   ├── basic_ca_left_edge_marker.lean
│   ├── basic_compose_k_steps.lean
│   ├── basic_flip.lean
│   ├── basic_mark_border.lean
│   ├── basic_product_ca.lean
│   ├── trace_id.lean
│   ├── cart_fix_empty_word.lean
│   │
│   ├── border_quiescent.lean ← basic.lean, border.lean
│   ├── border_dead.lean ← basic.lean, border.lean, int_lemmas.lean
│   │
│   ├── left_indep_to_regular.lean ← basic.lean
│   ├── left_indep_from_regular.lean ← basic.lean, internal_defs.lean
│   │
│   ├── speedup_compressed.lean ← basic.lean
│   ├── speedup_left_independent.lean ← basic.lean, border.lean, border_quiescent.lean
│   ├── speedup_k_step.lean ← basic.lean, border.lean, border_dead.lean, causal.lean
│   │
│   ├── basic_exp_word.lean ← basic_compose_k_steps.lean, basic_ca_left_edge_marker.lean
│   │
│   └── composition/
│       ├── diag.lean ← basic_compose_k_steps, basic_ca_id, basic_ca_left_edge_marker
│       ├── speedup_compressed.lean ← left_indep_*, border_quiescent, speedup_left_independent
│       ├── trace_kx.lean ← speedup_compressed
│       ├── compress_to_diag.lean ← speedup_compressed (composition)
│       ├── sim_from_lambda.lean ← basic.lean
│       ├── decompress_triple.lean ← compress_to_diag
│       ├── compose_cart.lean ← ALL of the above + speedup_k_step
│       └── compose_two_stage.lean ← compose_cart, finite_state_transducers
│
├── proofs/
│   ├── middle_not_two_stage.lean ← basic.lean, finite_state_transducers.lean
│   ├── advice_prefix_mem_rt_closed.lean ← basic.lean, finite_state_transducers.lean
│   ├── two_stage_is_rt_closed.lean ← ca_rt_utils, compose_cart, compose_two_stage, trace_id
│   ├── is_two_stage_of_rt_closed_and_causal.lean ← compose_cart, basic, trace_id, FST, advice_prefix_mem, two_stage_is_rt_closed
│   └── exp_middle_two_stage.lean ← basic, FST, basic_exp_word, advice_prefix_mem, word_ops
│
├── results.lean ← all main theorem files (0 sorry)
├── results_unproven.lean ← basic_exp_word (10 sorry)
└── open_questions.lean (2 sorry)
```

---

## 8. Proof Technique Highlights

### Induction Patterns
- **Outer/inner induction** (speedup_left_independent): Outer on time `t`, inner descending on component index `j`.
- **Mutual induction** (left_indep_from_regular): Even and odd time steps proven simultaneously.
- **Phase induction** (basic_exp_word): Induction on bounce number `k` for signal trajectory.
- **Counter-cycle** (sim_from_lambda): Case matching on `(t, k)` pairs with termination by `(t, p.natAbs, k)`.

### Algebraic Backbone
- `ring_nf` and `omega` for position/time arithmetic throughout.
- `grind` for mixed boolean/arithmetic goals (especially `border_dead.lean`).
- Custom integer lemmas in `int_lemmas.lean` for division/modulo of folded coordinates.

### Counting Arguments
- Pigeonhole principle in `middle_not_two_stage.lean`: more distinct marker positions than FST states.
- Cardinality bounds via `Fintype.card` and `Finset.card_le_card`.

### Pipeline Verification
- The composition proof uses `calc` chains through all 6 pipeline stages.
- Each sub-construction has a standalone `spec` theorem.
- `IsCausal.eq_iff` enables verifying `trace_rt` equality by checking causality + pointwise agreement — crucial for the final composition theorem.

---

## 9. Relationship to Literature

The **base constructions** (Results 1–6) formalize classical results from the cellular automata literature (Kutrib, Malcher, Fischer, etc.). The proofs sometimes differ from the originals — e.g., the dead border uses zigzag folding rather than the textbook "expanding border" technique, making it more amenable to formal verification.

The **advice theory** (Results 7–12) is the **novel contribution**. The concept of two-stage advice and the characterization of causal RT-closed advice appear to be new. The composition theorem for RT transducers is known in principle but has not been formally verified before; the multi-stage pipeline required here is a significant engineering achievement.

The central **open question** — whether every RT-closed advice is two-stage — connects to questions about the computational geometry of one-dimensional CAs: can information always be rearranged by a two-stage (CA + FST) process, or do some RT-closed advices require fundamentally non-geometric simulations?
