# Research Summary: Formalization of Cellular Automata in Lean 4

## Abstract

This repository presents a formal verification framework for one-dimensional cellular automata and their computational properties using the Lean 4 theorem prover with Mathlib4. The primary novel contribution is a rigorous characterization of **"two-stage advice"** — a structured form of auxiliary information that can be computed in real-time and used to augment cellular automaton computations. The key proven results establish:

1. **A negative result**: The "middle marker" advice (which marks the middle position of a word) cannot be computed as a two-stage advice.
2. **Positive characterization**: Any advice that is both "rt-closed" (preserves real-time language class) and "prefix-stable" can be expressed as a two-stage advice.
3. **Closure properties**: Two-stage advices are closed under composition.

These results contribute to the theoretical understanding of what computational assistance is "easy" (real-time computable) versus "hard" for cellular automata, with implications for parallel computation theory.

---

## 1. Core Definitions

### 1.1 Cellular Automaton Hierarchy

The formalization establishes a type hierarchy of cellular automata:

- **`CellAutomaton α β`**: Basic cellular automaton with input alphabet `α`, output `β`, state space `Q`, and transition function `δ: Q → Q → Q → Q`.
- **`LCellAutomaton α`**: Cellular automaton that can process words (input alphabet is `Option α` allowing for boundary markers).
- **`tCellAutomaton α`**: Time-bounded cellular automaton with explicit time function `t: ℕ → ℕ` and observation position `p: ℕ → ℤ`.

### 1.2 Real-Time Classes

Key complexity classes formalized:

| Class | Definition | Description |
|-------|------------|-------------|
| `CA_rt α` | `t(n) = n - 1`, observe at position 0 | Real-time CA |
| `OCA_rt α` | Real-time + left-independent | One-way real-time CA |
| `CA_2n α` | `t(n) = 2n` | Linear-time (doubled) CA |
| `CA_lt α` | `t(n) = c·n` for some constant `c` | General linear-time CA |

### 1.3 Two-Stage Advice (Novel Concept)

A **two-stage advice** is a structured computation that:

```lean
structure TwoStageAdvice (α: Type) (Γ: Type) where
  β: Type                           -- Intermediate alphabet
  C: CArtTransducer α β            -- First stage: RT cellular automaton transducer
  M: FiniteStateTransducer β Γ     -- Second stage: FST scanning from right
```

The advice function is: `advice(w) = M.scanr(C.trace_rt(w))`

This captures advice that can be:
1. First computed by a real-time CA (reading left-to-right, outputting at each position)
2. Then post-processed by a finite-state transducer scanning right-to-left

---

## 2. Main Proven Results

### 2.1 Middle Marker Cannot Be Two-Stage (Negative Result)

**Theorem**: The advice `Advice.middle α` that marks the middle position of a word is *not* expressible as a two-stage advice.

```lean
theorem middle_not_two_stage_advice : ¬ (Advice.middle α).is_two_stage_advice
```

**Proof Technique**: A novel "bottleneck argument" showing that:
1. Any two-stage advice with FST state space of size `|Q|` can produce at most `|Q|` distinct prefixes for any fixed prefix of the input.
2. The middle marker requires `Ω(n)` distinct prefixes for prefixes of length `2n`.
3. This creates a contradiction for sufficiently large inputs.

### 2.2 Prefix-Membership Advice is Two-Stage (Positive Result)

**Theorem**: For any real-time CA language `L`, the advice indicating whether each prefix is in `L` is a two-stage advice.

```lean
theorem advice_prefix_mem_is_two_stage_advice (C: CA_rt α):
    (Advice.prefix_mem C.val.L).is_two_stage_advice
```

### 2.3 Characterization Theorem

**Theorem**: Any advice that is both rt-closed and prefix-stable can be expressed as a two-stage advice.

```lean
theorem is_two_stage_of_rt_closed_and_prefix_stable (adv: Advice α Γ) 
    (h1: adv.rt_closed) (h2: adv.prefix_stable): adv.is_two_stage_advice
```

Where:
- **rt-closed**: Using the advice doesn't expand the class of RT-recognizable languages
- **prefix-stable**: `adv.f(w.take i) = (adv.f w).take i` — advice on prefixes matches prefix of advice

### 2.4 Closure Under Composition

**Theorem**: Two-stage advices are closed under composition.

```lean
theorem advice_two_stage_closed_under_composition (a1: TwoStageAdvice α Γ') (a2: TwoStageAdvice Γ' Γ):
    (compose_two_stage a2 a1).advice.f = a2.advice.f ∘ a1.advice.f
```

This is proven via a sophisticated construction that interleaves a CA transducer with an FST operating "backwards" to maintain the two-stage structure.

---

## 3. Technical Innovations

### 3.1 Backwards FSM Construction

The proof of composition closure introduces a novel automaton construction (`backwards_fsm`) that:
- Tracks all possible FST states simultaneously
- Uses the CA to delay information appropriately
- Allows reconstruction of composed advice while maintaining two-stage structure

### 3.2 Cellular Automaton Composition

The repository develops a theory of CA composition with time complexity analysis:

```lean
def Composition.C : CellAutomaton α？ γ  -- Composes C1: α→β with C2: β→γ

theorem Composition.spec: C.trace_rt = C2.trace_rt ∘ C1.trace_rt
```

This involves:
- Time compression via `SpeedupKx` (k-step speedup)
- Trace buffering via `TraceKx`
- Signal propagation via `CompressToΛ`

---

## 4. Comparison to State of the Art

### 4.1 Classical Results (Not Formalized Before)

The formalized results connect to classical complexity theory:

| Classical Result | This Work |
|-----------------|-----------|
| RT ⊆ DTIME(n) [folklore] | Formalized `CA_rt` definitions |
| Advice hierarchies [Damm-Holzer] | Two-stage advice characterization |
| CA transducer composition | `CArtTransducer.compose` with proof |

### 4.2 Novel Contributions

1. **First Lean 4 formalization** of cellular automata with Mathlib4 integration
2. **Bottleneck lemma** for proving negative two-stage results
3. **Modular proof architecture** separating FST lemmas from CA proofs
4. **Decidability results**: `DecidablePred C.L` for real-time CA languages

---

## 5. Open Questions (Formally Stated)

```lean
-- Is every rt-closed advice a two-stage advice?
theorem open_question_1 (adv: Advice α Γ) (h: adv.rt_closed): adv.is_two_stage_advice := sorry

-- Is real-time equal to linear-time for CA?
theorem lt_eq_rt: CA_rt α = CA_lt α := sorry
```

---

## 6. Repository Structure

```
CellularAutomatas/
├── defs.lean                    -- Core type definitions
├── results.lean                 -- Main proven theorems
├── results_unproven.lean        -- Conjectured results (with sorry)
├── open_questions.lean          -- Formally stated open problems
└── proofs/
    ├── middle_not_two_stage.lean         -- Negative result proof
    ├── advice_prefix_mem_rt_closed.lean  -- Positive result
    ├── is_two_stage_of_rt_closed...lean  -- Characterization theorem
    ├── composition.lean                  -- CA composition theory
    └── finite_state_transducers.lean     -- FST lemmas
```

---

## 7. Value and Impact

### Theoretical Value
- Provides machine-checked proofs for results in parallel computation theory
- Establishes a foundation for formalizing cellular automata complexity
- Demonstrates that two-stage advice is a natural boundary in the advice hierarchy

### Practical Value
- The Lean 4 formalization serves as executable specification
- Modular design allows extension to other CA variants
- Integration with Mathlib4 enables reuse of extensive mathematical library

### Educational Value
- Clean separation of definitions, lemmas, and main theorems
- Extensive use of Lean 4 features (type classes, tactics, simp lemmas)
- Demonstrates formal methods applied to automata theory

---

## 8. Conclusion

This repository represents a significant step toward formalizing the computational theory of cellular automata. The key insight — that two-stage advice provides a clean characterization of "tractable" auxiliary information — is novel and has been rigorously verified. The negative result about middle markers and the positive characterization theorem together paint a clear picture of the boundary between two-stage and non-two-stage advice.

The work opens avenues for:
1. Formalizing the RT vs LT question
2. Extending to higher-dimensional CA
3. Connecting to circuit complexity formalizations
