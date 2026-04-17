# Composition of Real-Time CA Transducers

This directory proves that real-time cellular automaton transducers (CARTs) are **closed under composition** (Result 5), and extends this to two-stage advices (Result 9).

Given `C1 : CellAutomaton α？ β` and `C2 : CellAutomaton β？ γ`, we construct `C : CellAutomaton α？ γ` such that `C.trace_rt = C2.trace_rt ∘ C1.trace_rt`.

## Pipeline

The composition is not direct — a CA cannot simply feed one cell's output into another, because intermediate results arrive at different times across positions. The key idea is to:

1. **Compress** `C1`'s trace onto a diagonal (3 values per cell),
2. **Speed up** `C2` by factor 3 to consume triples,
3. **Simulate** the sped-up `C2` using diagonal signals from `C1`,
4. **Decompress** the triple outputs back to individual values.

```
  C1 : α？ → β                                          C2 : β？ → γ
       │                                                      │
       ▼                                                      ▼
  ┌ AddBorder ───────────────────────────┐    ┌ SpeedupAndTraceKx ──────────────┐
  │                                      │    │                                  │
  │   C1  ⨂  MarkBorder  → map_project  │    │   ┌ TraceKx ─────────────────┐   │
  │                                      │    │   │  stores k+1 time steps   │   │
  │   out: α？ → β？                      │    │   │  out: β？ → (Fin k → β？) │   │
  └───────────────┬──────────────────────┘    │   └──────────┬───────────────┘   │
                  │                           │              ▼                   │
                  │                           │   ┌ SpeedupKx ───────────────┐   │
                  │                           │   │  spatial compression     │   │
                  │                           │   │  (Fin 3 → α) → (Fin 3 → β) │
                  │                           │   └──────────────────────────┘   │
                  │                           │   → map_project                  │
                  │                           │                                  │
                  │                           │   out: (β？)³ → γ³               │
                  │                           └───────────────┬──────────────────┘
                  ▼                                           │
  ┌ CompressToΛ ───────────────────────────────────┐          │
  │                                                │          │
  │   ┌ CompressToDiag ─────────────────────────┐  │          │
  │   │                                         │  │          │
  │   │   ┌ CAgfSpeedup ────────────────────┐   │  │          │
  │   │   │                                 │   │  │          │
  │   │   │  RegToLI ──▶ LISpeedup ──▶ LIToReg │  │          │
  │   │   │                                 │   │  │          │
  │   │   └─────────────────────────────────┘   │  │          │
  │   │                                         │  │          │
  │   │   wraps CAgfSpeedup with 4-step history │  │          │
  │   │   tracking; decodes triples via g1/g2   │  │          │
  │   │                                         │  │          │
  │   └─────────────────────────────────────────┘  │          │
  │                                                │          │
  │   ┌ diag_right ─────────────────────────────┐  │          │
  │   │  leftEdgeCA ──▶ idCA ──▶ diag_base.flip │  │          │
  │   │  fires at p ≥ 0, t = 3 + 2·p            │  │          │
  │   └─────────────────────────────────────────┘  │          │
  │                                                │          │
  │   ┌ diag_left ──────────────────────────────┐  │          │
  │   │  leftEdgeCA ──▶ idCA ──▶ diag_base      │  │          │
  │   │  fires at p ≤ 0, t = 3 + 2·|p|          │  │          │
  │   └─────────────────────────────────────────┘  │          │
  │                                                │          │
  │   CompressToDiag ⨂ diag_right ⨂ diag_left     │          │
  │   → map_project (gates output to diagonal)     │          │
  │                                                │          │
  │   out: α？ → (β？³)?                            │          │
  └────────────────────────┬───────────────────────┘          │
                           │                                  │
                           ▼                                  ▼
                     ┌ SimFromΛ ──────────────────────────────────┐
                     │                                            │
                     │   Simulates C_inr on the configuration     │
                     │   provided by C_ctl along the diagonal     │
                     │                                            │
                     │   out: α？ → (γ³)?                         │
                     └────────────────────┬───────────────────────┘
                                          │
                                          ▼
                               ┌ DecompressTriple ──┐
                               │                    │
                               │   unpacks triples  │
                               │   out: α？ → γ     │
                               └─────────┬──────────┘
                                         │
                                         ▼
                     ┌ SpeedupKSteps (k=6, c=7) ─────────────────┐
                     │                                            │
                     │   iterates SpBD k times (SpBDk):           │
                     │   each SpBD = Sp ∘ DeadBorder              │
                     │                                            │
                     │   Sp:         left-border shift (+1 step)  │
                     │   DeadBorder: ensures dead border property │
                     │                                            │
                     │   out: α？ → γ                             │
                     └────────────────┬──────────────────────────┘
                                      │
                                      ▼
                          C.trace_rt = C2.trace_rt ∘ C1.trace_rt

Legend:  ──▶  sequential pipeline (composeKSteps)
         ⨂   parallel product (same input, combined output)
        ┌ ┐  nesting = wraps / contains sub-construction
```

## Supporting Constructions

### Diagonal Signals — [diag.lean](diag.lean)

Constructs CAs that fire a `true` signal along the left or right diagonal of the space-time diagram. `diag_left` fires at position `p ≤ 0` at time `3 + 2·|p|`, `diag_right` mirrors this for `p ≥ 0`. These signals tell `CompressToΛ` *when* to emit the compressed configuration at each cell.

### 3× Speedup — [speedup_compressed.lean](speedup_compressed.lean)

A three-stage sub-pipeline (shown as `CAgfSpeedup` in the diagram above) that speeds up a CA by factor 3: Regular → LeftIndep → Speedup k=3 → Regular. Defines decoding functions `g1` and `g2` to extract original trace values from the sped-up output.

### Backwards FSM — [compose_two_stage.lean](compose_two_stage.lean)

Extends CART composition to **two-stage advices** (`TwoStageAdvice α Γ = FSM ∘ CART`). The problem: composing `(M₂ ∘ C₂) ∘ (M₁ ∘ C₁)` yields `M₂ ∘ (C₂ ∘ M₁) ∘ C₁`, where a CA follows an FSM — the wrong order for two-stage form. The backwards FSM construction rearranges `C ∘ M` into `M' ∘ C'` by parametrically simulating the CA over all possible FSM states, then selecting the correct result with a new FSM.

## File Overview

| File | Construction | Role |
|---|---|---|
| [compose_cart.lean](compose_cart.lean) | `AddBorder`, `CompressToΛ`, `Composition` | Master file assembling the full pipeline |
| [compress_to_diag.lean](compress_to_diag.lean) | `CompressToDiag` | Compress trace onto diagonal as triples |
| [decompress_triple.lean](decompress_triple.lean) | `DecompressTriple` | Unpack triples into individual values |
| [diag.lean](diag.lean) | `diag_left`, `diag_right` | Diagonal signal generators |
| [sim_from_lambda.lean](sim_from_lambda.lean) | `SimFromΛ` | Simulate inner CA from control signals |
| [speedup_compressed.lean](speedup_compressed.lean) | `CAgfSpeedup` | 3× speedup via left-independent detour |
| [trace_kx.lean](trace_kx.lean) | `TraceKx`, `SpeedupAndTraceKx` | k-fold trace storage and compressed speedup |
| [compose_two_stage.lean](compose_two_stage.lean) | `backwards_fsm`, `compose_two_stage` | Two-stage advice closure under composition |
