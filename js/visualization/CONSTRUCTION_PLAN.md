# Plan: Port Lean CA Constructions to TypeScript

## Goal
Port all Lean cellular automata constructions to TypeScript for true simulation visualization.
Skip the k-step speedup construction, but include all others.

## Architecture

### Core Interface

```typescript
interface CellAutomaton<Q, Alpha, Beta> {
  readonly Q: { border: Q };  // State type with distinguished border
  readonly delta: (left: Q, center: Q, right: Q) => Q;
  readonly embed: (a: Alpha | undefined) => Q;
  readonly project: (q: Q) => Beta;
}
```

Each construction is a function that takes CA(s) and returns a new CA:
```typescript
type Construction<In, Out> = (input: In) => Out;
```

---

## Constructions to Port (in dependency order)

### 1. Basic Combinators

#### 1.1 `flip` - Mirror CA
**Lean source:** [CellularAutomatas/proofs/constructions/basic_flip.lean](../CellularAutomatas/proofs/constructions/basic_flip.lean)

```typescript
// Swap left and right in delta
function flip<Q, A, B>(ca: CA<Q, A, B>): CA<Q, A, B> {
  return {
    ...ca,
    delta: (l, c, r) => ca.delta(r, c, l)
  };
}
```

#### 1.2 `product` - Product of CAs
**Lean source:** [CellularAutomatas/proofs/constructions/basic_product_ca.lean](../CellularAutomatas/proofs/constructions/basic_product_ca.lean)

```typescript
// Run multiple CAs in parallel
function product<Q1, Q2, A, B1, B2>(
  ca1: CA<Q1, A, B1>,
  ca2: CA<Q2, A, B2>
): CA<[Q1, Q2], A, [B1, B2]>;
```

#### 1.3 `map_project` - Transform output
```typescript
function mapProject<Q, A, B, C>(
  ca: CA<Q, A, B>,
  f: (b: B) => C
): CA<Q, A, C>;
```

---

### 2. Conversion Constructions

#### 2.1 `RegularToLeftIndep` - Regular → Left-Independent
**Lean source:** [CellularAutomatas/proofs/constructions/left_indep_from_regular.lean](../CellularAutomatas/proofs/constructions/left_indep_from_regular.lean)

**State space:** `Q' = single(q) | pair(q₁, q₂) | dead`

**Key property:** The resulting CA is left-independent (δ(a, b, c) = δ(a', b, c))

**Time mapping:** 
- At even t: `single(q)` at position `i + t/2`
- At odd t: `pair(q₁, q₂)` at positions `i + ⌊t/2⌋, i + ⌊t/2⌋ + 1`

```typescript
interface RegularToLeftIndepState<Q> {
  type: 'single' | 'pair' | 'dead';
  q?: Q;
  q1?: Q;
  q2?: Q;
}

function regularToLeftIndep<Q, A, B>(ca: CA<Q, A, B>): CA<RegularToLeftIndepState<Q>, A, B>;
```

#### 2.2 `LeftIndepToRegular` - Left-Independent → Regular
**Lean source:** [CellularAutomatas/proofs/constructions/left_indep_to_regular.lean](../CellularAutomatas/proofs/constructions/left_indep_to_regular.lean)

**Key insight:** Since C is left-independent, we can compute TWO steps in ONE:
```
δ'(a, b, c) = δ(_, δ(_, a, b), δ(_, b, c))
```

**Time mapping:** `C'.comp(c, t, i) = C.comp(c, 2t, i - t)`

```typescript
function leftIndepToRegular<Q, A, B>(
  ca: CA<Q, A, B>,
  hLeftIndep: true  // assertion that ca is left-independent
): CA<Q, A, B>;
```

---

### 3. Diagonal Signal Constructions

#### 3.1 `DiagLeft` - Left diagonal signal
**Lean source:** [CellularAutomatas/proofs/constructions/composition/diag.lean](../CellularAutomatas/proofs/constructions/composition/diag.lean)

**States:** `idle | hold | fire`

**Behavior:** Fires at position p ≤ 0 at time t = 2|p| + 3

```typescript
type DiagQ = 'idle' | 'hold' | 'fire';

const diagLeft: CA<DiagQ, Unit, Bool> = {
  delta: (l, c, r) => {
    if (c === 'fire') return 'hold';
    if (c === 'hold') return 'idle';
    if (r === 'hold') return 'fire';
    return 'idle';
  },
  // input [()] triggers fire at position 0
  embed: (a) => a !== undefined ? 'fire' : 'idle',
  project: (q) => q === 'fire'
};
```

#### 3.2 `DiagRight` - Right diagonal signal  
Mirror of DiagLeft, fires at p ≥ 0

---

### 4. Compression Constructions

#### 4.1 `CAgfSpeedup` - 3x Compressed Speedup
**Lean source:** [CellularAutomatas/proofs/constructions/speedup_compressed.lean](../CellularAutomatas/proofs/constructions/speedup_compressed.lean)

**State:** Tracks 3 consecutive time steps of the original CA

**Output functions:**
- `g1(q)`: Extract middle time step
- `g2(q)`: Extract pair (first, third) time steps

```typescript
interface SpeedupState<Q> {
  step0: Q;
  step1: Q;
  step2: Q;
}

function cAgfSpeedup<Q, A, B>(ca: CA<Q, A, B>): {
  C: CA<SpeedupState<Q>, A, B>;
  g1: (b: B) => B;
  g2: (b: B) => [B, B];
};
```

#### 4.2 `CompressToDiag` - Compress to Diagonal Timing
**Lean source:** [CellularAutomatas/proofs/constructions/composition/compress_to_diag.lean](../CellularAutomatas/proofs/constructions/composition/compress_to_diag.lean)

**Key property:** At position p ≥ 0, time 2p + 3, outputs triple `(trace(3p), trace(3p+1), trace(3p+2))`

**State:** Tracks 4 time steps of speedup.C plus right neighbor history

```typescript
interface CompressToDiagState<Q> {
  self: [Q, Q, Q, Q];       // 4 steps at our position
  rightHist: [Q, Q, Q, Q];  // 4 steps from right neighbor
}

function compressToDiag<Q, A, B>(ca: CA<Q, A, B>): CA<CompressToDiagState<SpeedupState<Q>>, A, [B, B, B] | null>;
```

---

### 5. Composition Pipeline Components

#### 5.1 `AddBorder` - Mark border cells
**Lean source:** [CellularAutomatas/proofs/constructions/composition/compose_cart.lean](../CellularAutomatas/proofs/constructions/composition/compose_cart.lean#L100-L160)

Runs original CA in parallel with a border marker. Output:
- `some(v)` for non-border cells
- `none` for border cells

```typescript
function addBorder<Q, A, B>(ca: CA<Q, A, B>): CA<[Q, Bool], A, B | null>;
```

#### 5.2 `CompressToΛ` - Full compression to control signal
**Lean source:** [CellularAutomatas/proofs/constructions/composition/compose_cart.lean](../CellularAutomatas/proofs/constructions/composition/compose_cart.lean#L25-L110)

Combines:
- CompressToDiag (data source)
- DiagRight (positive position signal)
- DiagLeft (negative position signal)

Output at time 3 + 2|p|:
- For p ≥ 0: computed triple from trace
- For p < 0: `(none, none, none)` placeholder

```typescript
function compressToLambda<Q, A, B>(ca: CA<Q, A, B>): CA<...>, A, [[B | null, B | null, B | null] | null]>;
```

#### 5.3 `SpeedupAndTraceKx` (k=3)
**Lean source:** [CellularAutomatas/proofs/constructions/composition/trace_kx.lean](../CellularAutomatas/proofs/constructions/composition/trace_kx.lean)

Takes a CA with input type β and makes it work on β³ (triples).
Computes 3 steps of the original CA per step.

```typescript
function speedupAndTraceKx<Q, A, B>(
  k: 3,
  ca: CA<Q, A, B>
): CA<[Q, Q, Q], [A, A, A], [B, B, B]>;
```

#### 5.4 `SimFromΛ` - Simulation from Lambda Control
**Lean source:** [CellularAutomatas/proofs/constructions/composition/sim_from_lambda.lean](../CellularAutomatas/proofs/constructions/composition/sim_from_lambda.lean)

**This is the core of the composition construction!**

**Inputs:**
- `C_ctl`: Control CA that outputs triggers (from CompressToΛ)
- `C_inr`: Inner CA to simulate (from SpeedupAndTraceKx)

**State:**
```typescript
interface SimFromLambdaState<Q_ctl, Q_inr> {
  state: Q_ctl;           // Control CA state
  counter: 0 | 1 | 2;     // Phase counter (3 real steps = 1 inner step)
  sim: [Q_inr, Q_inr] | null;  // (current, previous) inner states
}
```

**Transition logic:**
1. When control CA outputs a trigger value `s`:
   - Initialize sim = (embed(s), embed(s))
   - Reset counter = 0

2. When counter = 2 (time to compute inner step):
   - Read neighbors' inner values (using counter for synchronization)
   - Compute next inner state: `δ_inr(left_val, cur_val, right_val)`
   - Update sim = (new_val, cur_val), counter = 0

3. Otherwise (counter < 2):
   - Just increment counter

**Output:** When counter = 0 and sim exists, output `project(sim.current)`

#### 5.5 `DecompressTriple` - Unpack triples
**Lean source:** [CellularAutomatas/proofs/constructions/composition/decompress_triple.lean](../CellularAutomatas/proofs/constructions/composition/decompress_triple.lean)

**State:** `(original_state, counter mod 3, stored_triple)`

At time 3t₁ + t₂ + k, outputs element t₂ from the triple computed at time 3t₁ + k.

```typescript
interface DecompressState<Q, B> {
  q: Q;
  counter: 0 | 1 | 2;
  triple: [B, B, B];
}

function decompressTriple<Q, A, B>(
  ca: CA<Q, A, [B, B, B] | null>
): CA<DecompressState<Q, B>, A, B>;
```

---

### 6. Full Composition

**Lean source:** [CellularAutomatas/proofs/constructions/composition/compose_cart.lean](../CellularAutomatas/proofs/constructions/composition/compose_cart.lean#L200-L300)

```typescript
function compose<A, B, C>(
  c1: CA<?, A, B>,  // First CA: α? → β
  c2: CA<?, B, C>   // Second CA: β? → γ
): CA<?, A, C> {
  // Pipeline:
  // 1. C1' = addBorder(C1)                    : α? → β?
  // 2. C1_Λ = compressToLambda(C1')          : α? → (β?³)?
  // 3. C2_3x = speedupAndTraceKx(3, C2)      : β?³ → γ³
  // 4. C_sim = simFromLambda(C1_Λ, C2_3x)    : α? → (γ³)?
  // 5. C_decomp = decompressTriple(C_sim)    : α? → γ
  // 6. [SKIP: SpeedupKSteps would go here]
  
  const c1Prime = addBorder(c1);
  const c1Lambda = compressToLambda(c1Prime);
  const c2_3x = speedupAndTraceKx(3, c2);
  const cSim = simFromLambda(c1Lambda, c2_3x);
  const cDecomp = decompressTriple(cSim);
  return cDecomp;
}
```

---

## Files to Create

1. `visualization/src/ca-constructions/types.ts` - Core CA interface
2. `visualization/src/ca-constructions/basic.ts` - flip, product, mapProject
3. `visualization/src/ca-constructions/conversions.ts` - RegularToLeftIndep, LeftIndepToRegular
4. `visualization/src/ca-constructions/diagonal.ts` - DiagLeft, DiagRight
5. `visualization/src/ca-constructions/compression.ts` - CAgfSpeedup, CompressToDiag
6. `visualization/src/ca-constructions/composition.ts` - AddBorder, CompressToΛ, SpeedupAndTraceKx, SimFromΛ, DecompressTriple
7. `visualization/src/ca-constructions/pipeline.ts` - Full compose function
8. `visualization/src/ca-constructions/index.ts` - Re-exports

---

## Verification Strategy

For each construction:
1. Implement the state type and transition function
2. Run on simple test inputs
3. Compare outputs with expected behavior from thesis/Lean definitions
4. Visualize intermediate states to verify correctness

## Notes

- Unlike Lean, TypeScript doesn't have dependent types, so we use runtime checks
- State types use discriminated unions (type: 'single' | 'pair' | 'dead')
- Border handling via undefined/null in Option-like patterns
- All constructions preserve the trace_rt semantic (real-time trace of outputs)
