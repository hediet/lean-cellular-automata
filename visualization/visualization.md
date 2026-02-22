# CA Construction & Visualization Framework

## Brainstorm

### Core CellAutomaton type

Current (good):
```typescript
interface CellAutomaton<Q, Alpha, Beta> {
    readonly embed: (a: Alpha | undefined) => Q;
    readonly delta: (left: Q, center: Q, right: Q) => Q;
    readonly project: (q: Q) => Beta;
}
```

Note: `border` is just `embed(undefined)`. Remove it; derive it.

For compressed CAs, use `Tuple<Q>` = `readonly Q[]` instead of `(j: number) => Q`.
This is more natural in TypeScript (JSON-serializable, equality-checkable, inspectable).

### Config optimization: flat array representation

Instead of `ReadonlyMap<number, Q>`, use a flat array with an offset:

```typescript
class Config<Q> {
    constructor(
        readonly cells: readonly Q[],   // Dense array of active cells
        readonly cellOffset: number,    // cells[0] corresponds to position cellOffset
        readonly border: Q              // = embed(undefined)
    ) {}

    get(i: number): Q {
        const idx = i - this.cellOffset;
        if (idx < 0 || idx >= this.cells.length) return this.border;
        return this.cells[idx];
    }
}
```

`next` only needs to update `cells` plus one cell before and one after:
```typescript
function next(ca, config): Config<Q> {
    // New cells array: from (offset - 1) to (offset + cells.length)
    // i.e. cells.length + 2 entries, offset = prev.offset - 1
    const newOffset = config.cellOffset - 1;
    const newLen = config.cells.length + 2;
    const newCells = new Array(newLen);
    for (let idx = 0; idx < newLen; idx++) {
        const p = newOffset + idx;
        newCells[idx] = ca.delta(config.get(p-1), config.get(p), config.get(p+1));
    }
    // Optionally trim border values from edges
    return new Config(newCells, newOffset, ca.delta(border, border, border));
}
```

Note: border for the next step is `delta(border, border, border)`, not `border` — quiescent states don't always map to themselves! In our Lean proofs we usually require quiescence, but the optimization should be correct regardless. If `delta(b,b,b) = b` (quiescent), then we can keep the same border and trim. Otherwise the active region truly expands every step.

Benefits:
- No Map overhead — pure array access
- Cache-friendly sequential iteration
- Easy to serialize
- `cellOffset` shifts by -1 each step (light cone naturally grows)

### Reflection/Meta system for plugging CAs together

The key idea: a **construction** is a function that takes CA(s) → CA, but it also carries **metadata** about how to render, inspect, and highlight states.

```typescript
interface CellAutomaton<Q, Alpha, Beta> {
    readonly embed: (a: Alpha | undefined) => Q;
    readonly delta: (left: Q, center: Q, right: Q) => Q;
    readonly project: (q: Q) => Beta;

    // Meta/rendering: how to visualize a single state of this CA
    readonly renderState: (q: Q, ctx: RenderContext) => React.ReactNode;

    // Decompose a state into sub-states for highlighting/tracing
    readonly decomposeState?: (q: Q) => StateDecomposition;
}
```

A `StateDecomposition` would tell the UI which parts of a compound state map back to which inner CA states:
```typescript
interface StateDecomposition {
    // Named sub-components, each referencing an inner CA
    parts: {
        label: string;
        caRef: CellAutomaton<unknown, unknown, unknown>;
        state: unknown;
    }[];
}
```

This is the *reflection* aspect: a composed CA knows it's composed, and can tell the UI "my state has a `.fst` from CA₁ and a `.snd` from CA₂".

### Rendering approach: how should we render cells?

**Current:** SVG with hand-coded positions. Each construction class has `renderTransformedCell(ctx)` returning `<circle>`, `<rect>`, `<text>` elements positioned at `(cx, cy)`. Cell size is fixed at ~32px. No layout engine — everything is manual.

**Options for the framework:**

1. **Fixed-width SVG cells** (simplest)
   - Each CA's `renderState` returns SVG elements in a local coordinate system (e.g., [-1, -1] to [1, 1]).
   - The space-time diagram places them in a grid with fixed cell size.
   - Scaling: `transform="scale(s)"` on the SVG group.
   - Pros: Easy composition, SVG scales well, vector-crisp at any zoom.
   - Cons: SVG performance degrades with thousands of elements.

2. **Canvas rendering** (fastest)
   - Each CA's `renderState` gets a canvas context + bounding rect.
   - Pros: Much faster for large diagrams.
   - Cons: No DOM events per cell (need manual hit-testing), harder to compose, no built-in hover/click.

3. **Absolutely-positioned SVG per cell** (hybrid)
   - Each cell is a small SVG element positioned via CSS.
   - Pros: Each cell is an independent DOM element → easy events.
   - Cons: Many DOM elements = slow.

**Recommendation:** Start with option 1 (fixed-width SVG cells, local coord system). Switch to canvas later only if performance is an issue.

The render function signature:
```typescript
// Renders into a normalized [-0.5, -0.5] to [0.5, 0.5] coordinate space
// The framework scales/translates to the actual cell position
renderState: (q: Q, ctx: RenderContext) => React.ReactNode;

interface RenderContext {
    readonly scale: number;       // Current cell size in pixels
    readonly minScale: number;    // Minimum useful scale (for LOD)
    readonly highlighted: boolean;
    readonly selected: boolean;
}
```

At small scales (deeply nested), `renderState` can return a simple colored rect instead of detailed sub-components. The `scale` parameter enables level-of-detail.

### Identity tracking via wrapped states (addIdentity)

**Core idea:** States are opaque. The visualization system can give them identity (tracking where they came from) by wrapping:

```typescript
class IdentifiedState<Q> {
    constructor(
        readonly inner: Q,
        readonly origin: { position: number; time: number }
    ) {}
}

function addIdentity<Q, A, B>(ca: CellAutomaton<Q, A, B>): CellAutomaton<IdentifiedState<Q>, A, B> {
    return {
        embed: (a) => new IdentifiedState(ca.embed(a), { position: ???, time: 0 }),
        delta: (l, c, r) => new IdentifiedState(
            ca.delta(l.inner, c.inner, r.inner),
            { position: c.origin.position, time: c.origin.time + 1 }
        ),
        project: (q) => ca.project(q.inner),
        renderState: (q, ctx) => ca.renderState(q.inner, ctx),
    };
}
```

**Problem with embed:** `embed` doesn't know the position. It only gets the symbol.

**Solution — IdentitySymbol:**
```typescript
class IdentitySymbol<A> {
    constructor(readonly symbol: A, readonly position: number) {}
}

// The input word becomes: word.map((a, i) => new IdentitySymbol(a, i))
// embed maps IdentitySymbol to IdentifiedState with known position
```

But this changes the Alpha type from `A` to `IdentitySymbol<A>`, which means the CA's type signature changes. That's fine — `addIdentity` is a construction that transforms `CellAutomaton<Q, A, B>` into `CellAutomaton<IdentifiedState<Q>, IdentitySymbol<A>, B>`.

**What does identity tracking enable?**
- Every state in the space-time diagram knows its (p, t) origin.
- When a construction composes CAs, inner states *still carry their identity*.
- Hovering a SimFromΛ cell: the inner C2_3x state has identity from C2_3x's space-time. The control state has identity from C1_Λ's space-time. → highlight both.
- No need for `decomposeState` — identity is baked into the state itself.

**Limitation:** `delta` creates a new state with `c.origin` as position (the center cell's origin). This loses the dependency on `l` and `r`. For dependency highlighting (which cells contributed to this one?), you'd need to store all three parent identities. That makes the state grow logarithmically with depth.

**Alternative: on-demand identity.** Don't store identity in the state. Instead, when the user clicks a cell at (p, t), walk the dependency graph backward on demand:
- Cell (p, t) depends on (p-1, t-1), (p, t-1), (p+1, t-1).
- The clicked cell's state was produced by `delta(state[p-1,t-1], state[p,t-1], state[p+1,t-1])`.
- For compound states: `decomposeState` tells you which parts came from which inner CA.
- Walk backward in each inner CA's space-time to find the corresponding cells.

This is cheaper (no extra per-state storage) but requires keeping the full space-time grids in memory (which we already do for the visualization).

### Highlighting

**Current approach** — broken:
The current code uses `HoverState = { origP, origT, deps }` which references the "original" CA's space-time coordinates. This works for constructions that map (i,t) → original cells, but fails for compositions where there's no simple mapping.

**Problem**: In SimFromΛ, a cell at (p, t) contains state from the *control CA* at (p, t) AND the *inner CA* at (p, innerStep). These are two different space-time diagrams. Hovering should highlight both.

**Proposed approach — state-identity-based highlighting:**

Instead of tracking dependencies via coordinates, track them via **state provenance**:

```typescript
interface StateProvenance {
    // Which CA produced this state
    ca: CellAutomaton<unknown, unknown, unknown>;
    // Position in that CA's space-time diagram
    position: number;
    time: number;
    // Sub-provenances for compound states
    children?: StateProvenance[];
}
```

When you hover over a cell, the CA's `decomposeState` tells you which inner CAs contributed. The UI then highlights all cells in all diagrams that share any provenance.

This is more powerful than coordinate-based deps:
- Hovering a SimFromΛ cell highlights the C1_Λ cell at (p,t) AND the C2_3x cell at (p,innerStep).
- Hovering a product cell highlights both component CAs.
- Works recursively for deeply nested constructions.

### How does the current highlighting work?

Currently in `constructions.tsx`:
1. `HoverState` stores `{ origP, origT }` — coordinates in the **original** CA's space-time.
2. `getCellContent(i, t)` returns `OriginalCell[]` mapping transformed coordinates → original coordinates.
3. When hovering, the UI highlights cells whose original coordinates match.
4. `getDependencies(p, t)` returns the 3 (or 2) parent cells at time t-1.

This only works for constructions with a static coordinate mapping (speedup, flip, product).
It completely breaks for SimFromΛ where the inner CA has its own independent space-time.

### Construction as a CA-producing function with metadata

```typescript
interface Construction<Inputs, Q, Alpha, Beta> {
    // Produce the composed CA
    build(inputs: Inputs): CellAutomaton<Q, Alpha, Beta>;
    
    // Metadata
    readonly name: string;
    readonly description: string;
    
    // UI parameters (like k for speedup)
    readonly params: ParamSpec[];
}
```

Where `Inputs` could be `{ C1: CellAutomaton<...>, C2: CellAutomaton<...> }` for composition,
or `{ C: CellAutomaton<...>, k: number }` for speedup.

### What about the space-time diagram rendering?

The space-time diagram is generic: given a CA and a word, simulate and render each cell using `ca.renderState`. The rendering framework doesn't need to know about specific constructions.

Multiple diagrams can be shown side by side:
- The "original" CA's space-time
- The "constructed" CA's space-time
- With highlighting links between them via provenance

### Tuple type

```typescript
// Instead of (j: number) => Q:
type Tuple<Q> = readonly Q[];

// SpeedupKx state: Tuple<Q> of length k
// CompressToDiag state: { self: Tuple<SpeedupState>, rightHist: Tuple<SpeedupState> }
// SimFromΛ state: { ctlState: Q_ctl, counter: 0|1|2, sim: [Q_inr, Q_inr] | null }
```

Benefits:
- JSON-serializable → inspectable in dev tools
- Structural equality via JSON.stringify (or deep compare)
- Works with `Array.map`, `Array.every`, etc.
- No hidden closure state

---

## Idea Rankings

### Tier 1: High impact, do first
1. **`renderState` on CellAutomaton** — Enables self-describing CAs. Constructions compose renderers automatically. Foundation for everything else.
2. **Flat-array Config** — Simple, big perf win, easy to implement. Array + offset replaces Map.
3. **`readonly Q[]` tuples** — Low effort, high clarity. Replace all `(j: number) => Q`.

### Tier 2: High impact, needs design
4. **`decomposeState` for highlighting** — Solves the cross-diagram highlighting problem. Moderate complexity. Can be added incrementally (only CAs that need it implement it).
5. **Fixed-width SVG cells with normalized coordinates** — Clean separation of layout from rendering. Each CA renders in [-0.5, 0.5]², framework handles placement.

### Tier 3: Interesting but can wait
6. **`addIdentity` wrapping** — Elegant but adds per-state overhead. The on-demand approach (walk backward on click) achieves the same for highlighting with zero runtime cost. Most useful as a debugging/inspection tool, not essential for rendering.
7. **Canvas rendering** — Only needed if SVG performance becomes a bottleneck. Current diagrams are <1000 cells, fine for SVG.

### Not recommended
8. **Absolutely-positioned SVG per cell** — Worst of both worlds (many DOM elements, complex CSS layout). Skip.

---

## Decided

### CellAutomaton interface (v2)

```typescript
interface CellAutomaton<Q, Alpha, Beta> {
    readonly embed: (a: Alpha | undefined) => Q;
    readonly delta: (left: Q, center: Q, right: Q) => Q;
    readonly project: (q: Q) => Beta;

    // Rendering: returns SVG elements in normalized [-0.5, -0.5] to [0.5, 0.5] space
    readonly renderState: (q: Q, ctx: RenderContext) => React.ReactNode;
}

interface RenderContext {
    readonly scale: number;       // Cell size in pixels
    readonly highlighted: boolean;
    readonly selected: boolean;
}
```

No `border` field. It's `embed(undefined)`.

### Use `readonly Q[]` instead of `(j: number) => Q`

More natural in TypeScript. All compressed states use arrays.

### Remove `CA<Q, A, B>` alias

Just use `CellAutomaton<Q, A, B>` everywhere. The alias adds confusion.

### Rendering is part of the CA

Each CA defines how to render its states. Constructions compose renderers from their input CAs. A `RenderContext` provides scale, position, and theme info.

### Config: flat array with offset

```typescript
class Config<Q> {
    constructor(
        readonly cells: readonly Q[],
        readonly cellOffset: number,  // cells[0] is at position cellOffset
        readonly border: Q            // = embed(undefined), or delta(border,border,border) after steps
    ) {}
}
```

### Highlighting via `decomposeState` (future)

Not implementing the full provenance system yet. But the `renderState` on the CA is the first step — it means constructed CAs can render their sub-states and link to inner CA diagrams naturally.

### `addIdentity` — deferred

On-demand backward walk is sufficient for highlighting. `addIdentity` is a nice debugging tool but not essential for the visualization framework. Defer until needed.
