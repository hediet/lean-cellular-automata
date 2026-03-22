# Left-Independent OCA Speedup — ASCII Diagram

## Current theorem: `result_left_indep_speedup`

### Naming convention

Each position gets a fixed letter. Subscript = time (omitted for t=0).
  Negative positions (right-to-left):
    -1→α  -2→β  -3→γ  -4→δ  -5→ε  -6→ζ  -7→η  -8→θ  -9→ι  -10→κ 
  Non-negative positions:
    0→a   1→b   2→c   3→d

So `γ₃` = position -3 at time 3.  `a` = position 0 at time 0.  `a₂` = position 0 at time 2.

### ORIGINAL left-independent OCA (k=2 compression)

Info flow: (p+1,t−1) → (p,t)   [the local rule δ ignores left neighbor]

```
   Pos  -10  -9  -8  -7  -6  -5  -4  -3  -2  -1   0   1   2   3

  t=0 :   κ   ι   θ   η   ζ   ε   δ   γ   β   α   a   b   c   d
  t=1 :   κ₁  ι₁  θ₁  η₁  ζ₁  ε₁  δ₁  γ₁  β₁  α₁  a₁  b₁  c₁  d₁
  t=2 :   κ₂  ι₂  θ₂  η₂  ζ₂  ε₂  δ₂  γ₂  β₂  α₂  a₂  ·   ·   ·
  t=3 :   κ₃  ι₃  θ₃  η₃  ζ₃  ε₃  δ₃  γ₃  β₃  α₃  ·   ·   ·   ·
  t=4 :   κ₄  ι₄  θ₄  η₄  ζ₄  ε₄  δ₄  γ₄  β₄  α₄  ·   ·   ·   ·
  t=5 :   κ₅  ι₅  θ₅  η₅  ζ₅  ε₅  δ₅  γ₅  β₅  α₅  ·   ·   ·   ·
  t=6 :   κ₆  ι₆  θ₆  η₆  ζ₆  ε₆  δ₆  γ₆  β₆  α₆  ·   ·   ·   ·
```

Main ╲ diagonal (each cell depends only on its upper-right neighbor):
  a ──╲──→ α₁ ──╲──→ β₂ ──╲──→ γ₃ ──╲──→ δ₄ ──╲──→ ε₅ ──╲──→ ζ₆ ──╲──→ ...

### COMPRESSED OCA (each left cell stores a k-tuple)

```
  Position  i'=-5        i'=-4        i'=-3        i'=-2        i'=-1          0   1   2   3

  t'=0 :   [κ,ι]        [θ,η]        [ζ,ε]        [δ,γ]        [β,α]          a   b   c   d
  t'=1 :  [κ₂,ι₂]      [θ₂,η₂]      [ζ₂,ε₂]      [δ₂,γ₂]      (β₂,α₁)       a₁  ·   ·   ·
  t'=2 :  [κ₄,ι₄]      [θ₄,η₄]      [ζ₄,ε₄]      (δ₄,γ₃)      (β₃,α₂)       a₂  ·   ·   ·
  t'=3 :  [κ₆,ι₆]      [θ₆,η₆]      (ζ₆,ε₅)      (δ₅,γ₄)      (β₄,α₃)        ·   ·   ·   ·
  t'=4 :  [κ₈,ι₈]      (θ₈,η₇)      (ζ₇,ε₆)      (δ₆,γ₅)      (β₅,α₄)        ·   ·   ·   ·
  t'=5 :  (κ₁₀,ι₉)     (θ₉,η₈)      (ζ₈,ε₇)      (δ₇,γ₆)      (β₆,α₅)        ·   ·   ·   ·
```

  [.,.]  = spatial mode (outside light cone): both components at same orig time k·t'
  (.,.)  = diagonal mode (inside light cone): components staggered by 1 orig step

### COORDINATE MAPPING: compressed (i', t', j) → original (p, τ)

```
  p = k·i' + j          (spatial decompression)
  τ = t' − (k−1)·i' − j (temporal decompression)
    = t' − i' − j       (for k=2)
```

Constraints: i' < 0,  −t' ≤ i',  j ∈ {0,…,k−1}

Example (i'=-1, t'=1):
  j=0 → p=-2, τ=1+1-0=2  →  β₂
  j=1 → p=-1, τ=1+1-1=1  →  α₁

Example (i'=-2, t'=2):
  j=0 → p=-4, τ=2+2-0=4  →  δ₄
  j=1 → p=-3, τ=2+2-1=3  →  γ₃

Example (i'=-3, t'=3):
  j=0 → p=-6, τ=3+3-0=6  →  ζ₆
  j=1 → p=-5, τ=3+3-1=5  →  ε₅

Example outside light cone (i'=-3, t'=1):
  both at τ=k·t'=2  →  [ζ₂,ε₂]

### Key Insight

Since the local rule ignores the left neighbor, each cell on a ╲ diagonal depends
only on the cell above-right, so k=2 consecutive diagonal cells can be computed in
one compressed step. The compressed CA groups original positions {2·i', 2·i'+1}
and simulates their diagonals in lockstep.

### Generalized theorem (config-level, no border assumption)

The current theorem is tied to words (and hence quiescent `#` border). But the
compressed diagram shows the construction doesn't need that: the `[.,.]` cells
outside the light cone are computed purely from their own initial k-compressed data.
No border quiescence needed — just a properly compressed initial configuration.

**Two compression regimes (for `i < 0`):**

There are two qualitatively different types of compressed cells, depending on whether
info from the right (i ≥ 0) has reached position i' yet:

**Case 1: Inside light cone (`t' ≥ -i'`)** — diagonal shift  `(.,.)` cells
  Each component `j` is at a *different* original time:
    `(C'.nextt c' t' i')[j]  =  C.nextt c (t' − (k−1)·i' − j) (k·i' + j)`

  Example (i'=-1, t'=1, k=2):  (β₂, α₁)  — times 2 and 1, staggered by 1

**Case 2: Outside light cone (`t' < -i'`)** — purely spatial  `[.,.]` cells
  All components are at the *same* original time:
    `(C'.nextt c' t' i')[j]  =  C.nextt c (k·t') (k·i' + j)`

  Example (i'=-2, t'=1, k=2):  [δ₂, γ₂]  — both at time 2 = k·t'

**The transition:** At `t' = -i'`, the cell switches from purely spatial to
  diagonal. This is when the first non-self info arrives from the right.

```
  Regime diagram (k=2):

               i'=-4     i'=-3     i'=-2     i'=-1
  t' = 0 :   [spat]    [spat]    [spat]    [spat]     ← all purely spatial
  t' = 1 :   [spat]    [spat]    [spat]    (diag)     ← i'=-1 switches
  t' = 2 :   [spat]    [spat]    (diag)    (diag)     ← i'=-2 switches
  t' = 3 :   [spat]    (diag)    (diag)    (diag)     ← i'=-3 switches
  t' = 4 :   (diag)    (diag)    (diag)    (diag)     ← i'=-4 switches
```

---

## Construction

### State space Q'

```lean
inductive Q' where
  | single (q : Q)                -- uncompressed cell (i ≥ 0)
  | spatial (w : Fin k → Q)       -- compressed, all at same orig time
  | diagonal (w : Fin k → Q)      -- compressed, staggered orig times
```

Three variants because the transition function differs:
- `diagonal` uses the existing `fold` (chain δ₂ right-to-left)
- `spatial` needs a full k-step triangle simulation
- The two give different results on the same input data

### Initial configuration

```lean
def compress (c : Config Q) : Config Q' :=
  fun i => if i ≥ 0 then Q'.single (c i)
           else Q'.spatial (fun j => c (k * i + j))
```

All negative cells start as `spatial` (all components at orig time 0).

### Transition δ' (left-independent: ignores left neighbor)

```lean
def δ' (_ b c : Q') : Q' :=
  match b, c with
  -- Single cells evolve normally
  | single q_b, _ => single (δ₂ q_b (asQ c))

  -- Diagonal stays diagonal (existing construction)
  | diagonal w_b, _ => diagonal (fold_diag w_b (asQ c))

  -- Spatial + spatial → spatial (full k-step simulation)
  | spatial w_b, spatial w_c => spatial (fold_spatial w_b w_c)

  -- Spatial + diagonal/single → diagonal (the switch!)
  | spatial w_b, _ => diagonal (fold_switch w_b (asQ c))
```

### The three fold functions (for k=2)

**fold_diag** (existing): chain from right, staggered times
  Given center=(a,b), q=asQ(right):
```
  result[1] = δ₂(b, q)           -- b and q at same orig time
  result[0] = δ₂(a, result[1])   -- a and result[1] at same orig time
```

**fold_spatial**: full k-step triangle, uniform times
  Given center=(a₀,a₁), right=(a₂,r₀):
```
  -- Level 0 (time T):    a₀, a₁, a₂, r₀
  -- Level 1 (time T+1):  δ₂(a₀,a₁), δ₂(a₁,a₂), δ₂(a₂,r₀)
  -- Level 2 (time T+2):  δ₂(L1[0],L1[1]), δ₂(L1[1],L1[2])
  result[0] = δ₂(δ₂(a₀,a₁), δ₂(a₁,a₂))
  result[1] = δ₂(δ₂(a₁,a₂), δ₂(a₂,r₀))
```
  Note: uses the FULL right tuple, not just asQ(right).

**fold_switch**: spatial → diagonal transition
  Given center=(a,b), q=asQ(right) where center at time T, q at time T:
```
  result[1] = δ₂(b, q)                     -- 1 step:  T → T+1
  result[0] = δ₂(δ₂(a, b), result[1])      -- 2 steps: T → T+2
```
  Component j advances by (k−j) steps. For k=2: comp 0 advances 2, comp 1 advances 1.

### Why fold_diag ≠ fold_switch

For k=2, center=(a,b), q:
  fold_diag:   (δ₂(a, δ₂(b,q)),  δ₂(b,q))     ← a is already 1 step ahead of b
  fold_switch: (δ₂(δ₂(a,b), δ₂(b,q)),  δ₂(b,q))  ← a must be advanced first

The difference is in component 0:  δ₂(a, ...) vs δ₂(δ₂(a,b), ...).
In diagonal mode, a is already at time T (one step ahead of b at T-1).
In spatial mode, a is at time T (same as b), so it needs δ₂(a,b) to catch up first.

---

## Invariants (induction hypothesis)

For `i < 0`, at compressed time `t'`:

```
  Inv(t', i') :=
    if t' < -i'  then  nextt(c', t', i') = spatial(j ↦ nextt(c, k·t', k·i'+j))
    if t' ≥ -i'  then  nextt(c', t', i') = diagonal(j ↦ nextt(c, t'-(k-1)·i'-j, k·i'+j))
```

For `i ≥ 0`:
```
  nextt(c', t', i') = single(nextt(c, t', i'))
```

### Proof obligations

The proof is by induction on t'. For each transition type, we show the invariant
is preserved:

**1. spatial + spatial → spatial**  (center at i', t' < -i'-1)
  - Right at i'+1, t' is spatial (since t' < -i'-1 implies t' < -(i'+1))
  - By inv: center = spatial(j ↦ nextt(c, kT, ki'+j))
            right = spatial(j ↦ nextt(c, kT, k(i'+1)+j))
  - fold_spatial simulates k original steps
  - Result = spatial(j ↦ nextt(c, kT+k, ki'+j)) = spatial(j ↦ nextt(c, k(T+1), ki'+j)) ✓

**2. spatial + diagonal → diagonal**  (center at i', t' = -i'-1)
  - Right at i'+1 just became diagonal at t' = -(i'+1) = -i'-1
  - By inv: center = spatial(j ↦ nextt(c, kT, ki'+j))  with T = t'
            right[0] = nextt(c, t'-(k-1)(i'+1), k(i'+1)) at time T
  - asQ(right) = right[0] at same orig time T as center — fold_switch applies
  - fold_switch advances comp j by (k-j) steps from T
  - Result = diagonal(j ↦ nextt(c, T+k-j, ki'+j))
           = diagonal(j ↦ nextt(c, (t'+1)-(k-1)i'-j, ki'+j)) ✓

**3. spatial + single → diagonal**  (center at i'=-1, t'=0)
  - Right = single(c(0)) ⇒ asQ = c(0) at time 0 = same as center
  - Exactly the same as case 2

**4. diagonal + diagonal → diagonal**  (center at i', t' ≥ -i')
  - Existing proof (fold_diag preserves diagonal invariant)

**5. diagonal + single → diagonal**  (center at i'=-1, t' ≥ 1)
  - Existing proof

---

## Lean theorem statement

```lean
theorem result_left_indep_speedup_config
    (C : CellAutomaton Q) (k : ℕ) (hk : k ≥ 2)
    (h_left_indep : C.left_independent)
    (c : Config C.Q) (t : ℕ) (i : ℤ) (hi : i < 0) (j : Fin k) :
    let e := LeftIndepSpeedupConfig.mk C k hk h_left_indep
    (e.C'.comp (e.compress c) t i) j =
    C.comp c (e.τ t i j) (k * i + j)
  where
    τ t i j := if t ≥ -i then (t - (k-1) * i - j).toNat
                         else k * t
```

**Differences from current `result_left_indep_speedup`:**
1. Works with `Config Q`, not `Word α` — no word-to-config embedding
2. No quiescent border assumption
3. No light-cone constraint — holds for ALL `i < 0`
4. Piecewise τ function captures both regimes
5. State space has 3 constructors instead of 2

---

## Handoff context for continuing AI

### File locations

- **This design doc**: `.scratch/left-indep-speedup-diagram.md`
- **New Lean file (WIP)**: `CellularAutomatas/proofs/constructions/speedup_left_independent_config.lean`
- **Existing diagonal speedup**: `CellularAutomatas/proofs/constructions/speedup_left_independent.lean`
- **Existing spatial compression**: `CellularAutomatas/proofs/constructions/speedup_compressed.lean`
- **Core definitions** (CellAutomaton, Config, nextt, comp, left_independent): `CellularAutomatas/defs.lean`

### Current state of the Lean file

The file builds successfully with `sorry`s. What's defined:

| Item | Status | Notes |
|------|--------|-------|
| `LeftIndepSpeedupConfig` structure | ✅ | Stores Q, δ, k, hk, h_left_indep |
| `Q'` (single/spatial/diagonal) | ✅ | With Fintype, Alphabet instances |
| `δ₂`, `asQ` | ✅ | With simp lemmas |
| `foldDiagAux`/`foldDiag` | ✅ def, `sorry` lemmas | Same as existing `foldAux`/`fold` |
| `stepWindow` | ✅ | Simulates one δ₂ step on a window |
| `foldSpatialAux`/`foldSpatial` | ✅ def | Chains `stepWindow` k times on 2k window |
| `foldSwitch` | `sorry` def | Hardest piece — triangle yielding staggered output |
| `δ'` | ✅ | Pattern-matches (b,c) with 4 cases |
| `compress` | ✅ | Spatial for i<0, single for i≥0 |
| `ψ`, `τ` | ✅ | Position/time mappings |
| `C'`, `C_orig` | ✅ | The compressed and original CAs |
| `spec_nonneg` | `sorry` | Single cells track original |
| `spec_spatial` | `sorry` | Spatial regime invariant |
| `spec_diagonal` | `sorry` | Diagonal regime invariant |
| `spec` | `sorry` | Main combined theorem |

### What needs to be done (in priority order)

**1. Define `foldSwitch` properly** (currently `sorry`).
   The challenge: component j must be at row (k-j) of a triangle on k+1 cells.
   For k=2: result = (δ₂(δ₂(a,b), δ₂(b,q)), δ₂(b,q)).
   This is NOT the same shape as `foldSpatialAux` (which gives 1 row of the triangle,
   not a diagonal slice). Need a recursive def that extracts the right diagonal of the triangle.
   Possible approach: define it recursively on j descending, where:
     result[k-1] = δ₂(w[k-1], q)
     result[j] = δ₂(stepWindow(w++[q])[j], result[j+1])
   Or just define it by iterating: build the full triangle row by row, extract the diagonal.

**2. Prove `spec_nonneg`** (single cells track original).
   Induction on t. At t=0, compress gives `single(c(i))`. For the step:
   - Left: could be single or diagonal (i-1 could be ≥ 0 or < 0)
   - Center: single (by IH)
   - Right: single (by IH, since i+1 > i ≥ 0)
   - δ'(_, single q_b, single q_c) = single(δ₂(q_b, q_c)) = single(δ(_, q_b, q_c))
   Key subtlety: need `asQ(single q) = q` and left-independence.
   Also need: for `i = 0`, left neighbor at `i-1 = -1` is spatial/diagonal, but
   `δ'` ignores left, so it doesn't matter.

**3. Prove `spec_spatial`** (spatial regime).
   Induction on t. Needs `foldSpatial` correctness lemma:
   "foldSpatial(center, right) = k original steps on the concatenated window"
   This is the triangle simulation. The window has:
     center = (nextt c (k*t) (k*i+j))_{j=0..k-1}
     right  = (nextt c (k*t) (k*(i+1)+j))_{j=0..k-1}
   After k steps of δ₂, the result should be:
     (nextt c (k*(t+1)) (k*i+j))_{j=0..k-1}
   Proving this requires showing that k δ₂-steps on a 2k window equals k nextt steps
   at the corresponding positions. This is the key new lemma.

**4. Prove the switch case in `spec_diagonal`** for `t = -i` (first diagonal step).
   Uses `foldSwitch` correctness + timing synchronization.

**5. Prove steady-state `spec_diagonal`** for `t > -i`.
   Can adapt existing proof from `LeftIndepSpeedupQuiescent.spec_nextt`.

### Key insight for proofs

The existing file `speedup_left_independent.lean` has the full infrastructure for the
diagonal regime (fold_step, fold_last, the inner induction on j). The main gap is:
- `foldSpatial` correctness (triangle simulation)
- `foldSwitch` definition and correctness (one-shot transition)
- Gluing via the outer induction with case split on `t < -i` vs `t ≥ -i`

### Existing infrastructure you can reuse (by analogy, not direct import)

From `LeftIndepSpeedupQuiescent`:
- `foldAux_step` / `fold_step`: pattern for proving fold[j] = δ₂(w[j], fold[j+1])
- `foldAux_last` / `fold_last`: pattern for proving fold[k-1] = δ₂(w[k-1], q)
- `spec_nextt` proof structure: outer induction on t, inner descending induction on j
- `psi_succ_zero_eq`, `phi_*` lemmas: position/time mapping algebra

From `SpeedupKx` (in `speedup_compressed.lean`):
- `compression_k_step`: shows nextt(k) on compress = compress∘nextt(k) — analogous to
  what `foldSpatial` needs to prove, but for a general (3-neighbor) CA, not δ₂-only

### Build command

```bash
lake build ./CellularAutomatas/proofs/constructions/speedup_left_independent_config.lean
```
