# Mazoyer's 6-state minimal-time FSSP — informal proof

This document describes Mazoyer's solution to the Firing Squad Synchronization Problem and explains why it works, in plain language with ASCII pictures. It is a companion to the Lean 4 port in [fssp_mazoyer/](fssp_mazoyer/) (which mirrors Jean Duprat's 1997 Coq formalization in [external/firing-squad/](../../../external/firing-squad/)). The full design plan is in [fssp_mazoyer_proof_plan.md](fssp_mazoyer_proof_plan.md).

---

## 1. The problem

A finite line of `n` identical finite-state cells, all in the *quiet* state `L` except cell 0 which is the *general* `G`. They evolve synchronously by a 3-cell local rule `δ`. The general's left neighbour and the rightmost cell's right neighbour are phantom `L`s and `G`s respectively (so the general is "anchored on a wall").

**Goal.** Find a constant-size automaton (independent of `n`) such that all `n` cells enter a special *fire* state `F` for the first time at exactly time `2n − 2`. This is the minimal possible time, because the signal must travel to the right end (`n − 1` steps) and back (`n − 1` steps).

Mazoyer (1986) gives a 6-state solution: `A`, `B`, `C`, `L`, `G`, `F`. We follow Duprat's (1997) Coq formalization of its correctness proof.

Space-time picture (time grows downward; columns `0..n−1` are real cells; the `[G]` at column `n` is the fixed right-phantom that the rightmost real cell always sees):

```
              col:  0   1   2  …  n−2  n−1     n
       t = 0       G   L   L  …   L    L    [G]      ← initial row
                    \                       /
                     \    "DD wedge"       /
                      \  side n−1         /  ← G-wall (right phantom)
                       \                 /
       t = 2n−3        G   G   G  …   G    [G]      ← all G, last quiet step
       t = 2n−2        F   F   F  …   F    [G]      ← FIRE
```

The rest of this document explains the structure inside that wedge.

---

## 2. Geometric language

Every claim in the proof is a statement about the value of a cell at some `(t, x)`. To make those manageable we pre-package them into 8 geometric figures, all defined pointwise over the global trace `Etat n t x : Couleur` (see [fssp_mazoyer/geom.lean](fssp_mazoyer/geom.lean)).

| Figure | Region | Used for |
|---|---|---|
| `Horizontale t x len P` | row of length `len + 1` | row hypotheses and conclusions |
| `Horizontale_t0 t x len P0 P` | row with distinguished head `P0` | the initial row `G : L^*` |
| `Horizontale_t1 t x len P0 P1 P` | row with distinguished head and second cell | the recursion seed `G : C : L^*` |
| `Verticale t x ht P` | column of height `ht + 1` | "G-wall" hypotheses |
| `Triangle_inf t x c P` | lower-right triangle filled with `P` | quiet-zone propagation |
| `Diag t x c P Q R` | iso-triangle of side `c`: apex `P`, interior `Q`, ground-vertex `R` | bricks (see §3) |
| `Diag' t x c P Q' Q R` | like `Diag`, with row `t+1` carrying `Q'` instead of `Q` | the `B`-brick top row is `G`, not `B` |
| `Semi_Diag t x c P Q` | `Diag` minus the ground vertex | strip-peeling |

A `Diag` looks like:

```
              x       x+c
       t                P            ← apex
       t+1            Q Q
       t+2          Q Q Q
                  Q Q Q Q
       t+c−1     Q Q Q Q Q
       t+c     R                     ← ground-left vertex
```

The constructors that *build* these figures are `Rec_Diag`, `Rec_Diag'`, `Rec_SemiDiag`: each takes four boundary δ-step rules and produces the full triangle. They are proved via `inter`, the only true 2-D induction in the proof. Everything above this layer is structural.

---

## 3. Atomic bricks `A_basic`, `B_basic`, `C_basic`

A *brick* of type `?` and side `c` is **two consecutive `Diag`s** stacked at times `t` and `t + 1`, both filled with state `?` and edged with `L` (see [fssp_mazoyer/basic_bricks.lean](fssp_mazoyer/basic_bricks.lean)). Pictorially (here `?` = `A`, side `c`):

```
                 col x     ...       x+c
       t          L  .  .  .  .  .   L           ← apex of upper Diag
       t+1        L  L  .  .  .  L   L           ← apex of lower Diag
       t+2          L A A A A A L
       t+3            L A A A L
       …                L A L
       t+c                L                       ← shared ground vertex
       t+c+1
```

`B_basic` is the same shape but with the very top single-cell row carrying `G` rather than `B`. This is exactly what `Diag'` exists for.

The two-row thickness is essential: `δ` looks at three cells, so to know what each cell becomes one step later, we need information about *two* consecutive rows of the same shape.

### Brick algebra

Six lemmas express how bricks succeed each other:

| Lemma | What it gives |
|---|---|
| `A_A`, `B_B`, `C_C` | brick of same type, two rows later, same anchor |
| `A_B` | `A` brick + 2 trailing `L`s ⇒ `B` brick (same side, anchor `+1`) |
| `B_C` | `B` brick + 2 trailing `L`s ⇒ `C` brick (same side, anchor `+1`) |
| `C_A` | `C` brick + 2 trailing `L`s ⇒ `A` brick of **side `+1`**, same anchor |

So the cycle `C → A → B → C` increases the side by 1 every three steps. The side-growing edge `C_A` is the *only* place a brick gains a column; this gives the construction its "scale 1/3" self-similarity (which we will see again in `DD`).

The proofs at this layer reduce to single-cell δ-evaluations packaged through a "calculus of diagonal superpositions" `DDD`, `DD_D'`, `DD_Ddollar`, … (see [fssp_mazoyer/constr.lean](fssp_mazoyer/constr.lean)).

### Apex helpers

The brick lemmas need ~8 single-step δ-facts about a `G` cell with various right neighbours: `GA_G`, `GB_G`, `GC_G`, `GA_dollarC`, `GBA_dollarC`, `GBG_dollarG`, `GBC_dollarB`, `GC_dollarB`. All are direct case checks on the transition table.

---

## 4. The left-edge staircase

The cell at column 0 has a phantom `L` to its left, so its dynamics are not symmetric with the bulk. We track it via five inductively-defined predicates `un_end ⊂ deux_end ⊂ trois_end ⊂ quatre_end ⊂ cinq_end` (see [fssp_mazoyer/border.lean](fssp_mazoyer/border.lean)):

```
un_end   t x  ::  G_t,x         ∧ G_(t+1),x
deux_end t x  ::  C_(t),(x+1)   ∧ B_(t+1),(x+1) ∧ un_end (t+1) x
trois_end t x ::  A_(t),(x+2)   ∧ G_(t+1),(x+2) ∧ deux_end (t+1) x
quatre_end t x :: L_(t),(x+3)   ∧ L_(t+1),(x+3) ∧ trois_end (t+1) x
cinq_end t x  ::  L_(t),(x+4)   ∧ L_(t+1),(x+4)
                 ∧ G_(t+1),(x+3) ∧ B_(t+2),(x+3) ∧ trois_end (t+2) x
```

Pictorially `cinq_end @ (t, 0)`:

```
       col:   0   1   2   3   4
       t:                       L                ← l4a
       t+1:               G     L                ← g3, l4b
       t+2:               B
                                                 (trois_end starts at t+2)
       t+2:           A
       t+3:           G
                                                 (deux_end starts at t+3)
       t+3:       C
       t+4:       B
                                                 (un_end starts at t+4)
       t+4:   G                                   ← always two G's at col 0
       t+5:   G
```

Each level adds exactly one diagonal column over the previous one. The key recursion driver is `cinq_quatre`: from a `cinq_end (t, x)` plus two trailing `L`s at column `x + 5`, we both
- **construct a brand-new `C_basic` of side 2** at `(t + 1, x + 3)`, and
- **continue with a `quatre_end (t + 3, x)`**.

This is exactly one synchronization step at the smallest scale — sub-problem solved, recursion continues two rows down.

The other propagation lemmas `un_deux`, `deux_trois`, `quatre_quatre`, `cinq_cinq`, `quatre_cinq`, … are direct corner-by-corner δ-evaluations.

---

## 5. The recursive wedge `DD`

**`DD t x cote`** (see [fssp_mazoyer/double_diag.lean](fssp_mazoyer/double_diag.lean)) is the central recursive object of the proof. Informally:

> "Starting at corner `(t, x)`, an entire triangular wedge of side `cote` synchronizes correctly: the cells at `(t + cote, x)` and `(t + cote + 1, x)` are both `G`, and below the brick at the upper right sits a smaller `DD`."

The constructors are:

- `DD_4 : quatre_end → DD (·) (·) 3` — base case (sub-problem of side 3).
- `DD_5 : cinq_end → DD (·) (·) 4` — base case (sub-problem of side 4).
- `DD_A`, `DD_B`, `DD_C`: recursive cases keyed on `cote mod 3`. Each says "there is an `A`/`B`/`C` brick of side `⌊cote/3⌋ + 1` somewhere on the upper right, and the wedge below it is itself a (smaller) `DD`".

Picture for the recursive case:

```
            col:    x                                       x + cote
       t                                                            .
                                                             .  .  /  ← apex of brick
                                                          .  .  /
                                  side `cote` wedge    .  .  /
                                                    .  .  /     ← brick: side ⌊cote/3⌋+1
                                                 .  .  /
       t+⌊cote/3⌋+1                       .  .  /                 (brick bottom-left)
                                       .       
                                    .          
                                 .         ← inner DD,
                              .                side ≈ 2·cote/3
                           .   inner DD
                        .
                     .
       t+cote     G                       
       t+cote+1   G  ←  produced by DD_GG (the inner DD's G's bubble up here)
```

The arithmetic works out exactly:

| `cote mod 3` | Brick type | Brick side | Time advance | Sub-side |
|---|---|---|---|---|
| 0 | `A` | `⌊cote/3⌋ + 1` | `⌊cote/3⌋ + 1` | `2·⌊cote/3⌋ − 1` |
| 1 | `B` | `⌊cote/3⌋ + 1` | `⌊cote/3⌋ + 1` | `2·⌊cote/3⌋` |
| 2 | `C` | `⌊cote/3⌋ + 1` | `⌊cote/3⌋ + 1` | `2·⌊cote/3⌋ + 1` |

In every case `(time advance) + (sub-side) = cote` exactly, so the inner wedge's bottom row coincides with the outer wedge's bottom row. This is why **`DD_GG`** holds: the inner `DD` produces two `G`s at `(t + cote, x)` and `(t + cote + 1, x)`, which are then the outer `DD`'s.

### Closure lemmas: `DD_hh` and `DD_hddollar`

Two more theorems make `DD` flexible enough for use:

- **`DD_hh`**: extending the right edge with two extra `L`s preserves `DD` (same side, time `+ 2`). Proved by induction on `DD`: base cases use `quatre_quatre`/`cinq_cinq`; recursive cases use `A_A`/`B_B`/`C_C` plus the IH.
- **`DD_hddollar`**: extending the right edge with two `L`s **at column `cote + 1`** rotates the brick type (A→B, B→C, C→A) and grows the side by 1. The C→A case must call `DD_hh` (not the IH) on the inner `DD` because the rotation re-shapes things differently. This is the *recursive-growth* lemma.

Both proofs are around 100 lines of arithmetic alignment in Lean.

---

## 6. From rows to wedges: `Ht1_DD`, `Ht1_VV`, `Ht0_DDf`

We still need to produce `DD`s from raw input rows. The translation layer is in [fssp_mazoyer/vertical.lean](fssp_mazoyer/vertical.lean).

**Key insight.** A row of the form `G : C : L : L : ... : L` (i.e. a `Horizontale_t1` with predicates `G_Etat, C_Etat, L_Etat`) is exactly the input shape of a sub-synchronization. From such a row of length `cote + 2` we get:

- **`Ht1_DD`**: for every `dx ≤ cote`, a wedge `DD (t + dx) x (dx + 3)`. Proof: induct on `dx`. Base case `dx = 0` is `DD_4` from `Ht1_End4` (the row's `G : C` head plus `L`s yields a `quatre_end`). Step is `DD_hddollar` driven by the next column of `L`s, which exist because an all-`L` row extends downward as a triangle (`Hor_tr_inf`, since `δ L L L = L`).
- **`Ht1_VV`**: a vertical `G`-column of height `2·cote + 1` directly under the row's leftmost `G`. Proof: each sub-`DD` of side `dx + 3` produces two `G`s at column `x` (by `DD_GG`); these stack up via `rec_vert`.

The initial-row analogue `Ht0_DDf` handles the `G : L : L : ... : L` row at `t = 0` (no `C` because the recursion seed has not appeared yet). After one CA step the row becomes `G : C : L : L : ...` (`δ G L L = C`), and we then reduce to `Ht1_*` analysis. The base-case bridge is `Ht0_End2` / `Ht0_End4` which compute `δ` directly on the initial corner.

---

## 7. Trapezoids: brick + G-wall ⇒ smaller wedge below

[fssp_mazoyer/trapeze.lean](fssp_mazoyer/trapeze.lean) provides the *induction step* of the apex theorem. For each of A/B/C, we have two lemmas: `_Vg` produces a new vertical `G`-wall on the **left** of the brick; `_DD` produces a new wedge **underneath** the brick.

Picture for the A-trapezoid (`Ha_Vg` and `Ha_DD`):

```
                col:  x                       x+c+1     x+c+2 ...
                                                         ┃
                     A-brick of side c+1                 ┃ right G-wall,
                            (size c+1)                   ┃ height triple c
                                                         ┃
       (t+c)+2:                                          ┃   ← brick bottom row
                  ┃                                      ┃
                  ┃                                      ┃
                  ┃ NEW G-wall (Ha_Vg)                   ┃   ← still G-wall
                  ┃ length 2c−1                          ┃
                  ┃                                      ┃
                  ┃                                      ┃
                  ┃     NEW DD wedge (Ha_DD), side c     ┃
                  ┃                                      ┃
       (t+2c):    G    ←━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛
```

The proof recipe is uniform across A/B/C:

1. The brick plus two `G`s on its right gives a "**ZCB**" wedge (a `Diag` of `G/C/G` stacked over a `Diag` of `G/B/G`) — this is the `A_ZCB`/`B_ZCB`/`C_ZCB` lemma in [fssp_mazoyer/reflection.lean](fssp_mazoyer/reflection.lean). The ZCB is the *reflection* of the original brick: an apex region surrounded by `G` instead of `L`.
2. **`ZCB_Ht1`**: the ZCB plus a sufficiently tall G-wall on its right produces a `G : C : L : ... : L` row at the bottom. This is the central translation between the brick world and the row world.
3. The new row plugs into `Ht1_VV` to give a vertical G-wall, and into `Ht1_DDf` to give a new wedge.
4. The new G-wall is concatenated (`vv_vert`) with the small G-wall sitting directly under the brick (from `A_Vg`/`B_Vg`/`C_Vg`).

The smallest cases (`Ha3_Hg`, `Hc2_Hg`, `H2_Hg`, …) are too small for the general construction and are discharged by direct δ-evaluation on a handful of cells.

---

## 8. The apex theorem `DD_Hg`

This is *the* theorem (see [fssp_mazoyer/sommet.lean](fssp_mazoyer/sommet.lean)):

> **`DD_Hg`**: A wedge `DD t x cote` plus a vertical `G`-wall of height `cote` immediately to its right produces a horizontal `G`-row of length `cote` at time `t + cote + 1`.

Picture:

```
              col:  x                           x+cote     x+cote+1
                                                                ┃
                            DD wedge,                           ┃ right G-wall,
                            side `cote`                         ┃ height `cote`
                                                                ┃
       t+cote+1:    G  G  G  G  G  G  G  G  G  G                ← all-G row
                          (Horizontale produced)
```

**Proof: strong induction on `cote`** (the only place strong induction is needed; the rest of the proof is structural induction on `DD`).

- *Base `cote = 3`* (`DD_4 ⇒ quatre_end`): unfold the staircase and walk through ~5 corner δ-evaluations to reach the `G G G` row.
- *Base `cote = 4`* (`DD_5 ⇒ cinq_end`): same idea with ~7 corners.
- *Step* (one of `DD_A`/`DD_B`/`DD_C`): use `Ha_Vg`/`Hb_Vg`/`Hc_Vg` to derive a *new* G-wall on the left of the brick, then call the IH on the (smaller) sub-`DD` underneath, then concatenate the resulting G-row with the cells under the brick (which are the first few cells of the all-G row, computed directly).

After `DD_Hg`, the very last step `Hg_Hf` closes the proof:

> **`Hg_Hf`**: A horizontal `G`-row of length `len + 1` plus a `G` at the cell immediately to its right yields a horizontal `F`-row of length `len + 1` one step later.

This is the **only** place the state `F` ever appears. It works because every cell now has at least one `G` neighbour, and:
- everywhere except column 0: `δ G G G = F`.
- at column 0: the phantom-`L` rule makes `δ L G G = F`.

So the whole row fires synchronously.

---

## 9. Final assembly

[fssp_mazoyer/final.lean](fssp_mazoyer/final.lean) chains everything:

```
base1        : t = 0 row is G : L^(n−2)                  -- given by initial config
diagonale    : DD n (n−3) 0 (n−1)                        ← Ht0_DDf base1
base2        : right-phantom row is G : C : L^(n−2)      -- given by initial config / phantom
vert_droite  : Verticale 1 n (2n−3) G                    ← Ht1_VV base2
sommet_1     : Horizontale (2n−3) 0 (n−1) G              ← DD_Hg diagonale (cropped vert_droite)
firing_squad : Horizontale (2n−2) 0 (n−1) F              ← Hg_Hf sommet_1 GN1
```

The full space-time picture:

```
              col:  0   1   2  …  n−2  n−1     n     n+1
       t=0        G   L   L  …   L    L     [G]    [C]      ← base1 ⊕ base2
                  \                                /
                   \                              /
                    \   "DD diagonale"           / vert_droite
                     \   side n−1              /  (G-wall on column n,
                      \                       /   from base2 via Ht1_VV)
                       \                     /
                        \                   /
       t=2n−3 (sommet_1):  G G G  …  G G G   [G]   −   −     ← all G
       t=2n−2 (fire):      F F F  …  F F F   [G]   −   −     ← FIRE
```

---

## 10. Why does this take exactly `2n − 2` steps?

The diagonal `DD (n−3) 0 (n−1)` extends from `t = n − 3` to `t = n − 3 + (n−1) = 2n − 4`. Adding the row beneath gives `2n − 3` (all-`G` row), and one more step from `Hg_Hf` gives `2n − 2` (all-`F` row).

The deeper reason is the case-by-case arithmetic of `DD`: each recursion level eats `⌊cote/3⌋ + 1` of time and produces a sub-wedge of side `2·⌊cote/3⌋ ± 1`. So:
- *time eaten* per level: `cote / 3`,
- *side reduced* per level: `cote / 3`.

After `O(log_{3/2} n)` levels we reach the base case, but the *total* time is the sum of "time eaten at every level" which is a geometric series summing to exactly `cote`. The choice of `2/3` as the contraction ratio is precisely what makes this sum match the diameter of the array — and it is the ultimate reason every minimal-time FSSP construction uses some variant of "1/3-mark" signalling.

---

## 11. Status of the Lean port

| File | Status | Comment |
|---|---|---|
| [geom.lean](fssp_mazoyer/geom.lean) | proved | Layer 1 — `Local_Prop`, figures, `Rec_Diag`, induction principles |
| [etat.lean](fssp_mazoyer/etat.lean) | proved | Per-state predicates; `un_pas`, `demi_pas`; initial row |
| [constr.lean](fssp_mazoyer/constr.lean) | all `sorry` | The `Pas_*` and `D??_???` combinators (mechanical, voluminous) |
| [basic_bricks.lean](fssp_mazoyer/basic_bricks.lean) | proved (modulo `constr`) | `A`/`B`/`C` brick lemmas and apex helpers |
| [border.lean](fssp_mazoyer/border.lean) | proved | All staircase lemmas, including `cinq_quatre` |
| [double_diag.lean](fssp_mazoyer/double_diag.lean) | proved | `DD_GG`, `DD_hh`, `DD_hddollar` — the recursive heart |
| [vertical.lean](fssp_mazoyer/vertical.lean) | proved | `Ht1_DD`, `Ht1_VV`, `Ht0_DDf` |
| [reflection.lean](fssp_mazoyer/reflection.lean) | all `sorry` | `B_UA`, `*_ZCB`, `ZCB_Ht1`, `*_Vg` |
| [trapeze.lean](fssp_mazoyer/trapeze.lean) | proved (modulo `reflection`) | All `H?_Vg`, `H?_DD`, plus `cote = 2, 3` base cases |
| [sommet.lean](fssp_mazoyer/sommet.lean) | all `sorry` | `quatre_Hg`, `cinq_Hg`, `DD_Hg`, `Hg_Hf` |
| [final.lean](fssp_mazoyer/final.lean) | proved (modulo `sommet`) | The 5-line glue is structurally complete |
| [bridge.lean](fssp_mazoyer/bridge.lean) | all `sorry` | `Etat`-level theorem to `SolvesFSSPOptimal`; also handles the no-firing-before direction |

The "spine" — `geom → etat → basic_bricks → border → double_diag → vertical → trapeze → final` — is structurally complete: every theorem is stated correctly and threaded through correctly. What remains is δ-table grunt work in three pockets:

1. **`constr.lean`** (~22 combinators): each one a small case-analytic δ-induction over a `Diag`/`Diag'`/`Semi_Diag`. No conceptual difficulty.
2. **`reflection.lean`** (~10 wedge lemmas): same flavour, plus the `recur_nSn` strip-peeling for `ZCB_lll`.
3. **`sommet.lean`** (one big strong induction `DD_Hg` + two base cases): this is the largest remaining proof.

Plus [bridge.lean](fssp_mazoyer/bridge.lean), which handles two non-Coq concerns: translating between `Etat` and the project's `cell n t x`, and proving the *no-firing-before* direction missing from Coq's `final.v`.

---

## References

- J. Mazoyer. *A six-state minimal time solution to the firing squad synchronization problem.* Theoretical Computer Science 50 (1986), 183–238. The original construction.
- J. Duprat. *Proof of correctness of the Mazoyer's solution of the firing squad synchronization problem in Coq.* July 1997. Source in [external/firing-squad/](../../../external/firing-squad/).
- E. F. Moore (1962). Original statement of the FSSP.
