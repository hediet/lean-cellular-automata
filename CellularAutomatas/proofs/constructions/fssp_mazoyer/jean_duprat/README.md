# Jean Duprat's Coq FSSP Proof — Lean 4 Port

This folder contains a Lean 4 port of Jean Duprat's Coq formalization of
the correctness of **Mazoyer's 6-state minimal-time Firing Squad
Synchronization Problem** solution.

**Original source:**
[rocq-archive/firing-squad](https://github.com/rocq-archive/firing-squad)
(commit `821676dce0353798b0651d058ffb22b65fb09097`), licensed under
LGPL 2.1.

## File mapping

| Coq file          | Lean file          | Notes |
|-------------------|--------------------|-------|
| `autom.v` (491 loc) + `algo.v` (222 loc) | `autom.lean` (196 loc) + `etat.lean` (127 loc) | `Couleur`, transition table `δ`, `init`, `Etat` in `autom.lean`; per-state predicates (`A_Etat`, `B_Etat`, …) in `etat.lean`. |
| `bib.v` (646 loc) + `geom.v` (436 loc) | `geom.lean` (586 loc) | `Local_Prop`, `loi`/`loi_droite`, figure predicates, induction principles. The two Coq files were merged; many `bib.v` helper theorems (`Rec3`, `Rec4`, …) are unnecessary in Lean and were dropped. |
| `constr.v` (684 loc) | `constr.lean` (1268 loc) | Diagonal-superposition combinators. The Lean version is larger because every `loi`/`loi_droite` hypothesis is explicit (Coq used implicit section variables) and all proofs are fully elaborated (no `sorry`). |
| `basic.v` (396 loc) | `basic_bricks.lean` (385 loc) | Brick lemmas `A_basic`, `B_basic`, `C_basic`. |
| `bord.v` (278 loc) | `border.lean` (352 loc) | Left-edge staircase predicates. |
| `double_diag.v` (241 loc) | `double_diag.lean` (418 loc) | Recursive `DD` predicate. |
| `vertical.v` (242 loc) | `vertical.lean` (307 loc) | Horizontal-to-`DD` and G-wall bridges. |
| `reflection.v` (493 loc) | `reflection.lean` (508 loc) | Wedge predicates `UA`, `UAB`, `ZCB`, and `*_Vg` walls. |
| `trapeze.v` (527 loc) | `trapeze.lean` (667 loc) | Trapezoid lemmas. |
| `sommet.v` (426 loc) | `sommet.lean` (567 loc) | Apex theorem `DD_Hg`, `Hg_Hf`. |
| `final.v` (145 loc) | `final.lean` (133 loc) | Final `firing_squad` theorem. |
| `extract.v` (26 loc) | — | OCaml extraction; not applicable. |
| **Total: 5253 loc** | **Total: 5514 loc** (jean\_duprat only) | |

## Files outside this folder

These files live in the parent `fssp_mazoyer/` directory and are **not**
part of the Coq port:

| File | Lines | Purpose |
|------|-------|---------|
| `defs.lean` | ~70 | Re-exports `autom.lean`; adds simulator (`all_fire`, `none_fire`, `row`) and `native_decide` tests. |
| `ca.lean` | ~200 | Lifts the 6-state CA into our `CellAutomaton α Bool` framework with a 7th `Border` state. |
| `bridge.lean` | 398 | Bridge from the `Etat`-style theorem to the `SolvesFSSPOptimal` spec. |
| `not_fire.lean` | 643 | "No firing before time 2n−2" invariants (the backward direction of `SolvesFSSPOptimal`, not covered by the original Coq proof). |

## Key differences between the Coq original and the Lean port

### Proof style
- **Coq** relies heavily on `intuition`, `auto`, `simpl`, `elim`,
  and Ltac-style proof scripts. Many goals are discharged by a single
  `intuition` or `auto with arith`.
- **Lean** uses `omega` for arithmetic, `simp`/`decide` for
  decidability, structured `calc` blocks for equality chains, and
  explicit `have`/`show` steps. Proofs tend to be more verbose but
  more readable.

### Section variables vs explicit arguments
- **Coq** uses `Section`/`Variable`/`Hypothesis` extensively: each
  file opens a section that declares `n : nat` and various `loi`
  hypotheses as implicit parameters.
- **Lean** passes everything explicitly via `variable (n : ℕ)` and
  function arguments. This makes `constr.lean` considerably longer
  than `constr.v`.

### Merged / split files
- Coq's `bib.v` (646 lines of generic combinators like `Rec3`, `Rec4`,
  `Rec5`, …) is mostly unnecessary in Lean — Lean's tactic mode and
  `omega` handle these patterns directly. The relevant parts were merged
  with `geom.v` into a single `geom.lean`.
- Coq's `autom.v` was split: core definitions went to the parent
  `fssp_mazoyer.lean`, state predicates to `etat.lean`.

### Integer handling
- **Coq** uses `Z` (binary integers) and lemmas from `ZArith`.
- **Lean** uses `ℤ` with `omega`, `push_cast`, and `ring` for
  arithmetic normalization. The `push_cast` tactic replaces many
  manual `Z.of_nat` / `Zabs_nat` manipulations.

### Inductive predicates vs structure-based figures
- The geometric figures (`Diag`, `Diag'`, `DD`, …) are encoded as
  Lean `structure`s with field accessors, rather than Coq `Inductive`
  propositions. Construction is via "builder" lemmas (`Rec_Diag`, etc.)
  that mirror the Coq inductive constructors.

### Overall size
The ported Lean files (5318 loc) are comparable in size to the Coq
originals (5253 loc). The additional bridge + not\_fire files (1041 loc)
represent new work not present in the Coq formalization.
