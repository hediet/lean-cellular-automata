# Refactoring Ideas

## 1. `DeadBorder`: Deduplicate `map_coord_prev` / `map_coord_next`

**File:** `CellularAutomatas/proofs/dead_border.lean`

`map_coord_prev` and `map_coord_next` are mirror images — 6 nearly identical cases each, ~60 lines apiece, differing only in direction (-1 vs +1, even↔odd swap). Similarly, `main_left` and `main_right` are mirrors.

**Idea:** Parameterize by direction:
```lean
def map_coord_step (dir : ℤ) -- dir = -1 or +1
```
One lemma, used twice. Cuts ~120 lines to ~60 and halves the correctness proof surface.

---

## 2. `SimFromΛ.after_trigger`: Factor counter-cycle pattern

**File:** `CellularAutomatas/proofs/sim_from_lambda.lean`

The `after_trigger` theorem has 8 explicit match branches `(t, k)` ∈ `{0, t+1} × {0, 1, 2}` plus a termination case. The branches for `k=1` and `k=2` are identical patterns (counter increment, same structure), just at different offsets.

**Idea:** Factor the "counter cycles 0→1→2" pattern into a separate lemma:
```lean
lemma counter_cycle (h_at_k0 : counter = 0 ∧ sim = some ...)
    (h_none_trigger : ...)
    (k : Fin 3) : counter_at_(+k) = k ∧ sim_at_(+k) = ...
```
Collapses 8 branches into 2 (base + inductive) times a 3-cycle lemma.

---

## 3. `CompressToDiag`: Unify g1/g2 extraction functions

**File:** `CellularAutomatas/proofs/compress_to_diag.lean`

`CAgfSpeedup` defines `g1` and `g2` as extraction functions that pattern-match on `BetaUnionSq` to recover trace values. The proofs (`g1_spec`, `g2_spec`) repeat the same chain: unfold `C` → `step3.spec` → `step2.spec` → `step1.spec` → `cast`/`ring_nf`/`grind`.

**Idea:** Define a single extraction function parameterized by `Fin 3`, with one spec lemma covering all three components. The repeated `cast $ e.step2.C_orig = e.step1.C` pattern suggests a missing definitional equality or `@[simp]` lemma.

---

## 5. `LeftIndepSpeedupQuiescent.spec_nextt`: Deduplicate inner induction

**File:** `CellularAutomatas/proofs/left_indep_speedup.lean`

The proof uses outer induction on `t` with inner descending induction on `j`. The base case (`j = k-1`) and step case (`j < k-1`) share the same pattern: apply `fold_last`/`fold_step`, rewrite with IH, use `phi`/`psi` algebraic lemmas, then `nextt_succ` + `h_left_indep`. The `phi_toNat_succ` computation is duplicated.

**Idea:** Factor the shared "given fold equals nextt at j+1, show it equals nextt at j" pattern into a helper lemma.

---

## 6. `QuiescentBorderLeftIndep.spec_internal`: Reduce case explosion

**File:** `CellularAutomatas/proofs/quiescent_border.lean`

The inductive step has deeply nested case splits on whether `i-1, i, i+1` are in the cone, producing ~8 branches. Many share the pattern: rewrite with IH, unfold `δ'`, apply `h_left_indep`.

**Idea:** Extract the repeated "rewrite IH, unfold δ', apply left_indep" pattern into a helper lemma for cone boundary transitions.

---

## 7. Refactor `rt_closed`/`weak_rt_closed` to use `Σ` instead of `∃`

**Files:** `CellularAutomatas/defs.lean`, `CellularAutomatas/proofs/ca_rt_utils.lean`, `CellularAutomatas/proofs/lx_rt_implies_rt.lean`

Currently `weak_rt_closed` is `ℒ (CA_rt (α × Γ) + f) = ℒ (CA_rt α)`, a `Prop`-level set equality. Extracting a witness CA from it requires `Classical.choice`. But proofs of rt-closedness (e.g., `two_stage_is_rt_closed`) already construct the witnessing CA explicitly — the existential wrapper discards that data.

**Idea:** Redefine as:
```lean
def Advice.weak_rt_closed (f: Advice α Γ) :=
    ∀ (C : CA_rt (α × Γ)), Σ (C' : CA_rt α), C'.val.L = (C.val + f).L
```
This makes the definition `Type`-valued, so downstream code can pattern-match on the witness directly without choice. The reverse inclusion `ℒ (CA_rt α) ⊆ ℒ (CA_rt (α × Γ) + f)` already holds for any advice (`CA_rt_subseteq_CA_rt_with_advice`), so only the interesting direction is needed. Nonconstructive proofs of rt-closedness can still use `Classical.indefiniteDescription` to lift `∃` into `Σ`.

---

## 7. Factor generic `state_track` lemma

**Files:** `sim_from_lambda.lean`, `decompress_triple.lean`, `compress_to_diag.lean`

The pattern "the first component of the constructed CA's state tracks the original CA's state" appears identically in:
- `SimFromΛ.state_track`
- `DecompressTriple.state_track`
- Implicitly in `CompressToDiag.C_self_tracks_speedup`

**Idea:** A generic lemma: "if a CA's δ always computes the same first projection as another CA's δ, then nextt's first projection tracks the other CA's nextt." One-line application instead of copy-pasted induction proofs.

---

## Priority

| Refactoring | Lines saved | Impact |
|---|---|---|
| 1. `DeadBorder` direction param | ~80 | Halves duplicated correctness proof |
| 7. Generic `state_track` | ~40 | Eliminates 3 duplicated proofs |
| 3. Unify g1/g2 extraction | ~60 | Single parameterized spec |
| 2. Factor counter-cycle | ~50 | 8 → 3 branches |
| 4–6 | ~30 each | Readability + maintainability |
