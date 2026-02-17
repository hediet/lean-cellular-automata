# Refactoring Plan

Each step is a self-contained unit of work. After each step:
1. Run `lake build ./CellularAutomatas/results.lean 2>&1 | head -80` to verify the build.
2. If it builds, commit with a descriptive message.
3. If it doesn't build, fix the errors before committing.

**Rule**: Never move definitions into `defs.lean`. Use `CellularAutomatas/internal_defs.lean` for shared internal definitions that don't belong in `defs.lean` but are needed across multiple proof files.

---

## Step 1: Replace `zip_words` with `List.zip`

`zip_words` is defined as `List.zipWith (·,·)`, which is exactly `List.zip`.
Replace `zip_words` with `List.zip` and keep the `⨂` notation pointing to `List.zip`.

### Changes
- In `CellularAutomatas/defs.lean`:
  - Delete `def zip_words` and the `@[app_unexpander zip_words]`.
  - Change `infixl:65 " ⨂ " => zip_words` to `infixl:65 " ⨂ " => List.zip`.
  - Keep the unexpander or adjust it for `List.zip`.
- In `CellularAutomatas/proofs/basic.lean`:
  - Update `zip_length` to use `List.zip` (should get simpler, possibly replaceable by Mathlib lemma `List.length_zip`).
  - Update `Word.zip_fst`, `Word.zip_snd` — these restate `List.unzip_zip_left/right` or similar.
  - Check if `zip_left_empty`, `zip_right_empty`, `zip_empty_iff` (in `two_stage_is_rt_closed.lean`) become trivial / removable.
- In `CellularAutomatas/proofs/basic.lean` line ~603: `rw [<-List.zip]` was used to convert `zip_words` to `List.zip` — this rewrite becomes unnecessary.
- Grep for all uses of `zip_words` and `⨂` (on Word types) to verify nothing breaks.

**Note**: The `⨂` notation is overloaded for `ca_zip`, `M_prod`, and `zip_two_stage` too — those are on different types and are unaffected.

**Build command**: `lake build ./CellularAutomatas/results.lean 2>&1 | head -80`

---

## Step 2: Remove duplicate `map_project` lemmas in `basic.lean`

`map_project_comp` (line ~471) is a duplicate of `comp_of_map_project` (line ~113).
`map_project_trace_rt` (line ~475) is a duplicate of `trace_rt_of_map_project` (line ~125).

### Changes
- In `CellularAutomatas/proofs/basic.lean`: Delete `map_project_comp` and `map_project_trace_rt`.
- Grep for uses of `map_project_comp` and `map_project_trace_rt` in other files — rewrite to use `comp_of_map_project` / `trace_rt_of_map_project`.

**Known callers** (from my reading):
- `compress_to_diag.lean` has its own `map_project_comp2` that calls into the word variant — check if it references the deleted names.

---

## Step 3: Remove duplicate `is_two_stage_of_rt_closed_and_prefix_stable.lean`

The file `is_two_stage_of_rt_closed_and_prefix_stable.lean` is nearly identical to `is_two_stage_of_rt_closed_and_causal.lean`. The only difference is `adv.causal` vs `adv.prefix_stable`.

### Investigation first
- Check if `Advice.prefix_stable` is actually defined anywhere in defs.lean. (From my reading, it is NOT defined — only `Advice.causal` exists.)
- If `prefix_stable` is undefined, the file doesn't compile anyway. **Delete it.**
- If it IS defined (perhaps via `IsCausal` which is the same concept), merge the two files.

### Changes
- Delete `CellularAutomatas/proofs/is_two_stage_of_rt_closed_and_prefix_stable.lean`.
- Remove its import from any file that imports it (check `all.lean`, `results.lean`).
- Verify the shared definitions (`L_c`, `CA_adv_L_c`, `CA_L_c`, etc.) only exist in the causal version.

---

## Step 4: Replace Mathlib-available lemmas

### `prop_of_elem_prop_set`
This is `Set.mem_setOf_eq` or `Iff.rfl`. Delete and replace callers.

Callers (from reading):
- `is_two_stage_of_rt_closed_and_causal.lean` (multiple)
- `two_stage_is_rt_closed.lean` (multiple)
- `middle_not_two_stage.lean`

### `subset_iff`
This is `Set.subset_def`. Delete and replace callers.

Caller: `two_stage_is_rt_closed.lean`

### `list_map_congr`
Already `private` — check if `List.map_congr_left` (or similar Mathlib lemma) can replace it. If so, delete.

Caller: `basic.lean` (used in `scan_temporal_independence`)

---

## Step 5: Rename `ca_id` to `ca_trace_id`

`ca_id` has `δ := fun _ _ r => r` — it shifts the configuration right by 1 each step, so `nextt c t p = c (p + t)`. Its key property is that `trace = config_to_trace`, i.e. it's the identity for the *trace* at position 0.

`CellAutomaton.idCA` has `δ := fun _ c _ => c` — true identity on configurations. `nextt c t p = c p`.

**These are fundamentally different.** Both must be kept.

### Changes
- Rename `ca_id` → `ca_trace_id` in `basic.lean` and all callers.
- Rename `ca_id_word` → `ca_trace_id_word`.
- Rename `ca_id_trace_eq` → `ca_trace_id_trace_eq`.
- Rename `ca_id_scan_temporal` → `ca_trace_id_scan_temporal`.

Callers: `basic.lean`, `two_stage_is_rt_closed.lean`, `is_two_stage_of_rt_closed_and_causal.lean`.

---

## Step 6: Move misplaced general definitions out of `two_stage_is_rt_closed.lean`

This file contains many general utilities that other files depend on. Move them to appropriate locations.

### Move to `CellularAutomatas/proofs/ca_rt_utils.lean` (new file):
- `c_count_until` + specs
- `word_to_config_empty`
- `embed_word_p_not_in_range`, `embed_word_p_in_range`, `embed_word_p_eq`
- `c_is_border` + specs
- `fix_empty` + `fix_empty_spec`
- `subset_iff` (if not deleted in Step 4)
- `advice_rt_closed_iff`
- `tCellAutomatonWithAdvice.L_mem_ℒ`
- `tCellAutomatonWithAdvice.exists_CA_rt_of_rt_closed`
- `tCellAutomatonWithAdvice.elem_L_iff`
- `ca_to_two_stage` + spec
- `zip_two_stage` + spec
- `TwoStageAdvice.L`, `.to_CA_rt`, `.from_CA_rt` + specs
- `zip_left_empty`, `zip_right_empty`, `zip_empty_iff`

### Update imports
- `two_stage_is_rt_closed.lean` imports `ca_rt_utils.lean` and keeps only `two_stage_rt_closed`.
- Other files that imported `two_stage_is_rt_closed.lean` just for utilities now import `ca_rt_utils.lean`.

**This is the riskiest step** — many import chains. Build-test carefully.

---

## Step 7: Move border-related general lemmas to `CellularAutomatas/proofs/border.lean`

### Move from `dead_border.lean`:
- `dead_border_prop`
- `initial_border_prop`
- `to_word_exists_generic`

### Move from `k_step_speedup.lean`:
- `dead_implies_left_dead`
- `left_dead_border_left`

### Move from `basic.lean`:
- `CellAutomaton.border_stays_right`

### Update imports
- `dead_border.lean` imports `border.lean`
- `k_step_speedup.lean` imports `border.lean`
- `quiescent_border.lean` imports `border.lean` (for `border_stays_right` if needed)

---

## Step 8: Split `basic.lean` into focused files

`basic.lean` is ~600 lines covering unrelated topics. Split into:

### `CellularAutomatas/proofs/nextt_lemmas.lean`
- `nextt_congr` (or delete if `nextt_locality` suffices)
- `nextt_shift`
- `nextt_locality`
- `nextt_add`
- `nextt0`, `nextt1` — consider deleting if `nextt_zero`/`nextt_succ` from defs.lean suffice
- `LCellAutomaton.nextt_succ_eq` — consider deleting (duplicate of `nextt_succ`)

### `CellularAutomatas/proofs/embed_lemmas.lean`
- `embed_word_at_eq`, `_at_eq1`, `_at_eq2`
- `project_config_at`
- `comp_word_eq_project_nextt`, `comp_config_eq_project_nextt`
- `Word.get'_eq`
- `word_to_config_natcast_eq`
- Temporal independence lemmas (`scan_temporal_independence_at_0`, `scan_temporal_independence`, `CArtTransducer.scan_temporal_independence`)

### `CellularAutomatas/proofs/product_ca.lean`
- `ProdCA` + all lemmas
- `ca_zip` + all lemmas

### `CellularAutomatas/proofs/word_ops.lean`
- `Word.fst`, `Word.snd` + all 12+ lemmas
- `adv_empty`, `adv_empty_2`, `adv_cannot_empty_2`
- `advice_eq_iff`
- `zip_length` (if not removed in Step 1)

### `CellularAutomatas/proofs/flip.lean`
- `Config.flip` + all lemmas
- `CellAutomaton.flip` + all lemmas
- `config_to_trace`

### `CellularAutomatas/proofs/ca_rt_lemmas.lean`
- `toRtCa` + spec
- `CA_rt_t`, `CA_rt_p`
- `CA_rt_L_iff`, `CA_rt_L_iff2`
- `trace_rt_length`, `trace_rt_empty`, `trace_rt_neq_empty`
- `trace_L`, `trace_rt_L`, `trace_rt_getElem_i_iff`, `_iff2`
- `elemL_iff_trace_rt`
- `tCellAutomaton.elem_L_iff`
- `ℒ_CA_rt_iff`, `ℒ_oca_def`
- `CA_rt_subseteq_CA_rt_with_advice`, `CArtWithAdvice_eq_CArt_iff`
- `tCellAutomaton.map_embed` + lemmas
- `prop_of_elem_prop_set` (if not deleted in Step 4)
- `comp_of_map_project`, `trace_of_map_project`, `trace_rt_of_map_project`

### Keep in `basic.lean` (renamed to `basic.lean` or deleted if empty)
- Only truly basic/uncategorized things, or delete if everything moved.

### Approach
Do this incrementally:
1. Create one new file at a time.
2. Move definitions + lemmas.
3. Add import to `basic.lean` so everything re-exports.
4. Build-test.
5. Commit.

---

## Step 9: Move `BetaUnionSq` and shared notation to `internal_defs.lean`

### Changes
- Create `CellularAutomatas/internal_defs.lean` (imports `defs.lean`).
- Move `BetaUnionSq` type + instances from `regular_to_left_indep.lean` to `internal_defs.lean`.
- Move `notation:max x "³"` (for `Fin 3 → x`) from `compress_to_diag.lean` to `internal_defs.lean`.
- Move `triple_at` from `compress_to_diag.lean` to `internal_defs.lean` (it uses the `³` notation).
- Update imports: files that use these (`regular_to_left_indep.lean`, `compress_to_diag.lean`, `composition.lean`) import `internal_defs.lean`.

---

## Step 10: Mark construction-internal lemmas `private`

For each construction namespace, mark lemmas `private` unless they are:
- Referenced in `results.lean`
- Used by another file outside the namespace

### Files to audit:
- `CompressToDiag`: `C_δ_fst_lt`, `C_δ_fst_3`, `C_self_tracks_speedup`, `C_right_tracks_speedup`, `C_embed_eq` → all `private`
- `DecompressTriple`: `state_track`, `delta_snd`, `counter_stored` → all `private`
- `SimFromΛ`: `state_track`, `step_counter_sim`, `before_trigger`, `get_neighbor_val_*`, `after_trigger` → most `private` (keep `spec`, `h_cond_form`)
- `LeftIndepSpeedupQuiescent`: many internal lemmas → `private`
- `Composition`: internal `C1'`, `C1_Λ`, `C2_3x`, `C_sim`, `C_decomp`, `C_exact` → stay (they structure the proof), but helper lemmas → `private`
- `CAgfSpeedup`: `step1`, `step2`, `step3`, `g1_spec`, `g2_spec`, `g2_initial_spec` → `private`
- `QuiescentBorderLeftIndep`: `embed_word_in_range`, `embed_word_out_range`, `orig_left_of_cone`, `orig_right_of_word`, `spec_internal`, `spec_unwrap` → `private`
- `DeadBorder`: `shape_outside`, `shape_inside`, `main_center`, `main_left`, `main_right`, `main`, `inv`, `trace_eq_project_unfold` → `private`
- `DeadBorderCoord`: `map_coord_iff`, `map_coord_prev`, `map_coord_next` → `private`

### Approach
One file at a time. Add `private` keyword. Build-test. Commit.

**Caution**: Some `private` lemmas may actually be used cross-file via the namespace. Verify with grep before marking private. If used externally, keep public.

---

## General Notes

- **Build command**: `lake build ./CellularAutomatas/results.lean 2>&1 | head -80`
- If `results.lean` builds, also build `all.lean`: `lake build ./CellularAutomatas/all.lean 2>&1 | head -80`
- **Git workflow**: `git add -A && git commit -m "..."` after each verified step.
- Steps 1–5 are low-risk, independent changes. Do them first.
- Steps 6–8 are higher-risk (import chain changes). Do them carefully.
- Steps 9–10 are cosmetic/organizational. Do them last.
