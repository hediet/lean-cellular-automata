# Refactoring Analysis: `tCellAutomaton α` → `tCellAutomaton α schema`

## Proposed Change

```lean
-- NEW
structure AcceptanceSchema where
  t : ℕ → ℕ
  p : ℕ → ℤ

structure tCellAutomaton (α : Type) (schema : AcceptanceSchema) extends LCellAutomaton α

-- CURRENT
structure tCellAutomaton (α : Type) extends LCellAutomaton α where
  t : ℕ → ℕ
  p : ℕ → ℤ
```

## Summary

| Metric | Value |
|--------|-------|
| **Active .lean files affected** | ~15 |
| **tCellAutomaton constructions to change** | 7 (only 3 outside `defs.lean` / `basic.lean`) |
| **CA class definitions to rewrite** | 14 (`CA`, `CA_rt`, `CA_2n`, `CA_lt`, `CAr`, `OCA*`, `OCAr*`, `OCA_2n_neg2n`) |
| **Helper lemmas to rewrite** | ~8 (`elem_L_iff`, `CA_rt_t`, `CA_rt_p`, `toRtCa`, `map_embed`, `ℒ_CA_rt_iff`, etc.) |
| **Proofs that extract `.t` / `.p` from membership** | ~10 sites (pattern: `have hC_t := hC.2; have hC_p := hC.1.2`) |
| **Advice system** | Medium — `tCellAutomatonWithAdvice` needs schema parameter |
| **Estimated difficulty** | **Medium** — mostly mechanical, with a few design decisions |

## Difficulty Breakdown by Area

### 1. Core Definitions (`defs.lean`) — Easy

**Current (lines 322–382):**
```lean
structure tCellAutomaton (α: Type) extends LCellAutomaton α where
  t: ℕ → ℕ
  p: ℕ → ℤ

def tCellAutomata (α: Type): Set (tCellAutomaton α) := Set.univ

def CA   := { C ∈ tCellAutomata α | C.p = fun _ => 0 }
def CA_rt := CA α |> t_rt α
-- etc.
```

**After:**
```lean
structure AcceptanceSchema where
  t : ℕ → ℕ
  p : ℕ → ℤ

namespace AcceptanceSchema
  def rt_center    : AcceptanceSchema := ⟨(· - 1), fun _ => 0⟩
  def rt_right     : AcceptanceSchema := ⟨(· - 1), fun n => n⟩
  def time_2n_center : AcceptanceSchema := ⟨fun n => 2 * (n - 1), fun _ => 0⟩
  def time_2n_left : AcceptanceSchema := ⟨fun n => 2 * (n - 1), fun n => -((n : ℤ) - 1)⟩
end AcceptanceSchema

structure tCellAutomaton (α : Type) (schema : AcceptanceSchema) extends LCellAutomaton α

abbrev CA_rt α := tCellAutomaton α .rt_center
abbrev CA_2n α := tCellAutomaton α .time_2n_center
abbrev CAr_rt α := tCellAutomaton α .rt_right
```

This is straightforward — the definitions become simpler, not more complex.

**`tCellAutomata` disappears** — it was `Set.univ` and served only as a base for filtering.

**`t_rt`/`t_2n`/`t_lt` filter functions disappear** — schemas replace them.

### 2. `accepts` / `L` / `DefinesLanguage` (`defs.lean`) — Easy

**Current:**
```lean
def tCellAutomaton.accepts {C: tCellAutomaton α} (w: Word α): Bool :=
  C.comp w (C.t w.length) (C.p w.length)
```

**After:**
```lean
def tCellAutomaton.accepts {s : AcceptanceSchema} (C: tCellAutomaton α s) (w: Word α): Bool :=
  C.comp ⟬w⟭ (s.t w.length) (s.p w.length)

-- C.L, C.accepts still work exactly as before
```

The `DefinesLanguage` instance needs the schema parameter:
```lean
instance [Alphabet α] (s : AcceptanceSchema) : DefinesLanguage (tCellAutomaton α s) α where
  L C := C.L
```

### 3. Fixed-Schema Classes (`CA_rt`, `CA_2n`, `CAr_rt`) — **Big Win**

These become **type aliases** instead of filtered sets:

```lean
-- CURRENT: CA_rt α = { C ∈ { C ∈ Set.univ | C.p = 0 } | ∀ n, C.t n = n - 1 }
-- AFTER:   CA_rt α = tCellAutomaton α .rt_center
```

**Consequences:**
- `C ∈ CA_rt α` (set membership) → `C : CA_rt α` (typing)
- `C.val` / `C.prop` pattern → just `C` directly
- `CA_rt_t`, `CA_rt_p` helper lemmas → **deleted** (schema is definitionally known)
- `⟨ca, proof⟩` membership construction → just build the `tCellAutomaton`
- `ℒ_CA_rt_iff` simplifies: `L ∈ ℒ(CA_rt α) ↔ ∃ C : CA_rt α, C.L = L`

### 4. Variable-Schema Classes (`CA_lt`, `OCA_lt`) — Needs Design Decision

`CA_lt` currently filters by `∃ c, ∀ n, C.t n = c * (n - 1)`. With schema-as-parameter:

**Option A: Existential over schema**
```lean
def ℒ_CA_lt (α) [Alphabet α] : Set (Language α) :=
  { L | ∃ c : ℕ, ∃ C : tCellAutomaton α (.lt_center c), L = C.L }
```

**Option B: Schema predicate**
```lean
def lt_schema (s : AcceptanceSchema) : Prop :=
  s.p = fun _ => 0 ∧ ∃ c, s.t = fun n => c * (n - 1)

def ℒ_CA_lt (α) [Alphabet α] : Set (Language α) :=
  { L | ∃ s, lt_schema s ∧ ∃ C : tCellAutomaton α s, L = C.L }
```

Option A is cleaner. The key insight: `CA_lt` is only ever used at the ℒ level (as a language class), never as a type of automata you pass around. So defining it directly as `Set (Language α)` is fine.

### 5. Independence-Constrained Classes (`OCA`, `OCAr`) — Easy

```lean
-- CURRENT: OCA = { C ∈ CA α | C.left_independent }
-- AFTER:
def OCA_rt α := { C : CA_rt α // C.left_independent }
```

`C.left_independent` accesses `C.toCellAutomaton.left_independent` which lives on `CellAutomaton`, unaffected by the schema change.

### 6. Constructions — Easy (Only 3 Sites)

Only **3 files** construct `tCellAutomaton` values outside core definitions:

#### a. `lift_language.lean` — `liftCA`
```lean
-- CURRENT
private def liftCA (C : tCellAutomaton α) : tCellAutomaton (Option α) where
  ...
  t := C.t
  p := C.p

-- AFTER: Schema propagates through the type
private def liftCA (C : tCellAutomaton α s) : tCellAutomaton (Option α) s where
  ...
  -- t, p not needed — inherited from schema parameter
```

#### b. `ca_rt_rev_eq_car_rt.lean` — `toRight`, `toLeft`
```lean
-- CURRENT
def tCellAutomaton.toRight (C : tCellAutomaton α) : tCellAutomaton α where
  toCellAutomaton := C.toCellAutomaton.flip
  t := C.t
  p := fun n => ((n : ℤ) - 1)

-- AFTER: Output schema is different from input — this is a schema change
def tCellAutomaton.toRight (C : tCellAutomaton α s) : tCellAutomaton α ⟨s.t, fun n => ((n : ℤ) - 1)⟩ where
  toCellAutomaton := C.toCellAutomaton.flip
-- Or more concretely, since this is always called on CA_rt:
def CA_rt.toRight (C : CA_rt α) : CAr_rt α where
  toCellAutomaton := C.toCellAutomaton.flip
```

This is the **one place** where the schema changes between input and output. The type-parameter approach makes this explicit, which is actually a clarity improvement.

#### c. `rt_eq_2n_iff_rt_eq_rt_rev.lean` — `ca_2n_subset_ca_2n_proper` etc.
```lean
-- CURRENT
let C' : tCellAutomaton α := {
  toCellAutomaton := ...
  t := fun n => 2 * n
  p := fun _ => 0
}

-- AFTER: Use a specific schema
def AcceptanceSchema.time_2n_proper : AcceptanceSchema := ⟨fun n => 2 * n, fun _ => 0⟩

let C' : tCellAutomaton α .time_2n_proper := {
  toCellAutomaton := ...
}
```

### 7. `tCellAutomaton.map_embed` (`basic.lean`) — Easy

```lean
-- CURRENT
def tCellAutomaton.map_embed (C: tCellAutomaton α) (f: β → α): tCellAutomaton β :=
  { toCellAutomaton := C.toCellAutomaton.map_embed (Option.map f), t := C.t, p := C.p }

-- AFTER: Schema propagates, no .t/.p needed
def tCellAutomaton.map_embed (C: tCellAutomaton α s) (f: β → α): tCellAutomaton β s :=
  { toCellAutomaton := C.toCellAutomaton.map_embed (Option.map f) }
```

The simp lemma `c_map_embed_in_ca_rt_iff_c_in_ca_rt` becomes trivial (types match definitionally).

### 8. `toRtCa` (`basic.lean`) — Easy

```lean
-- CURRENT
def toRtCa (C: CellAutomaton α？ Bool): CA_rt α :=
  ⟨{ toCellAutomaton := C, t n := n - 1, p _ := 0 }, by simp [CA_rt, t_rt, CA, tCellAutomata]⟩

-- AFTER: No membership proof needed
def toRtCa (C: CellAutomaton α？ Bool): CA_rt α :=
  { toCellAutomaton := C }
```

### 9. Proofs That Extract `.t` / `.p` from Membership — **Eliminated**

~10 proof sites currently do:
```lean
have hC_t : ∀ n, C.t n = n - 1 := by unfold CA_rt t_rt at C; grind
have hC_p : C.p = fun _ => 0 := by ...
```

After the change, if `C : CA_rt α`, then `s = .rt_center` is in the type, so `s.t n = n - 1` is **definitional**. These `have` lines and their associated proof work **disappear entirely**. Sites:

- `basic.lean`: `CA_rt_t`, `CA_rt_p` — deleted
- `rt_eq_2n_iff_rt_eq_rt_rev.lean`: Lines 67-69, 150-152, 202-203, 579-580 — deleted
- `ca_rt_rev_eq_car_rt.lean`: membership extraction — deleted

### 10. Advice System (`defs.lean`) — Medium

```lean
-- CURRENT
structure tCellAutomatonWithAdvice (α: Type) where
  Γ: Type
  [alphabetΓ: Alphabet Γ]
  adv: Advice α Γ
  C: tCellAutomaton (α × Γ)

-- AFTER: Needs schema parameter
structure tCellAutomatonWithAdvice (α: Type) (s : AcceptanceSchema) where
  Γ: Type
  [alphabetΓ: Alphabet Γ]
  adv: Advice α Γ
  C: tCellAutomaton (α × Γ) s
```

The `HAdd` instance and `weak_rt_closed` definitions adjust accordingly:
```lean
-- CURRENT
def Advice.weak_rt_closed (f: Advice α Γ) :=
  ℒ (CA_rt (α × Γ) + f) = ℒ (CA_rt α)

-- AFTER: Same meaning, simpler types
def Advice.weak_rt_closed (f: Advice α Γ) :=
  ℒ (CA_rt (α × Γ) + f) = ℒ (CA_rt α)
-- Actually unchanged — CA_rt is now an abbrev for tCellAutomaton α .rt_center
```

### 11. `ℒ` Function — Needs Slight Adjustment

```lean
-- CURRENT
def ℒ [DefinesLanguage T α] (s: Set T): Set (Language α) := ...
-- Used as: ℒ (CA_rt α)  where CA_rt α : Set (tCellAutomaton α)

-- AFTER: CA_rt α is a Type, not a Set
-- Option 1: ℒ works on types directly
def ℒ (T : Type) [DefinesLanguage T α] : Set (Language α) :=
  { L | ∃ ca : T, L = DefinesLanguage.L ca }
-- Used as: ℒ (CA_rt α)

-- Option 2: Keep Set-based ℒ for variable classes, add new for types
```

This is a **design decision point**. Option 1 is cleaner — `ℒ (CA_rt α)` reads the same but is now `∃ C : CA_rt α, L = C.L` instead of `∃ C ∈ CA_rt α, C.L = L`.

For `CA_lt` (variable schema), you'd write: `⋃ c, ℒ (tCellAutomaton α (.lt_center c))`.

### 12. `verification_candidates.lean` / `open_questions.lean` — Easy

These only state theorems using CA classes and `ℒ`. The changes are syntactic (type vs. set membership).

### 13. WIP Files (`wip/`) — Low Priority

`speedup_right_border_oca.lean` and `lt_closed.lean` use CA classes but are work-in-progress. They can be updated later.

### 14. `.old/` Files — Skip

Archived code. No need to update.

---

## Migration Order

1. **`defs.lean`** — Define `AcceptanceSchema`, redefine `tCellAutomaton`, redefine CA classes, update `tCellAutomatonWithAdvice`, update `ℒ`.
2. **`basic.lean`** — Update `elem_L_iff`, delete `CA_rt_t`/`CA_rt_p`, simplify `toRtCa`, update `map_embed`, update `ℒ_CA_rt_iff`.
3. **`ca_rt_utils.lean`** — Update `advice_weak_rt_closed_iff` and related.
4. **`ca_rt_finite_closure.lean`** — Update closure proofs (simpler with types).
5. **Proof files** — `rt_closed.lean`, `two_stage_is_rt_closed.lean`, `is_two_stage_of...`, `advice_prefix_mem_rt_closed.lean`.
6. **Language files** — `lift_language.lean`, `ca_rt_rev_eq_car_rt.lean`, `car_rt_subset_ca_2n.lean`.
7. **`rt_eq_2n_iff_rt_eq_rt_rev/`** — The largest block; mostly deleting `have hC_t`/`have hC_p` lines.
8. **`results.lean`**, `verification_candidates.lean` — Final cleanup.

## Risks

| Risk | Severity | Mitigation |
|------|----------|------------|
| `extends LCellAutomaton α` may interact badly with type parameter | Low | Test early — this is the first thing to verify |
| `ℒ` on types vs sets may need two versions | Medium | Decide upfront; Option 1 (type-based) is sufficient |
| Downstream `.val` / `.prop` patterns break | Low | Mechanical: `.val` → direct, `.prop` → deleted |
| `CA_lt` existential over schema adds verbosity | Low | Define helper: `ℒ_lt α = ⋃ c, ℒ (tCellAutomaton α (.lt_center c))` |

## Net Impact

**Lines removed** (estimated): ~60 (membership proofs, `have hC_t/hC_p`, filter definitions, `t_rt`/`t_2n`/`t_lt`, `tCellAutomata`, `CA_rt_t`/`CA_rt_p`)

**Lines added** (estimated): ~20 (`AcceptanceSchema` + named schemas)

**Net: ~40 lines shorter, and every remaining line is clearer.**
