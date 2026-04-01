import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

/-!
# Fold CA Construction

This file defines a CA that folds a bi-infinite configuration into a right-infinite one.

## Main Definitions

* `FoldConfig` - Folds a bi-infinite config: negative positions → `none`,
  positive `i` → `some (c i, c (-i-1))`.
* `foldCA` - CA operating on folded configs. When a left-moving signal hits the `none`
  boundary, it reflects back as a right-moving signal (swapping components:
  second component's left signal → first component's right signal).

## Main Results

* `fold_spec` - The fold CA correctly simulates the original CA.
-/

namespace CellularAutomatas

open CellAutomaton

/-! ### Fold Configuration -/

/--
Fold a bi-infinite config into a right-infinite one.
- Position `i < 0`: `none`
- Position `i ≥ 0`: `some (c i, c (-i - 1))`

This pairs position `i` with position `-i - 1`, folding the negative half onto the positive.
At i=0: pairs c(0) with c(-1)
At i=1: pairs c(1) with c(-2)
etc.
-/
def FoldConfig {α : Type} (c : Config α) : Config (Option (α × α)) :=
  fun p =>
    if p < 0 then
      none
    else
      some (c p, c (-p - 1))

/-! ### Bordered Config Lemmas -/

section BorderedConfigLemmas

variable {α : Type}

@[simp]
lemma BorderedConfig_pos (b₁ : α) (v w : Word α) (b₂ : α) (i : ℤ)
    (hi : 0 ≤ i) (hi2 : i < w.length) :
    BorderedConfig b₁ v w b₂ i = w[i.toNat] := by
  unfold BorderedConfig
  simp only [hi, hi2, and_self, ↓reduceDIte]

@[simp]
lemma BorderedConfig_neg (b₁ : α) (v w : Word α) (b₂ : α) (i : ℤ)
    (hi : -v.length ≤ i) (hi2 : i < 0) :
    BorderedConfig b₁ v w b₂ i = v[(-i - 1).toNat] := by
  unfold BorderedConfig
  have h1 : ¬(0 ≤ i ∧ i < w.length) := by omega
  have h2a : -↑v.length ≤ i := hi
  have h2b : i < 0 := hi2
  simp only [h1, ↓reduceDIte, h2a, h2b, and_self]

@[simp]
lemma BorderedConfig_right_border (b₁ : α) (v w : Word α) (b₂ : α) (i : ℤ)
    (hi : i ≥ w.length) :
    BorderedConfig b₁ v w b₂ i = b₂ := by
  unfold BorderedConfig
  have h1 : ¬(0 ≤ i ∧ i < w.length) := by omega
  have h2 : ¬(-↑v.length ≤ i ∧ i < 0) := by omega
  simp only [h1, ↓reduceDIte, h2, hi, ite_true]

@[simp]
lemma BorderedConfig_left_border (b₁ : α) (v w : Word α) (b₂ : α) (i : ℤ)
    (hi : i < -v.length) :
    BorderedConfig b₁ v w b₂ i = b₁ := by
  unfold BorderedConfig
  have h1 : ¬(0 ≤ i ∧ i < w.length) := by omega
  have h2 : ¬(-↑v.length ≤ i ∧ i < 0) := by omega
  have h3 : ¬(i ≥ w.length) := by omega
  simp only [h1, ↓reduceDIte, h2, h3, ite_false]

end BorderedConfigLemmas

/-! ### Fold CA Construction -/

/--
Given a CA `C`, construct a CA `foldCA C` that operates on folded configurations.

The folded config has type `Option (C.Q × C.Q)`:
- `none` represents the boundary (negative positions)
- `some (fwd, bwd)` where `fwd` tracks position i, `bwd` tracks position -i-1

Key behavior: at position 0 (boundary), fwd's left neighbor comes from bwd,
and bwd's right neighbor comes from fwd — this is the reflection.
-/
def foldCA {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) : CellAutomaton (Option (α × α)) β :=
  {
    Q := Option (C.Q × C.Q)
    δ := fun left center right =>
      match left, center, right with
      -- Boundary case (position 0): fwd's left = bwd, bwd's right = fwd
      | none, some (c_fwd, c_bwd), some (r_fwd, r_bwd) =>
          some (C.δ c_bwd c_fwd r_fwd, C.δ r_bwd c_bwd c_fwd)
      -- Normal case (position > 0): fwd uses fwd neighbors, bwd uses bwd neighbors (reversed)
      | some (l_fwd, l_bwd), some (c_fwd, c_bwd), some (r_fwd, r_bwd) =>
          some (C.δ l_fwd c_fwd r_fwd, C.δ r_bwd c_bwd l_bwd)
      -- Invalid states
      | _, _, _ => none
    embed := fun
      | none => none
      | some (a, b) => some (C.embed a, C.embed b)
    project := fun
      | none => default  -- border output (shouldn't be queried at valid positions)
      | some (q, _) => C.project q  -- project first component
  }

/-! ### FoldConfig lemmas -/

@[simp]
lemma FoldConfig_neg {α : Type} (c : Config α) (p : ℤ) (hp : p < 0) :
    FoldConfig c p = none := by
  simp only [FoldConfig, hp, ↓reduceIte]

@[simp]
lemma FoldConfig_nonneg {α : Type} (c : Config α) (p : ℤ) (hp : 0 ≤ p) :
    FoldConfig c p = some (c p, c (-p - 1)) := by
  simp only [FoldConfig, not_lt.mpr hp, ↓reduceIte]

/-! ### Fold CA specification -/

/-- Helper: FoldConfig on the internal state type -/
def FoldConfigQ {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config C.Q) : Config (foldCA C).Q :=
  fun p => if p < 0 then none else some (c p, c (-p - 1))

lemma FoldConfigQ_neg {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config C.Q) (p : ℤ) (hp : p < 0) :
    FoldConfigQ C c p = none := by
  unfold FoldConfigQ
  simp only [hp, ↓reduceIte]

lemma FoldConfigQ_nonneg {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config C.Q) (p : ℤ) (hp : 0 ≤ p) :
    FoldConfigQ C c p = some (c p, c (-p - 1)) := by
  unfold FoldConfigQ
  simp only [not_lt.mpr hp, ↓reduceIte]

/-- embed_config of FoldConfig equals FoldConfigQ of embed_config -/
lemma embed_FoldConfig {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config α) :
    (foldCA C).embed_config (FoldConfig c) = FoldConfigQ C (C.embed_config c) := by
  funext p
  simp only [CellAutomaton.embed_config, FoldConfigQ, FoldConfig, foldCA]
  split_ifs <;> rfl

/-- Helper: the folded config or any nextt of it is none at negative positions -/
lemma fold_nextt_neg {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config C.Q) (t : ℕ) (p : ℤ) (hp : p < 0) :
    (foldCA C).nextt (FoldConfigQ C c) t p = none := by
  induction t generalizing p with
  | zero => exact FoldConfigQ_neg C c p hp
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- All three neighbors of a negative position are ≤ p+1
    -- For p < 0, we have p-1 < 0, so ih applies to p-1 and p
    have hp1 : p - 1 < 0 := by omega
    rw [ih p hp, ih (p - 1) hp1]
    -- For p + 1: either < 0 or = 0
    by_cases hp2 : p + 1 < 0
    · rw [ih (p + 1) hp2]
      simp [foldCA]
    · -- p + 1 ≥ 0, but p < 0, so p = -1 and p + 1 = 0
      have heq : p = -1 := by omega
      subst heq
      simp only [Int.reduceNeg, neg_add_cancel]
      -- δ (none) (none) (some ...) = none by our definition
      simp only [foldCA]

/-- Key lemma: FoldConfigQ commutes with nextt -/
lemma fold_nextt_spec {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config C.Q) (t : ℕ) (i : ℤ) (hi : 0 ≤ i) :
    (foldCA C).nextt (FoldConfigQ C c) t i =
      some (C.nextt c t i, C.nextt c t (-i - 1)) := by
  induction t generalizing i with
  | zero =>
    simp only [CellAutomaton.nextt_zero]
    exact FoldConfigQ_nonneg C c i hi
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- At position i, look at neighbors i-1, i, i+1
    have hi_plus : 0 ≤ i + 1 := by omega
    have h_center := ih i hi
    have h_right := ih (i + 1) hi_plus
    -- For the left neighbor: if i = 0, it's none; if i > 0, use ih
    by_cases hi0 : i = 0
    · -- Boundary case: i = 0
      subst hi0
      -- Left neighbor at -1 is none
      have h_left : (foldCA C).nextt (FoldConfigQ C c) t (-1) = none :=
        fold_nextt_neg C c t (-1) (by omega)
      -- Normalize 0 - 1 = -1, 0 + 1 = 1, etc.
      simp only [zero_sub, zero_add, Int.reduceNeg] at h_center h_right ⊢
      rw [h_left, h_center, h_right]
      simp only [foldCA]
      rfl
    · -- Normal case: i > 0
      have hi_minus : 0 ≤ i - 1 := by omega
      have h_left := ih (i - 1) hi_minus
      rw [h_left, h_center, h_right]
      simp only [foldCA]
      -- The δ matches: fwd uses l_fwd, c_fwd, r_fwd; bwd uses r_bwd, c_bwd, l_bwd
      congr 1
      all_goals (congr 1; ring_nf)

/--
The foldCA correctly simulates the original CA on a bi-infinite configuration.

At position `i ≥ 0`, the output of `foldCA C` equals the output of `C` at position `i`.
-/
theorem fold_spec {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config α) (t : ℕ) (i : ℤ) (hi : 0 ≤ i) :
    (foldCA C).comp (FoldConfig c) t i = C.comp c t i := by
  -- Unfold comp to nextt + project
  unfold CellAutomaton.comp CellAutomaton.project_config
  simp only [Function.comp_apply]
  -- The key: FoldConfig (embed_config c) is definitionally equal to FoldConfigQ
  -- because both are `fun p => if p < 0 then none else some (c p, c (-p-1))`
  show (foldCA C).project ((foldCA C).nextt (FoldConfig (C.embed_config c)) t i) =
       C.project (C.nextt (C.embed_config c) t i)
  -- FoldConfig on C.Q is definitionally FoldConfigQ
  have h_eq : FoldConfig (C.embed_config c) = FoldConfigQ C (C.embed_config c) := rfl
  rw [h_eq]
  -- Now use fold_nextt_spec
  rw [fold_nextt_spec C (C.embed_config c) t i hi]
  -- Project from the folded state
  simp only [foldCA]

/-! ### FoldConfig of BorderedConfig -/

/--
When `v.length = w.length`, folding a bordered config at position `0 ≤ i < w.length`
gives the pair `(w[i], v[i])` — effectively zipping the two words.
-/
lemma FoldConfig_BorderedConfig_inner {α : Type} (b₁ : α) (v w : Word α) (b₂ : α)
    (hlen : v.length = w.length) (i : ℤ) (hi : 0 ≤ i) (hi2 : i < w.length) :
    FoldConfig (BorderedConfig b₁ v w b₂) i = some (w[i.toNat], v[i.toNat]) := by
  simp only [FoldConfig, not_lt.mpr hi, ↓reduceIte]
  -- Forward: w[i]
  have fwd : BorderedConfig b₁ v w b₂ i = w[i.toNat] :=
    BorderedConfig_pos b₁ v w b₂ i hi hi2
  -- Backward: v[i] at position -i-1
  have h_neg : -i - 1 < 0 := by omega
  have h_range : -↑v.length ≤ -i - 1 := by simp only [hlen]; omega
  have bwd : BorderedConfig b₁ v w b₂ (-i - 1) = v[i.toNat] := by
    rw [BorderedConfig_neg b₁ v w b₂ (-i - 1) h_range h_neg]
    congr 1
    omega
  rw [fwd, bwd]

/--
When `v.length = w.length`, folding a bordered config at position `i ≥ w.length`
gives the constant border pair `(b₂, b₁)`.
-/
lemma FoldConfig_BorderedConfig_border {α : Type} (b₁ : α) (v w : Word α) (b₂ : α)
    (hlen : v.length = w.length) (i : ℤ) (hi : i ≥ w.length) :
    FoldConfig (BorderedConfig b₁ v w b₂) i = some (b₂, b₁) := by
  have hi0 : 0 ≤ i := by omega
  simp only [FoldConfig, not_lt.mpr hi0, ↓reduceIte]
  -- Forward: b₂ (right border)
  have fwd : BorderedConfig b₁ v w b₂ i = b₂ :=
    BorderedConfig_right_border b₁ v w b₂ i hi
  -- Backward: b₁ (left border) at position -i-1 < -w.length
  have h_left : -i - 1 < -↑v.length := by simp only [hlen]; omega
  have bwd : BorderedConfig b₁ v w b₂ (-i - 1) = b₁ :=
    BorderedConfig_left_border b₁ v w b₂ (-i - 1) h_left
  rw [fwd, bwd]

/--
`FoldConfig` of a bordered config: case analysis on position.
When `v.length = w.length`:
- `i < 0`: `none`
- `0 ≤ i < w.length`: `some (w[i], v[i])`
- `i ≥ w.length`: `some (b₂, b₁)`
-/
lemma FoldConfig_BorderedConfig_eq {α : Type} (b₁ : α) (v w : Word α) (b₂ : α)
    (hlen : v.length = w.length) (i : ℤ) :
    FoldConfig (BorderedConfig b₁ v w b₂) i =
      if h1 : i < 0 then none
      else if h2 : i < w.length then
        have hi_nat : i.toNat < w.length := by omega
        have hv_nat : i.toNat < v.length := by omega
        some (w[i.toNat]'hi_nat, v[i.toNat]'hv_nat)
      else some (b₂, b₁) := by
  split_ifs with h1 h2
  · exact FoldConfig_neg _ i h1
  · have hi : 0 ≤ i := by omega
    exact FoldConfig_BorderedConfig_inner b₁ v w b₂ hlen i hi h2
  · have hi : i ≥ w.length := by omega
    exact FoldConfig_BorderedConfig_border b₁ v w b₂ hlen i hi

/--
`FoldConfig` of a bordered config equals a bordered config on pairs with empty left word.
When `v.length = w.length`:
`FoldConfig [b₁ | v ‖ w | b₂] = [none | [] ‖ zip w v | some (b₂, b₁)]`
-/
lemma FoldConfig_BorderedConfig {α : Type} (b₁ : α) (v w : Word α) (b₂ : α)
    (hlen : v.length = w.length) :
    FoldConfig (BorderedConfig b₁ v w b₂) =
      BorderedConfig none [] (List.zipWith (fun a b => some (a, b)) w v) (some (b₂, b₁)) := by
  funext i
  rw [FoldConfig_BorderedConfig_eq b₁ v w b₂ hlen i]
  unfold BorderedConfig
  simp only [List.length_zipWith, hlen, min_self, List.length_nil, Nat.cast_zero, neg_zero]
  by_cases hi : i < 0
  · -- i < 0: result is none
    have h1 : ¬(0 ≤ i ∧ i < ↑w.length) := by omega
    have h3 : ¬(i ≥ ↑w.length) := by omega
    simp [hi, h1, h3]
  · have h0 : 0 ≤ i := by omega
    by_cases hi2 : i < w.length
    · -- 0 ≤ i < w.length: result is some (w[i], v[i])
      have h1 : 0 ≤ i ∧ i < ↑w.length := ⟨h0, hi2⟩
      simp [hi, hi2, h1, List.getElem_zipWith]
    · -- i ≥ w.length: result is some (b₂, b₁)
      have h3 : i ≥ ↑w.length := by omega
      simp [hi, hi2, h3]

end CellularAutomatas
