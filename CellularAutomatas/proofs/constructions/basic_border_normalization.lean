import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

/-!
# Border Normalization CA Construction

This file defines a CA construction that converts a CA with arbitrary borders
`b₁`, `b₂` into a CA that uses the standard `none` border.

## Main Definitions

* `borderNormalizeCA` - CA that simulates `C` on `[b₁ | [] ‖ w | b₂]` given standard word input.

## Main Results

* `border_normalize` - Any CA with borders can be converted to use the uniform `none` border.
-/

namespace CellularAutomatas

open CellAutomaton

/-! ### Border Normalization -/

/--
Border normalization CA construction.

State space: `Option C.Q × C.Q × C.Q` where:
- First: `none` for border, `some q` for interior
- Second: left border simulation (tracks what position -1 would be in `BorderedConfig b₁ [] w b₂`)
- Third: right border simulation (tracks what position n would be)

Key insight: Each cell independently simulates the border evolution.
When a neighbor is border (`none`), use the local simulation as effective neighbor.
-/
def borderNormalizeCA {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) : CellAutomaton α？ β :=
  {
    Q := Option C.Q × C.Q × C.Q
    δ := fun l c r =>
      let (l_main, _, _) := l
      let (c_main, c_lSim, c_rSim) := c
      let (r_main, _, _) := r

      -- Effective neighbors: use local sim if neighbor is border
      -- If left is none → left is left border → use lSim
      -- If right is none → right is right border → use rSim
      let l_eff := l_main.getD c_lSim
      let r_eff := r_main.getD c_rSim

      -- Border simulation evolution:
      -- lSim tracks position -1: sees (pos-2=lSim, pos-1=lSim, pos0=c_main or lSim)
      -- rSim tracks position n: sees (pos n-1=c_main or rSim, pos n=rSim, pos n+1=rSim)
      let c_lSim' := C.δ c_lSim c_lSim (c_main.getD c_lSim)
      let c_rSim' := C.δ (c_main.getD c_rSim) c_rSim c_rSim

      -- Main state evolution
      let c_main' := match c_main with
        | some q => some (C.δ l_eff q r_eff)
        | none =>
          -- Border cell. Becomes active if adjacent to interior.
          if r_main.isSome then
            -- Right neighbor is interior → we're LEFT border (position -1)
            some (C.δ c_lSim c_lSim r_eff)
          else if l_main.isSome then
            -- Left neighbor is interior → we're RIGHT border (position n)
            some (C.δ l_eff c_rSim c_rSim)
          else
            -- Deep in border region, stay none
            none

      (c_main', c_lSim', c_rSim')

    embed := fun a =>
      match a with
      | some x => (some (C.embed x), C.embed b₁, C.embed b₂)
      | none => (none, C.embed b₁, C.embed b₂)

    project := fun (main, lSim, _) =>
      C.project (main.getD lSim)  -- border projects using left sim
  }

/-! ### Border Config Lemmas -/

-- Simplification for `BorderedConfig b₁ [] w b₂`:
-- Position i ∈ [0, |w|): w[i]
-- Position i ≥ |w|: b₂
-- Position i < 0: b₁

@[simp]
lemma BorderedConfig_empty_v_pos (b₁ : α) (w : Word α) (b₂ : α) (i : ℤ)
    (hi : 0 ≤ i) (hi2 : i < w.length) :
    BorderedConfig b₁ [] w b₂ i = w[i.toNat] := by
  unfold BorderedConfig
  simp only [hi, hi2, and_self, ↓reduceDIte]

@[simp]
lemma BorderedConfig_empty_v_right (b₁ : α) (w : Word α) (b₂ : α) (i : ℤ)
    (hi : i ≥ w.length) :
    BorderedConfig b₁ [] w b₂ i = b₂ := by
  unfold BorderedConfig
  have h1 : ¬(0 ≤ i ∧ i < w.length) := by omega
  have h2 : ¬(-↑([] : Word α).length ≤ i ∧ i < 0) := by simp only [List.length_nil]; omega
  simp only [h1, ↓reduceDIte, h2, hi, ite_true]

@[simp]
lemma BorderedConfig_empty_v_left (b₁ : α) (w : Word α) (b₂ : α) (i : ℤ)
    (hi : i < 0) :
    BorderedConfig b₁ [] w b₂ i = b₁ := by
  unfold BorderedConfig
  have h1 : ¬(0 ≤ i ∧ i < w.length) := by omega
  have h2 : ¬(-↑([] : Word α).length ≤ i ∧ i < 0) := by simp only [List.length_nil]; omega
  have h3 : ¬(i ≥ w.length) := by omega
  simp only [h1, ↓reduceDIte, h2, h3, ite_false]

/-! ### Embedding Lemmas -/

/-- word_to_config produces `some w[i]` for interior positions. -/
@[simp]
lemma word_to_config_interior {w : Word α} (i : ℤ) (hi : 0 ≤ i) (hi2 : i < w.length) :
    word_to_config w i = some w[i.toNat] := by
  unfold word_to_config
  simp [hi, hi2]

/-- word_to_config produces `none` for left border. -/
@[simp]
lemma word_to_config_left_border {w : Word α} (i : ℤ) (hi : i < 0) :
    word_to_config w i = none := by
  unfold word_to_config
  simp
  intro h; omega

/-- word_to_config produces `none` for right border. -/
@[simp]
lemma word_to_config_right_border {w : Word α} (i : ℤ) (hi : i ≥ w.length) :
    word_to_config w i = none := by
  unfold word_to_config
  simp
  omega

/-! ### Main State Correspondence -/

/--
For positions in the homogeneous left border region (i.e., p < 0), all states are equal
because they all see the same neighbors (all b₁).
-/
lemma bordered_config_left_region_eq {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (t : ℕ) (p₁ p₂ : ℤ)
    (hp₁ : p₁ + t < 0) (hp₂ : p₂ + t < 0) :
    C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p₁ = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p₂ := by
  -- Both positions are entirely in the left border region during all t steps
  -- so they see identical neighborhoods (all b₁) and evolve identically
  induction t generalizing p₁ p₂ with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config]
    have h1 : p₁ < 0 := by omega
    have h2 : p₂ < 0 := by omega
    simp [BorderedConfig_empty_v_left, h1, h2]
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ]
    unfold CellAutomaton.next
    -- At positions p₁ and p₂, neighbors are all in the left border region
    have hp₁_prev : p₁ + t < 0 := by omega
    have hp₂_prev : p₂ + t < 0 := by omega
    have hp₁_l : (p₁ - 1) + t < 0 := by omega
    have hp₂_l : (p₂ - 1) + t < 0 := by omega
    have hp₁_r : (p₁ + 1) + t < 0 := by omega
    have hp₂_r : (p₂ + 1) + t < 0 := by omega
    -- By IH, neighbors at both positions are equal
    simp only [ih _ _ hp₁_l hp₂_l, ih _ _ hp₁_prev hp₂_prev, ih _ _ hp₁_r hp₂_r]

/--
For positions in the homogeneous right border region (i.e., p ≥ w.length), all states are equal
because they all see the same neighbors (all b₂).
-/
lemma bordered_config_right_region_eq {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (t : ℕ) (p₁ p₂ : ℤ)
    (hp₁ : p₁ - t ≥ w.length) (hp₂ : p₂ - t ≥ w.length) :
    C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p₁ = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p₂ := by
  induction t generalizing p₁ p₂ with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config]
    have h1 : p₁ ≥ w.length := by omega
    have h2 : p₂ ≥ w.length := by omega
    simp [BorderedConfig_empty_v_right, h1, h2]
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ]
    unfold CellAutomaton.next
    have hp₁_prev : p₁ - t ≥ w.length := by omega
    have hp₂_prev : p₂ - t ≥ w.length := by omega
    have hp₁_l : (p₁ - 1) - t ≥ w.length := by omega
    have hp₂_l : (p₂ - 1) - t ≥ w.length := by omega
    have hp₁_r : (p₁ + 1) - t ≥ w.length := by omega
    have hp₂_r : (p₂ + 1) - t ≥ w.length := by omega
    simp only [ih _ _ hp₁_l hp₂_l, ih _ _ hp₁_prev hp₂_prev, ih _ _ hp₁_r hp₂_r]

/-! ### Activation and Main Correspondence -/

/--
Far-left positions stay `none`: if p + t < 0, then main is none.
This is because such positions never see an interior neighbor.
-/
lemma borderNormalizeCA_far_left_none {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (t : ℕ) (p : ℤ)
    (hp : p + t < 0) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).1 = none := by
  induction t generalizing p with
  | zero =>
    -- At t=0, p < 0, so word_to_config w p = none
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config]
    have hp0 : p < 0 := by omega
    have h : word_to_config w p = none := by simp [word_to_config]; omega
    simp only [borderNormalizeCA, h]
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ]
    unfold CellAutomaton.next
    -- We need to show the main component is none after transition
    -- Position p-1, p, p+1 all satisfy the bound (p+1) + t < 0 since p + (t+1) < 0
    have hp_prev : p + t < 0 := by omega
    have hpl : (p - 1) + t < 0 := by omega
    have hpr : (p + 1) + t < 0 := by omega
    -- By IH, all neighbors have main = none
    have hl := ih (p - 1) hpl
    have hc := ih p hp_prev
    have hr := ih (p + 1) hpr

    -- Get the states and destructure
    set sl := (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1)
    set sc := (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p
    set sr := (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1)

    -- Center's main is none
    have hc' : sc.1 = none := hc
    have hl' : sl.1 = none := hl
    have hr' : sr.1 = none := hr

    -- The transition function: when center main is none, check neighbors
    simp only [borderNormalizeCA]
    simp only [hc', hr', hl', Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/--
Far-right positions stay `none`: if p - t ≥ w.length, then main is none.
-/
lemma borderNormalizeCA_far_right_none {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (t : ℕ) (p : ℤ)
    (hp : p - t ≥ w.length) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).1 = none := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config]
    have hp0 : p ≥ w.length := by omega
    have h : word_to_config w p = none := by simp [word_to_config]; omega
    simp only [borderNormalizeCA, h]
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ]
    unfold CellAutomaton.next
    have hpl : (p - 1) - t ≥ w.length := by omega
    have hpc : p - t ≥ w.length := by omega
    have hpr : (p + 1) - t ≥ w.length := by omega
    have hl := ih (p - 1) hpl
    have hc := ih p hpc
    have hr := ih (p + 1) hpr

    set sl := (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1)
    set sc := (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p
    set sr := (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1)

    have hc' : sc.1 = none := hc
    have hl' : sl.1 = none := hl
    have hr' : sr.1 = none := hr

    simp only [borderNormalizeCA]
    simp only [hc', hr', hl', Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/--
lSim invariant: when a position is in the deep left border region,
its lSim component tracks the bordered config at position (p-1).

Specifically, lSim(p, t) = nextt_BC t (p-1) when p ≤ 0 and p + t ≤ 0.
-/
lemma borderNormalizeCA_lSim_invariant {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (t : ℕ) (p : ℤ)
    (hp : p ≤ 0) (hpt : p + t ≤ 0) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).2.1 =
      C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1) := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config]
    have hpneg2 : p - 1 < 0 := by omega
    rw [BorderedConfig_empty_v_left b₁ w b₂ (p - 1) hpneg2]
    by_cases hplt : p < 0
    · have h : word_to_config w p = none := by simp [word_to_config]; omega
      simp only [borderNormalizeCA, h]
    · -- p = 0
      have hpeq : p = 0 := by omega
      subst hpeq
      -- For position 0: word_to_config w 0 could be some or none depending on w,
      -- but the lSim component is always C.embed b₁
      simp only [borderNormalizeCA]
      by_cases hw : w.length > 0
      · have h : word_to_config w 0 = some w[0] := by simp [word_to_config, hw]
        simp only [borderNormalizeCA, h]
      · have hw0 : w.length = 0 := by omega
        have h : word_to_config w 0 = none := by simp [word_to_config, hw0]
        simp only [borderNormalizeCA, h]
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ]
    unfold CellAutomaton.next

    have hpt_prev : p + t < 0 := by omega
    have hmain_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).1 = none :=
      borderNormalizeCA_far_left_none C b₁ b₂ w t p hpt_prev

    have ih_lSim := ih p hp (by omega)

    have heq_l : C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 2) =
                 C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1) :=
      bordered_config_left_region_eq C b₁ b₂ w t (p - 2) (p - 1) (by omega) (by omega)
    have heq_r : C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p =
                 C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1) :=
      bordered_config_left_region_eq C b₁ b₂ w t p (p - 1) (by omega) (by omega)

    set sc := (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p with hsc_def

    simp only [borderNormalizeCA, hmain_none, Option.getD_none, ih_lSim]

    -- Goal: C.δ (nextt t (p-1)) (nextt t (p-1)) (nextt t (p-1)) =
    --       C.δ (nextt t (p-1-1)) (nextt t (p-1)) (nextt t (p-1+1))
    -- First normalize the indices on RHS
    have h1 : (p - 1 - 1 : ℤ) = p - 2 := by ring
    have h2 : (p - 1 + 1 : ℤ) = p := by ring
    simp only [h1, h2, heq_l, heq_r]

/--
rSim invariant: For positions where p ≥ w.length - 1 and p - t ≥ w.length - 1,
the rSim component tracks the bordered config at position p + 1.
Symmetric to lSim invariant.
-/
lemma borderNormalizeCA_rSim_invariant {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ)
    (hp : p ≥ w.length - 1) (hpt : p - t ≥ w.length - 1) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).2.2 =
      C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config]
    have hw_pos : w.length > 0 := List.length_pos_of_ne_nil hw
    have hp1_right : p + 1 ≥ w.length := by omega
    rw [BorderedConfig_empty_v_right b₁ w b₂ (p + 1) hp1_right]
    by_cases hpgt : p ≥ w.length
    · have h : word_to_config w p = none := by simp [word_to_config]; omega
      simp only [borderNormalizeCA, h]
    · -- p = w.length - 1
      have hpeq : p = w.length - 1 := by omega
      have hp0 : 0 ≤ p := by omega
      have hpw : p < w.length := by omega
      have h : word_to_config w p = some w[p.toNat] := by simp [word_to_config, hp0, hpw]
      simp only [borderNormalizeCA, h]
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ]
    unfold CellAutomaton.next
    have hw_pos : w.length > 0 := List.length_pos_of_ne_nil hw

    have hpt_prev : p - t ≥ w.length := by omega
    have hmain_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).1 = none :=
      borderNormalizeCA_far_right_none C b₁ b₂ w t p hpt_prev

    have ih_rSim := ih p hp (by omega)

    have heq_l : C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p =
                 C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) :=
      bordered_config_right_region_eq C b₁ b₂ w t p (p + 1) (by omega) (by omega)
    have heq_r : C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 2) =
                 C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) :=
      bordered_config_right_region_eq C b₁ b₂ w t (p + 2) (p + 1) (by omega) (by omega)

    -- Work with the destructured components
    obtain ⟨c_main, c_lSim, c_rSim, hc_eq⟩ :
      ∃ (c_m : C.Q？) (c_ls c_rs : C.Q),
        (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p = (c_m, c_ls, c_rs) :=
      ⟨_, _, _, rfl⟩

    have hc_main_none : c_main = none := by rw [← hmain_none, hc_eq]
    have hc_rSim : c_rSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) := by
      rw [← ih_rSim, hc_eq]

    subst hc_main_none hc_rSim
    rw [hc_eq]
    simp only [borderNormalizeCA, Option.getD_none]
    have h1 : (p + 1 - 1 : ℤ) = p := by ring
    have h2 : (p + 1 + 1 : ℤ) = p + 2 := by ring
    simp only [h1, h2, heq_l, heq_r]

/--
General main invariant: position p is active (main = some) and tracks the bordered config
exactly when p is within the "activation zone" at time t.

The activation zone at time t is: -t ≤ p < |w| + t, i.e., p + t ≥ 0 and p - t < |w|.

Note: requires w ≠ [] because an empty word provides no interior positions
to trigger the activation wave.
-/
lemma borderNormalizeCA_main_general {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ)
    (hp_left : p + t ≥ 0) (hp_right : p - t < w.length) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).1 =
      some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p) := by
  have hw_pos : w.length > 0 := List.length_pos_of_ne_nil hw
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config]
    have hp0 : 0 ≤ p := by omega
    have hpw : p < w.length := by omega
    have h : word_to_config w p = some w[p.toNat] := by
      simp [word_to_config]; constructor <;> omega
    simp only [borderNormalizeCA, h]
    congr 1
    rw [BorderedConfig_empty_v_pos b₁ w b₂ p hp0 hpw]
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ]
    unfold CellAutomaton.next

    -- Three cases based on whether p was in the zone at time t and where
    by_cases h_in_interior : p + t > 0 ∧ p - t < w.length - 1
    · -- Case 1: p was strictly in the interior at time t
      -- Both neighbors were also in the zone
      obtain ⟨h_left_t, h_right_t⟩ := h_in_interior
      have ih_p := ih p (by omega) (by omega)
      have ih_l := ih (p - 1) (by omega) (by omega)
      have ih_r := ih (p + 1) (by omega) (by omega)
      -- All three have main = some _, so the CA computes the correct δ
      show ((borderNormalizeCA C b₁ b₂).δ
              ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1))
              ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p)
              ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1))).1 =
           some (C.next (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t) p)

      -- Destructure with explicit equalities to connect IHs
      obtain ⟨l_main, l_lSim, l_rSim, hl_eq⟩ :
        ∃ (l_m : C.Q？) (l_ls l_rs : C.Q),
          (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1) = (l_m, l_ls, l_rs) :=
        ⟨_, _, _, rfl⟩
      obtain ⟨c_main, c_lSim, c_rSim, hc_eq⟩ :
        ∃ (c_m : C.Q？) (c_ls c_rs : C.Q),
          (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p = (c_m, c_ls, c_rs) :=
        ⟨_, _, _, rfl⟩
      obtain ⟨r_main, r_lSim, r_rSim, hr_eq⟩ :
        ∃ (r_m : C.Q？) (r_ls r_rs : C.Q),
          (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1) = (r_m, r_ls, r_rs) :=
        ⟨_, _, _, rfl⟩

      -- From IHs: l_main, c_main, r_main are all some _
      have hl1 : l_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1)) := by
        rw [← ih_l, hl_eq]
      have hc1 : c_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p) := by
        rw [← ih_p, hc_eq]
      have hr1 : r_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1)) := by
        rw [← ih_r, hr_eq]

      -- Rewrite goal using the equalities
      subst hl1 hc1 hr1
      rw [hl_eq, hc_eq, hr_eq]
      simp only [borderNormalizeCA, Option.getD_some]
      rfl

    · -- Case 2 or 3: p was at a boundary or outside
      push_neg at h_in_interior

      by_cases h_left_bdy : p + t = 0
      · -- Case 2: Left boundary - p was at left edge of zone
        by_cases h_r_in_zone : (p + 1) - t < w.length
        · -- Right neighbor was in zone
          have ih_p := ih p (by omega) (by omega)
          have ih_r := ih (p + 1) (by omega) h_r_in_zone
          have h_l_far : (p - 1) + t < 0 := by omega
          have hmain_l_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1)).1 = none :=
            borderNormalizeCA_far_left_none C b₁ b₂ w t (p - 1) h_l_far

          -- Get the lSim invariant: lSim tracks C.nextt t (p-1)
          have h_lSim := borderNormalizeCA_lSim_invariant C b₁ b₂ w t p (by omega) (by omega)

          -- Destructure the triples
          obtain ⟨l_main, l_lSim, l_rSim, hl_eq⟩ :
            ∃ (l_m : C.Q？) (l_ls l_rs : C.Q),
              (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1) = (l_m, l_ls, l_rs) :=
            ⟨_, _, _, rfl⟩
          obtain ⟨c_main, c_lSim, c_rSim, hc_eq⟩ :
            ∃ (c_m : C.Q？) (c_ls c_rs : C.Q),
              (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p = (c_m, c_ls, c_rs) :=
            ⟨_, _, _, rfl⟩
          obtain ⟨r_main, r_lSim, r_rSim, hr_eq⟩ :
            ∃ (r_m : C.Q？) (r_ls r_rs : C.Q),
              (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1) = (r_m, r_ls, r_rs) :=
            ⟨_, _, _, rfl⟩

          -- From IHs and none facts
          have hl1 : l_main = none := by rw [← hmain_l_none, hl_eq]
          have hc1 : c_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p) := by
            rw [← ih_p, hc_eq]
          have hr1 : r_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1)) := by
            rw [← ih_r, hr_eq]
          have h_lSim' : c_lSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1) := by
            rw [← h_lSim, hc_eq]

          subst hl1 hc1 hr1 h_lSim'
          rw [hl_eq, hc_eq, hr_eq]
          simp only [borderNormalizeCA, Option.getD_some, Option.getD_none]
        · -- Right neighbor was NOT in zone - p is the only position in zone at time t
          have h_r_far : (p + 1) - t ≥ w.length := by omega
          have hmain_r_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1)).1 = none :=
            borderNormalizeCA_far_right_none C b₁ b₂ w t (p + 1) h_r_far
          have h_l_far : (p - 1) + t < 0 := by omega
          have hmain_l_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1)).1 = none :=
            borderNormalizeCA_far_left_none C b₁ b₂ w t (p - 1) h_l_far
          have ih_p := ih p (by omega) (by omega)

          -- Both lSim and rSim invariants apply in this case
          have h_lSim := borderNormalizeCA_lSim_invariant C b₁ b₂ w t p (by omega) (by omega)
          have h_rSim := borderNormalizeCA_rSim_invariant C b₁ b₂ w hw t p (by omega) (by omega)

          -- Destructure the triples
          obtain ⟨l_main, l_lSim, l_rSim, hl_eq⟩ :
            ∃ (l_m : C.Q？) (l_ls l_rs : C.Q),
              (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1) = (l_m, l_ls, l_rs) :=
            ⟨_, _, _, rfl⟩
          obtain ⟨c_main, c_lSim, c_rSim, hc_eq⟩ :
            ∃ (c_m : C.Q？) (c_ls c_rs : C.Q),
              (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p = (c_m, c_ls, c_rs) :=
            ⟨_, _, _, rfl⟩
          obtain ⟨r_main, r_lSim, r_rSim, hr_eq⟩ :
            ∃ (r_m : C.Q？) (r_ls r_rs : C.Q),
              (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1) = (r_m, r_ls, r_rs) :=
            ⟨_, _, _, rfl⟩

          have hl1 : l_main = none := by rw [← hmain_l_none, hl_eq]
          have hr1 : r_main = none := by rw [← hmain_r_none, hr_eq]
          have hc1 : c_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p) := by
            rw [← ih_p, hc_eq]
          have h_lSim' : c_lSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1) := by
            rw [← h_lSim, hc_eq]
          have h_rSim' : c_rSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) := by
            rw [← h_rSim, hc_eq]

          subst hl1 hr1 hc1 h_lSim' h_rSim'
          rw [hl_eq, hc_eq, hr_eq]
          simp only [borderNormalizeCA, Option.getD_some, Option.getD_none]

      · by_cases h_right_bdy : p - t = w.length - 1
        · -- Case 3: Right boundary - p was at right edge of zone
          by_cases h_l_in_zone : (p - 1) + t ≥ 0
          · -- Left neighbor was in zone
            have ih_p := ih p (by omega) (by omega)
            have ih_l := ih (p - 1) h_l_in_zone (by omega)
            have h_r_far : (p + 1) - t ≥ w.length := by omega
            have hmain_r_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1)).1 = none :=
              borderNormalizeCA_far_right_none C b₁ b₂ w t (p + 1) h_r_far

            -- Get the rSim invariant: rSim tracks C.nextt t (p+1)
            have h_rSim := borderNormalizeCA_rSim_invariant C b₁ b₂ w hw t p (by omega) (by omega)

            -- Destructure the triples
            obtain ⟨l_main, l_lSim, l_rSim, hl_eq⟩ :
              ∃ (l_m : C.Q？) (l_ls l_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1) = (l_m, l_ls, l_rs) :=
              ⟨_, _, _, rfl⟩
            obtain ⟨c_main, c_lSim, c_rSim, hc_eq⟩ :
              ∃ (c_m : C.Q？) (c_ls c_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p = (c_m, c_ls, c_rs) :=
              ⟨_, _, _, rfl⟩
            obtain ⟨r_main, r_lSim, r_rSim, hr_eq⟩ :
              ∃ (r_m : C.Q？) (r_ls r_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1) = (r_m, r_ls, r_rs) :=
              ⟨_, _, _, rfl⟩

            -- From IHs and none facts
            have hr1 : r_main = none := by rw [← hmain_r_none, hr_eq]
            have hc1 : c_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p) := by
              rw [← ih_p, hc_eq]
            have hl1 : l_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1)) := by
              rw [← ih_l, hl_eq]
            have h_rSim' : c_rSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) := by
              rw [← h_rSim, hc_eq]

            subst hr1 hc1 hl1 h_rSim'
            rw [hl_eq, hc_eq, hr_eq]
            simp only [borderNormalizeCA, Option.getD_some, Option.getD_none]
          · -- Left neighbor was NOT in zone
            have h_l_far : (p - 1) + t < 0 := by omega
            have hmain_l_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1)).1 = none :=
              borderNormalizeCA_far_left_none C b₁ b₂ w t (p - 1) h_l_far
            have h_r_far : (p + 1) - t ≥ w.length := by omega
            have hmain_r_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1)).1 = none :=
              borderNormalizeCA_far_right_none C b₁ b₂ w t (p + 1) h_r_far
            have ih_p := ih p (by omega) (by omega)

            -- Both lSim and rSim invariants apply in this case (same as Case 2b isolated)
            have h_lSim := borderNormalizeCA_lSim_invariant C b₁ b₂ w t p (by omega) (by omega)
            have h_rSim := borderNormalizeCA_rSim_invariant C b₁ b₂ w hw t p (by omega) (by omega)

            -- Destructure the triples
            obtain ⟨l_main, l_lSim, l_rSim, hl_eq⟩ :
              ∃ (l_m : C.Q？) (l_ls l_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1) = (l_m, l_ls, l_rs) :=
              ⟨_, _, _, rfl⟩
            obtain ⟨c_main, c_lSim, c_rSim, hc_eq⟩ :
              ∃ (c_m : C.Q？) (c_ls c_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p = (c_m, c_ls, c_rs) :=
              ⟨_, _, _, rfl⟩
            obtain ⟨r_main, r_lSim, r_rSim, hr_eq⟩ :
              ∃ (r_m : C.Q？) (r_ls r_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1) = (r_m, r_ls, r_rs) :=
              ⟨_, _, _, rfl⟩

            have hl1 : l_main = none := by rw [← hmain_l_none, hl_eq]
            have hr1 : r_main = none := by rw [← hmain_r_none, hr_eq]
            have hc1 : c_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p) := by
              rw [← ih_p, hc_eq]
            have h_lSim' : c_lSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1) := by
              rw [← h_lSim, hc_eq]
            have h_rSim' : c_rSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) := by
              rw [← h_rSim, hc_eq]

            subst hl1 hr1 hc1 h_lSim' h_rSim'
            rw [hl_eq, hc_eq, hr_eq]
            simp only [borderNormalizeCA, Option.getD_some, Option.getD_none]

        · -- Case 4: p was outside the zone at time t, activates at t+1
          have h_outside : p + t < 0 ∨ p - t ≥ w.length := by
            -- From not being in interior and not at either boundary, derive contradiction if in zone
            by_contra h_all_neg
            push_neg at h_all_neg
            -- h_all_neg: p + t ≥ 0 ∧ p - t < w.length (was in zone at time t)
            -- Since p + t ≠ 0 (from h_left_bdy), we have p + t > 0
            have hpt_pos : p + t > 0 := by omega
            -- From h_in_interior and hpt_pos: w.length - 1 ≤ p - t
            have hpt_large : w.length - 1 ≤ p - t := h_in_interior hpt_pos
            -- Combined with p - t ≠ w.length - 1: p - t > w.length - 1
            -- But p - t < w.length, so w.length - 1 < p - t < w.length
            -- This is impossible for integers
            omega

          rcases h_outside with h_left_border | h_right_border
          · -- Activating from left border
            have hpt : p + t = -1 := by omega
            have hmain_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).1 = none :=
              borderNormalizeCA_far_left_none C b₁ b₂ w t p h_left_border
            have h_r_left : (p + 1) + t ≥ 0 := by omega
            have h_r_right : (p + 1) - t < w.length := by omega
            have ih_r := ih (p + 1) h_r_left h_r_right
            have h_l_far : (p - 1) + t < 0 := by omega
            have hmain_l_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1)).1 = none :=
              borderNormalizeCA_far_left_none C b₁ b₂ w t (p - 1) h_l_far
            have h_lSim := borderNormalizeCA_lSim_invariant C b₁ b₂ w t p (by omega) (by omega)
            have heq : C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1) =
                       C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p :=
              bordered_config_left_region_eq C b₁ b₂ w t (p - 1) p (by omega) (by omega)

            -- Destructure the triples
            obtain ⟨l_main, l_lSim, l_rSim, hl_eq⟩ :
              ∃ (l_m : C.Q？) (l_ls l_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1) = (l_m, l_ls, l_rs) :=
              ⟨_, _, _, rfl⟩
            obtain ⟨c_main, c_lSim, c_rSim, hc_eq⟩ :
              ∃ (c_m : C.Q？) (c_ls c_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p = (c_m, c_ls, c_rs) :=
              ⟨_, _, _, rfl⟩
            obtain ⟨r_main, r_lSim, r_rSim, hr_eq⟩ :
              ∃ (r_m : C.Q？) (r_ls r_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1) = (r_m, r_ls, r_rs) :=
              ⟨_, _, _, rfl⟩

            have hl1 : l_main = none := by rw [← hmain_l_none, hl_eq]
            have hc1 : c_main = none := by rw [← hmain_none, hc_eq]
            have hr1 : r_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1)) := by
              rw [← ih_r, hr_eq]
            have h_lSim' : c_lSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1) := by
              rw [← h_lSim, hc_eq]

            subst hl1 hc1 hr1 h_lSim'
            rw [hl_eq, hc_eq, hr_eq, heq]
            simp only [borderNormalizeCA, Option.isSome_some, Option.getD_some, Option.getD_none, ↓reduceIte]

          · -- Activating from right border
            have hpt : p - t = w.length := by omega
            have hmain_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).1 = none :=
              borderNormalizeCA_far_right_none C b₁ b₂ w t p h_right_border
            have h_l_left : (p - 1) + t ≥ 0 := by omega
            have h_l_right : (p - 1) - t < w.length := by omega
            have ih_l := ih (p - 1) h_l_left h_l_right
            have h_r_far : (p + 1) - t ≥ w.length := by omega
            have hmain_r_none : ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1)).1 = none :=
              borderNormalizeCA_far_right_none C b₁ b₂ w t (p + 1) h_r_far
            have h_rSim := borderNormalizeCA_rSim_invariant C b₁ b₂ w hw t p (by omega) (by omega)
            have heq : C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) =
                       C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p :=
              bordered_config_right_region_eq C b₁ b₂ w t (p + 1) p (by omega) (by omega)

            -- Destructure the triples
            obtain ⟨l_main, l_lSim, l_rSim, hl_eq⟩ :
              ∃ (l_m : C.Q？) (l_ls l_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p - 1) = (l_m, l_ls, l_rs) :=
              ⟨_, _, _, rfl⟩
            obtain ⟨c_main, c_lSim, c_rSim, hc_eq⟩ :
              ∃ (c_m : C.Q？) (c_ls c_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p = (c_m, c_ls, c_rs) :=
              ⟨_, _, _, rfl⟩
            obtain ⟨r_main, r_lSim, r_rSim, hr_eq⟩ :
              ∃ (r_m : C.Q？) (r_ls r_rs : C.Q),
                (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (p + 1) = (r_m, r_ls, r_rs) :=
              ⟨_, _, _, rfl⟩

            have hl1 : l_main = some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p - 1)) := by
              rw [← ih_l, hl_eq]
            have hc1 : c_main = none := by rw [← hmain_none, hc_eq]
            have hr1 : r_main = none := by rw [← hmain_r_none, hr_eq]
            have h_rSim' : c_rSim = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (p + 1) := by
              rw [← h_rSim, hc_eq]

            subst hl1 hc1 hr1 h_rSim'
            rw [hl_eq, hc_eq, hr_eq, heq]
            -- Goal: (if false = true then ... else X).1 = X
            -- Simplify the if-then-else first
            simp only [borderNormalizeCA, ↓reduceIte, Option.isSome_some, Option.getD_some]
            -- Try to finish with rfl or simp
            rfl

/--
Interior positions (0 ≤ p < |w|) have main tracking the bordered config.
Interior positions are always active (main = some) and track correctly.
-/
lemma borderNormalizeCA_interior_main {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ)
    (hp0 : 0 ≤ p) (hpw : p < w.length) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t p).1 =
      some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t p) := by
  exact borderNormalizeCA_main_general C b₁ b₂ w hw t p (by omega) (by omega)

/--
Left border position -1 tracks the bordered config when activated (t ≥ 1).
-/
lemma borderNormalizeCA_posNeg1_main {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (hw : w ≠ []) (t : ℕ) (ht : t ≥ 1) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t (-1)).1 =
      some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t (-1)) := by
  have hw_pos : w.length > 0 := List.length_pos_of_ne_nil hw
  exact borderNormalizeCA_main_general C b₁ b₂ w hw t (-1) (by omega) (by omega)

/--
Main tracking for position 0: the main component tracks the bordered config evolution.
This is proven by showing that effective neighbors match the bordered config at each step.
-/
lemma borderNormalizeCA_pos0_main {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (hw : w ≠ []) (t : ℕ) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t 0).1 =
      some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t 0) := by
  have hw_pos : w.length > 0 := List.length_pos_of_ne_nil hw
  exact borderNormalizeCA_main_general C b₁ b₂ w hw t 0 (by omega) (by omega)

/--
Main correspondence lemma: position 0's main component tracks the bordered config.
-/
lemma borderNormalizeCA_main_eq {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (hw : w ≠ []) (t : ℕ) :
    ((borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t 0).1 =
      some (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t 0) :=
  borderNormalizeCA_pos0_main C b₁ b₂ w hw t

/--
**Border Normalization (non-existential)**: `borderNormalizeCA C b₁ b₂` on standard word
embedding equals `C` on bordered config.
-/
theorem borderNormalizeCA_trace {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) (w : Word α) (hw : w ≠ []) :
    (borderNormalizeCA C b₁ b₂).trace w = C.trace (BorderedConfig b₁ [] w b₂) := by
  -- Prove trace equality by showing they agree at all time steps
  funext t
  -- Unfold trace definitions
  unfold CellAutomaton.trace CellAutomaton.comp CellAutomaton.project_config
  simp only [Function.comp_apply]

  -- Use the main correspondence lemma
  have hmain := borderNormalizeCA_main_eq C b₁ b₂ w hw t

  -- The projection of borderNormalizeCA uses main.getD lSim
  -- Since main = some q, this gives C.project q
  set state := (borderNormalizeCA C b₁ b₂).nextt ⦋⟬w⟭⦌ t 0 with hstate

  -- The project function for borderNormalizeCA:
  -- project (main, lSim, _) = C.project (main.getD lSim)
  show (borderNormalizeCA C b₁ b₂).project state = C.project (C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t 0)

  -- Unfold project definition
  simp only [borderNormalizeCA]

  -- Since state.1 = some X, we have state.1.getD y = X for any y
  have h : state.1.getD state.2.1 = C.nextt ⦋BorderedConfig b₁ [] w b₂⦌ t 0 := by
    rw [hmain]
    rfl
  rw [h]

/--
**Border Normalization**: For any CA `C` and borders `b₁`, `b₂`, there exists a CA `C'`
such that `C'` on standard word embedding equals `C` on bordered config.
-/
theorem border_normalize {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (b₁ b₂ : α) :
    ∃ (C' : CellAutomaton α？ β),
      ∀ (w : Word α), w ≠ [] →
        C'.trace w = C.trace (BorderedConfig b₁ [] w b₂) :=
  ⟨borderNormalizeCA C b₁ b₂, borderNormalizeCA_trace C b₁ b₂⟩


end CellularAutomatas
