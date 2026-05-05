/-
  Mazoyer FSSP -- "no firing before time `2n − 2`" invariants.

  The Coq formalization (`final.v`) only proves the *forward* direction
  (every cell `0..n−1` IS `F` at time `2n−2`).  The Lean spec
  `SolvesFSSPOptimal` requires an `↔`, so we additionally need:

      `∀ t < 2n − 2, ∀ x ∈ [0, n − 1], Etat n t x ≠ F`.

  This file establishes the building blocks of that proof:

  * `Couleur` decidability gives `K ≠ F` for every non-F state `K`.
    Hence every cell whose state is named by an `A_Etat`/`B_Etat`/...
    /`G_Etat`/`L_Etat` predicate is automatically not `F`.
  * **`Diag` non-F** (`Diag_not_F`, `Diag'_not_F`) -- pointwise non-F
    along the antidiagonal of a `Diag`/`Diag'` whose `P`, `Q` (`Q'`),
    `R` predicates all imply `≠ F`.
  * **Brick non-F** (`A_basic_not_F`, `B_basic_not_F`, `C_basic_not_F`)
    -- pointwise non-F along the two diagonals each brick covers.
  * **Staircase non-F** (`un_end_g0_ne` … `cinq_end_g1_ne`) -- pointwise
    non-F for every cell *named directly* in the staircase predicate's
    fields.
  * **Early quiet zone** (`early_quiet_zone`) -- below the initial
    `L^(n − 1)` row at `t = 0`, the entire downward triangle stays `L`.
    This is `Hor_tr_inf` applied to `base1`'s tail.
  * **DD wedge non-F** (`DD_not_F`, `sorry`) -- the genuinely hard
    inductive lemma; see the comment on the lemma for what's missing.
  * **Final assembly** (`not_fire_before`, `sorry`) -- partition the
    rectangle `[0, n − 1] × [0, 2n − 3]` into

      * the initial row (covered by `init`),
      * the early quiet zone (covered by `early_quiet_zone`),
      * the global synchronization wedge (covered by `DD_not_F`
        applied to the `diagonale` from `final.lean`), and
      * the apex row at `t = 2n − 3` (covered by `sommet_1`, which is
        all `G`).
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.double_diag
import CellularAutomatas.proofs.constructions.fssp_mazoyer.vertical
import CellularAutomatas.proofs.constructions.fssp_mazoyer.final
import Mathlib.Tactic.IntervalCases

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

/-! ### Couleur ≠ F facts

Every non-`F` state is decidably not `F`. Combined with a `K_Etat`
hypothesis (which unfolds to `Etat n t x = K`), this gives the
`Etat n t x ≠ F` we need everywhere below.

`n` is `{implicit}` here so these lemmas can be passed as functions
to the higher-level `Diag_not_F` combinator. -/

private lemma A_ne_F : (A : Couleur) ≠ F := by decide
private lemma B_ne_F : (B : Couleur) ≠ F := by decide
private lemma C_ne_F : (C : Couleur) ≠ F := by decide
private lemma L_ne_F : (L : Couleur) ≠ F := by decide
private lemma G_ne_F : (G : Couleur) ≠ F := by decide

lemma A_Etat_ne_F {n : ℕ} {t : ℕ} {x : ℤ} (h : A_Etat n t x) :
    Etat n t x ≠ F := by
  rw [show Etat n t x = A from h]; exact A_ne_F

lemma B_Etat_ne_F {n : ℕ} {t : ℕ} {x : ℤ} (h : B_Etat n t x) :
    Etat n t x ≠ F := by
  rw [show Etat n t x = B from h]; exact B_ne_F

lemma C_Etat_ne_F {n : ℕ} {t : ℕ} {x : ℤ} (h : C_Etat n t x) :
    Etat n t x ≠ F := by
  rw [show Etat n t x = C from h]; exact C_ne_F

lemma L_Etat_ne_F {n : ℕ} {t : ℕ} {x : ℤ} (h : L_Etat n t x) :
    Etat n t x ≠ F := by
  rw [show Etat n t x = L from h]; exact L_ne_F

lemma G_Etat_ne_F {n : ℕ} {t : ℕ} {x : ℤ} (h : G_Etat n t x) :
    Etat n t x ≠ F := by
  rw [show Etat n t x = G from h]; exact G_ne_F

/-! ### Diag pointwise non-F

A `Diag t x cote P Q R` covers cells along the antidiagonal
`{(t + dt, x + dx) : dt + dx = cote, 0 ≤ dt, 0 ≤ dx ≤ cote}`. Apex at
`dt = 0`, bottom-left vertex at `dt = cote`, interior in between. If
`P`, `Q`, `R` are all non-F predicates, every such cell is non-F. -/

lemma Diag_not_F {n : ℕ} {t : ℕ} {x : ℤ} {cote : ℕ}
    {P Q R : Local_Prop}
    (hP : ∀ {t' : ℕ} {x' : ℤ}, P t' x' → Etat n t' x' ≠ F)
    (hQ : ∀ {t' : ℕ} {x' : ℤ}, Q t' x' → Etat n t' x' ≠ F)
    (hR : ∀ {t' : ℕ} {x' : ℤ}, R t' x' → Etat n t' x' ≠ F)
    (h : Diag t x cote P Q R)
    (dt dx : ℕ) (hsum : dt + dx = cote) :
    Etat n (t + dt) (x + dx) ≠ F := by
  rcases Nat.eq_zero_or_pos dt with hdt | hdt
  · -- Apex
    have hdx : dx = cote := by omega
    subst hdt; subst hdx
    have e : (t + 0 : ℕ) = t := by omega
    rw [e]
    exact hP h.apex
  · rcases Nat.eq_zero_or_pos dx with hdx | hdx
    · -- Bottom-left
      have hdt' : dt = cote := by omega
      subst hdx; subst hdt'
      have e : (x + ((0 : ℕ) : ℤ)) = x := by push_cast; ring
      rw [e]
      exact hR h.bottomLeft
    · -- Interior
      exact hQ (h.interior dt dx hdt hdx hsum)

/-- `Diag'` analogue. -/
lemma Diag'_not_F {n : ℕ} {t : ℕ} {x : ℤ} {cote : ℕ}
    {P Q' Q R : Local_Prop}
    (hP : ∀ {t' : ℕ} {x' : ℤ}, P t' x' → Etat n t' x' ≠ F)
    (hQ' : ∀ {t' : ℕ} {x' : ℤ}, Q' t' x' → Etat n t' x' ≠ F)
    (hQ : ∀ {t' : ℕ} {x' : ℤ}, Q t' x' → Etat n t' x' ≠ F)
    (hR : ∀ {t' : ℕ} {x' : ℤ}, R t' x' → Etat n t' x' ≠ F)
    (h : Diag' t x cote P Q' Q R)
    (dt dx : ℕ) (hsum : dt + dx = cote) :
    Etat n (t + dt) (x + dx) ≠ F := by
  rcases Nat.eq_zero_or_pos dt with hdt | hdt
  · have hdx : dx = cote := by omega
    subst hdt; subst hdx
    have e : (t + 0 : ℕ) = t := by omega
    rw [e]
    exact hP h.apex
  · rcases Nat.eq_zero_or_pos dx with hdx | hdx
    · have hdt' : dt = cote := by omega
      subst hdx; subst hdt'
      have e : (x + ((0 : ℕ) : ℤ)) = x := by push_cast; ring
      rw [e]
      exact hR h.bottomLeft
    · rcases Nat.lt_or_ge 1 dt with hdt1 | hdt1
      · exact hQ (h.interior dt dx hdt1 hdx hsum)
      · have hdt1' : dt = 1 := by omega
        subst hdt1'
        have hdx_succ : dx + 1 = cote := by omega
        exact hQ' (h.topRow dx hdx_succ)

/-! ### Brick non-F

Each `*_basic` brick of side `cote` carries two diagonals:

  * `diag0` covers cells with `dt + dx = cote`, `dt ∈ [0, cote]`.
  * `diag1` covers cells with `(dt − 1) + dx = cote`, `dt ∈ [1, cote + 1]`.

The lemmas below cover exactly this set, requiring `dt ≥ 1` for the
second diagonal. -/

variable (n : ℕ)

lemma A_basic_not_F {t : ℕ} {x : ℤ} {cote : ℕ}
    (h : A_basic n t x cote) (dt dx : ℕ)
    (hd : dt + dx = cote ∨ (1 ≤ dt ∧ dt + dx = cote + 1)) :
    Etat n (t + dt) (x + dx) ≠ F := by
  rcases hd with hd | ⟨hdt, hd⟩
  · exact Diag_not_F
      (P := L_Etat n) (Q := A_Etat n) (R := L_Etat n)
      L_Etat_ne_F A_Etat_ne_F L_Etat_ne_F h.diag0 dt dx hd
  · obtain ⟨dt', rfl⟩ : ∃ dt', dt = dt' + 1 := ⟨dt - 1, by omega⟩
    have hsum' : dt' + dx = cote := by omega
    have hcell : Etat n ((t + 1) + dt') (x + dx) ≠ F :=
      Diag_not_F
        (P := L_Etat n) (Q := A_Etat n) (R := L_Etat n)
        L_Etat_ne_F A_Etat_ne_F L_Etat_ne_F h.diag1 dt' dx hsum'
    have e : (t + (dt' + 1) : ℕ) = (t + 1) + dt' := by omega
    rw [e]; exact hcell

lemma B_basic_not_F {t : ℕ} {x : ℤ} {cote : ℕ}
    (h : B_basic n t x cote) (dt dx : ℕ)
    (hd : dt + dx = cote ∨ (1 ≤ dt ∧ dt + dx = cote + 1)) :
    Etat n (t + dt) (x + dx) ≠ F := by
  rcases hd with hd | ⟨hdt, hd⟩
  · exact Diag'_not_F
      (P := L_Etat n) (Q' := G_Etat n) (Q := B_Etat n) (R := L_Etat n)
      L_Etat_ne_F G_Etat_ne_F B_Etat_ne_F L_Etat_ne_F
      h.diag0 dt dx hd
  · obtain ⟨dt', rfl⟩ : ∃ dt', dt = dt' + 1 := ⟨dt - 1, by omega⟩
    have hsum' : dt' + dx = cote := by omega
    have hcell : Etat n ((t + 1) + dt') (x + dx) ≠ F :=
      Diag_not_F
        (P := L_Etat n) (Q := B_Etat n) (R := L_Etat n)
        L_Etat_ne_F B_Etat_ne_F L_Etat_ne_F h.diag1 dt' dx hsum'
    have e : (t + (dt' + 1) : ℕ) = (t + 1) + dt' := by omega
    rw [e]; exact hcell

lemma C_basic_not_F {t : ℕ} {x : ℤ} {cote : ℕ}
    (h : C_basic n t x cote) (dt dx : ℕ)
    (hd : dt + dx = cote ∨ (1 ≤ dt ∧ dt + dx = cote + 1)) :
    Etat n (t + dt) (x + dx) ≠ F := by
  rcases hd with hd | ⟨hdt, hd⟩
  · exact Diag_not_F
      (P := L_Etat n) (Q := C_Etat n) (R := L_Etat n)
      L_Etat_ne_F C_Etat_ne_F L_Etat_ne_F h.diag0 dt dx hd
  · obtain ⟨dt', rfl⟩ : ∃ dt', dt = dt' + 1 := ⟨dt - 1, by omega⟩
    have hsum' : dt' + dx = cote := by omega
    have hcell : Etat n ((t + 1) + dt') (x + dx) ≠ F :=
      Diag_not_F
        (P := L_Etat n) (Q := C_Etat n) (R := L_Etat n)
        L_Etat_ne_F C_Etat_ne_F L_Etat_ne_F h.diag1 dt' dx hsum'
    have e : (t + (dt' + 1) : ℕ) = (t + 1) + dt' := by omega
    rw [e]; exact hcell

/-! ### Staircase non-F (named cells)

For each level `un_end` … `cinq_end`, every cell named directly in
its struct fields is non-F. (Cells of the wedge that are *not* named
in any field, e.g. `(t, x)` for `quatre_end n t x`, are not addressed
by these lemmas.) -/

lemma un_end_g0_ne {t : ℕ} {x : ℤ} (h : un_end n t x) :
    Etat n t x ≠ F := G_Etat_ne_F h.g0
lemma un_end_g1_ne {t : ℕ} {x : ℤ} (h : un_end n t x) :
    Etat n (t + 1) x ≠ F := G_Etat_ne_F h.g1

lemma deux_end_c1_ne {t : ℕ} {x : ℤ} (h : deux_end n t x) :
    Etat n t (x + 1) ≠ F := C_Etat_ne_F h.c1
lemma deux_end_b1_ne {t : ℕ} {x : ℤ} (h : deux_end n t x) :
    Etat n (t + 1) (x + 1) ≠ F := B_Etat_ne_F h.b1
lemma deux_end_g0_ne {t : ℕ} {x : ℤ} (h : deux_end n t x) :
    Etat n (t + 1) x ≠ F := G_Etat_ne_F h.one.g0
lemma deux_end_g1_ne {t : ℕ} {x : ℤ} (h : deux_end n t x) :
    Etat n (t + 2) x ≠ F := G_Etat_ne_F h.one.g1

lemma trois_end_a2_ne {t : ℕ} {x : ℤ} (h : trois_end n t x) :
    Etat n t (x + 2) ≠ F := A_Etat_ne_F h.a2
lemma trois_end_g2_ne {t : ℕ} {x : ℤ} (h : trois_end n t x) :
    Etat n (t + 1) (x + 2) ≠ F := G_Etat_ne_F h.g2
lemma trois_end_c1_ne {t : ℕ} {x : ℤ} (h : trois_end n t x) :
    Etat n (t + 1) (x + 1) ≠ F := C_Etat_ne_F h.two.c1
lemma trois_end_b1_ne {t : ℕ} {x : ℤ} (h : trois_end n t x) :
    Etat n (t + 2) (x + 1) ≠ F := B_Etat_ne_F h.two.b1
lemma trois_end_g0_ne {t : ℕ} {x : ℤ} (h : trois_end n t x) :
    Etat n (t + 2) x ≠ F := G_Etat_ne_F h.two.one.g0
lemma trois_end_g1_ne {t : ℕ} {x : ℤ} (h : trois_end n t x) :
    Etat n (t + 3) x ≠ F := G_Etat_ne_F h.two.one.g1

lemma quatre_end_l3a_ne {t : ℕ} {x : ℤ} (h : quatre_end n t x) :
    Etat n t (x + 3) ≠ F := L_Etat_ne_F h.l3a
lemma quatre_end_l3b_ne {t : ℕ} {x : ℤ} (h : quatre_end n t x) :
    Etat n (t + 1) (x + 3) ≠ F := L_Etat_ne_F h.l3b
lemma quatre_end_a2_ne {t : ℕ} {x : ℤ} (h : quatre_end n t x) :
    Etat n (t + 1) (x + 2) ≠ F := A_Etat_ne_F h.three.a2
lemma quatre_end_g2_ne {t : ℕ} {x : ℤ} (h : quatre_end n t x) :
    Etat n (t + 2) (x + 2) ≠ F := G_Etat_ne_F h.three.g2
lemma quatre_end_c1_ne {t : ℕ} {x : ℤ} (h : quatre_end n t x) :
    Etat n (t + 2) (x + 1) ≠ F := C_Etat_ne_F h.three.two.c1
lemma quatre_end_b1_ne {t : ℕ} {x : ℤ} (h : quatre_end n t x) :
    Etat n (t + 3) (x + 1) ≠ F := B_Etat_ne_F h.three.two.b1
lemma quatre_end_g0_ne {t : ℕ} {x : ℤ} (h : quatre_end n t x) :
    Etat n (t + 3) x ≠ F := G_Etat_ne_F h.three.two.one.g0
lemma quatre_end_g1_ne {t : ℕ} {x : ℤ} (h : quatre_end n t x) :
    Etat n (t + 4) x ≠ F := G_Etat_ne_F h.three.two.one.g1

lemma cinq_end_l4a_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n t (x + 4) ≠ F := L_Etat_ne_F h.l4a
lemma cinq_end_l4b_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 1) (x + 4) ≠ F := L_Etat_ne_F h.l4b
lemma cinq_end_g3_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 1) (x + 3) ≠ F := G_Etat_ne_F h.g3
lemma cinq_end_b3_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 2) (x + 3) ≠ F := B_Etat_ne_F h.b3
lemma cinq_end_a2_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 2) (x + 2) ≠ F := A_Etat_ne_F h.three.a2
lemma cinq_end_g2_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 3) (x + 2) ≠ F := G_Etat_ne_F h.three.g2
lemma cinq_end_c1_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 3) (x + 1) ≠ F := C_Etat_ne_F h.three.two.c1
lemma cinq_end_b1_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 4) (x + 1) ≠ F := B_Etat_ne_F h.three.two.b1
lemma cinq_end_g0_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 4) x ≠ F := G_Etat_ne_F h.three.two.one.g0
lemma cinq_end_g1_ne {t : ℕ} {x : ℤ} (h : cinq_end n t x) :
    Etat n (t + 5) x ≠ F := G_Etat_ne_F h.three.two.one.g1

/-! ### Early quiet zone

`base1` from `final.lean` gives a `Horizontale_t0` row at `t = 0`:
`G` at column 0 followed by `n − 2` `L`s at columns `1..n − 1`. The
*tail* of that row is a plain `Horizontale 0 1 (n − 2) L`, which by
`Hor_tr_inf` extends downward as a triangle of `L`s. Every cell of
this triangle is therefore non-F.

The triangle covers cells `(dt, 1 + dx)` with `0 ≤ dt ≤ dx ≤ n − 2`.
Translating back to the original coordinates:

  `(t, x)` is in the triangle iff `1 ≤ x ≤ n − 1` and `0 ≤ t ≤ x − 1`.

This is the dominant region "above" the synchronization wedge in the
left half of the array. -/

lemma early_quiet_zone (h : 4 ≤ n) :
    Triangle_inf 0 (1 : ℤ) (n - 2) (L_Etat n) := by
  have hb := base1 n h
  have hbt : Horizontale 0 (1 : ℤ) (n - 2) (L_Etat n) := by
    have e : (0 : ℤ) + 1 = (1 : ℤ) := by ring
    have := hb.tail
    rw [e] at this
    exact this
  exact Hor_tr_inf n 0 1 (n - 2) hbt

lemma early_quiet_zone_not_F (h : 4 ≤ n) (dt dx : ℕ)
    (hdx : dx ≤ n - 2) (hdt : dt ≤ dx) :
    Etat n (0 + dt) ((1 : ℤ) + dx) ≠ F :=
  L_Etat_ne_F ((early_quiet_zone n h).pointwise dt dx hdx hdt)

/-! ### `DD` wedge non-F

The cells `(t + dt, x + dx)` covered by the structural fields of
`DD t x cote` lie on **two anti-diagonals**:

    `dx ≤ cote ∧ (dt + dx = cote ∨ dt + dx = cote + 1)`.

This is consistent across all `DD` constructors:

  * `DD_4` / `DD_5` (base): the staircase predicate `quatre_end` /
    `cinq_end` names exactly the cells on these two anti-diagonals
    (verified by inspection of the field positions).
  * `DD_A` (`cote = 3k`, `k = tiers cote`): brick `A_basic` of side
    `k + 1` at column-offset `2k − 1` covers `dx ∈ [2k − 1, 3k]`;
    sub-DD of side `2k − 1` covers `dx < 2k − 1`. Both contribute
    cells with `dt + dx ∈ {cote, cote + 1}`.
  * `DD_B` / `DD_C` (analogous shifts).

The proof is structural induction on `DD`. Base cases dispatch to
the `*_end_*_ne` staircase lemmas; inductive cases case-split on
`dx` (in brick range vs sub-DD range) and apply `*_basic_not_F` /
the IH respectively. -/

lemma DD_not_F : ∀ {t : ℕ} {x : ℤ} {cote : ℕ},
    DD n t x cote →
    ∀ (dt dx : ℕ), dx ≤ cote → (dt + dx = cote ∨ dt + dx = cote + 1) →
      Etat n (t + dt) (x + dx) ≠ F := by
  intro t x cote h
  induction h with
  | DD_4 t x hq =>
    -- cote = 3, base: quatre_end n t x. Eight cells, eight cases.
    intro dt dx hdx hsum
    interval_cases dx <;> rcases hsum with hs | hs
    -- dx = 0, dt + 0 ∈ {3, 4}
    · have hd : dt = 3 := by omega
      subst hd
      have e : (x + ((0 : ℕ) : ℤ)) = x := by push_cast; ring
      rw [e]; exact quatre_end_g0_ne n hq
    · have hd : dt = 4 := by omega
      subst hd
      have e : (x + ((0 : ℕ) : ℤ)) = x := by push_cast; ring
      rw [e]; exact quatre_end_g1_ne n hq
    -- dx = 1, dt + 1 ∈ {3, 4}
    · have hd : dt = 2 := by omega
      subst hd
      have e : (x + ((1 : ℕ) : ℤ)) = x + 1 := by push_cast; ring
      rw [e]; exact quatre_end_c1_ne n hq
    · have hd : dt = 3 := by omega
      subst hd
      have e : (x + ((1 : ℕ) : ℤ)) = x + 1 := by push_cast; ring
      rw [e]; exact quatre_end_b1_ne n hq
    -- dx = 2, dt + 2 ∈ {3, 4}
    · have hd : dt = 1 := by omega
      subst hd
      have e : (x + ((2 : ℕ) : ℤ)) = x + 2 := by push_cast; ring
      rw [e]; exact quatre_end_a2_ne n hq
    · have hd : dt = 2 := by omega
      subst hd
      have e : (x + ((2 : ℕ) : ℤ)) = x + 2 := by push_cast; ring
      rw [e]; exact quatre_end_g2_ne n hq
    -- dx = 3, dt + 3 ∈ {3, 4}
    · have hd : dt = 0 := by omega
      subst hd
      have e : (x + ((3 : ℕ) : ℤ)) = x + 3 := by push_cast; ring
      have e2 : (t + 0 : ℕ) = t := by omega
      rw [e2, e]; exact quatre_end_l3a_ne n hq
    · have hd : dt = 1 := by omega
      subst hd
      have e : (x + ((3 : ℕ) : ℤ)) = x + 3 := by push_cast; ring
      rw [e]; exact quatre_end_l3b_ne n hq
  | DD_5 t x hc =>
    -- cote = 4, base: cinq_end n t x. Ten cells, ten cases.
    intro dt dx hdx hsum
    interval_cases dx <;> rcases hsum with hs | hs
    -- dx = 0, dt ∈ {4, 5}
    · have hd : dt = 4 := by omega
      subst hd
      have e : (x + ((0 : ℕ) : ℤ)) = x := by push_cast; ring
      rw [e]; exact cinq_end_g0_ne n hc
    · have hd : dt = 5 := by omega
      subst hd
      have e : (x + ((0 : ℕ) : ℤ)) = x := by push_cast; ring
      rw [e]; exact cinq_end_g1_ne n hc
    -- dx = 1, dt ∈ {3, 4}
    · have hd : dt = 3 := by omega
      subst hd
      have e : (x + ((1 : ℕ) : ℤ)) = x + 1 := by push_cast; ring
      rw [e]; exact cinq_end_c1_ne n hc
    · have hd : dt = 4 := by omega
      subst hd
      have e : (x + ((1 : ℕ) : ℤ)) = x + 1 := by push_cast; ring
      rw [e]; exact cinq_end_b1_ne n hc
    -- dx = 2, dt ∈ {2, 3}
    · have hd : dt = 2 := by omega
      subst hd
      have e : (x + ((2 : ℕ) : ℤ)) = x + 2 := by push_cast; ring
      rw [e]; exact cinq_end_a2_ne n hc
    · have hd : dt = 3 := by omega
      subst hd
      have e : (x + ((2 : ℕ) : ℤ)) = x + 2 := by push_cast; ring
      rw [e]; exact cinq_end_g2_ne n hc
    -- dx = 3, dt ∈ {1, 2}
    · have hd : dt = 1 := by omega
      subst hd
      have e : (x + ((3 : ℕ) : ℤ)) = x + 3 := by push_cast; ring
      rw [e]; exact cinq_end_g3_ne n hc
    · have hd : dt = 2 := by omega
      subst hd
      have e : (x + ((3 : ℕ) : ℤ)) = x + 3 := by push_cast; ring
      rw [e]; exact cinq_end_b3_ne n hc
    -- dx = 4, dt ∈ {0, 1}
    · have hd : dt = 0 := by omega
      subst hd
      have e : (x + ((4 : ℕ) : ℤ)) = x + 4 := by push_cast; ring
      have e2 : (t + 0 : ℕ) = t := by omega
      rw [e2, e]; exact cinq_end_l4a_ne n hc
    · have hd : dt = 1 := by omega
      subst hd
      have e : (x + ((4 : ℕ) : ℤ)) = x + 4 := by push_cast; ring
      rw [e]; exact cinq_end_l4b_ne n hc
  | DD_A t x cote hcote hmod hbrick _hsub ihSub =>
    -- cote = 3k, brick at offset 2k - 1, sub-DD has cote 2k - 1, k = tiers cote.
    intro dt dx hdx hsum
    have hk : 2 ≤ tiers cote := le_tiers_six cote hcote
    have htriple : tiers cote + tiers cote + tiers cote = cote :=
      triple_tiers cote hmod
    have hdouble : double (tiers cote) = tiers cote + tiers cote := by
      unfold double; rfl
    by_cases hcase : 2 * tiers cote - 1 ≤ dx
    · -- Brick case: dx ∈ [2k - 1, 3k].
      obtain ⟨dx_b, hdxb⟩ : ∃ dx_b : ℕ, dx = (2 * tiers cote - 1) + dx_b :=
        ⟨dx - (2 * tiers cote - 1), by omega⟩
      -- Combine `dx = (2k - 1) + dx_b` (from hdxb) with `double k = k + k`
      -- (from hdouble) into a Nat equation.
      have hN : dx = (double (tiers cote) - 1) + dx_b := by
        rw [hdouble]; omega
      have hcell_eq :
          (x + (dx : ℤ)) =
            (x + ((double (tiers cote) - 1 : ℕ) : ℤ)) + (dx_b : ℤ) := by
        rw [hN]; push_cast; ring
      rw [hcell_eq]
      apply A_basic_not_F n hbrick dt dx_b
      rcases hsum with h1 | h1
      · left; omega
      · right; refine ⟨?_, ?_⟩ <;> omega
    · -- Sub-DD case: dx < 2k - 1.
      push_neg at hcase
      obtain ⟨dt', hdt_eq⟩ : ∃ dt' : ℕ, dt = (tiers cote + 1) + dt' :=
        ⟨dt - (tiers cote + 1), by omega⟩
      have hsub_dx : dx ≤ double (tiers cote) - 1 := by rw [hdouble]; omega
      have hsub_sum :
          dt' + dx = double (tiers cote) - 1 ∨
          dt' + dx = (double (tiers cote) - 1) + 1 := by
        rcases hsum with h1 | h1
        · left; rw [hdouble]; omega
        · right; rw [hdouble]; omega
      have hres :
          Etat n ((t + tiers cote + 1) + dt') (x + (dx : ℤ)) ≠ F :=
        ihSub dt' dx hsub_dx hsub_sum
      have ht_eq : (t + dt : ℕ) = (t + tiers cote + 1) + dt' := by
        rw [hdt_eq]; omega
      rw [ht_eq]; exact hres
  | DD_B t x cote hcote hmod hbrick _hsub ihSub =>
    -- cote = 3k + 1, brick at offset 2k, sub-DD has cote 2k, k = tiers cote.
    intro dt dx hdx hsum
    have hk : 2 ≤ tiers cote := le_tiers_six cote (by omega)
    have htriple : (tiers cote + tiers cote + tiers cote) + 1 = cote :=
      Striple_tiers cote hmod
    have hdouble : double (tiers cote) = tiers cote + tiers cote := by
      unfold double; rfl
    by_cases hcase : 2 * tiers cote ≤ dx
    · -- Brick case: dx ∈ [2k, 3k + 1].
      obtain ⟨dx_b, hdxb⟩ : ∃ dx_b : ℕ, dx = (2 * tiers cote) + dx_b :=
        ⟨dx - 2 * tiers cote, by omega⟩
      have hN : dx = double (tiers cote) + dx_b := by
        rw [hdouble]; omega
      have hcell_eq :
          (x + (dx : ℤ)) =
            (x + ((double (tiers cote) : ℕ) : ℤ)) + (dx_b : ℤ) := by
        rw [hN]; push_cast; ring
      rw [hcell_eq]
      apply B_basic_not_F n hbrick dt dx_b
      rcases hsum with h1 | h1
      · left; omega
      · right; refine ⟨?_, ?_⟩ <;> omega
    · -- Sub-DD case: dx < 2k.
      push_neg at hcase
      obtain ⟨dt', hdt_eq⟩ : ∃ dt' : ℕ, dt = (tiers cote + 1) + dt' :=
        ⟨dt - (tiers cote + 1), by omega⟩
      have hsub_dx : dx ≤ double (tiers cote) := by rw [hdouble]; omega
      have hsub_sum :
          dt' + dx = double (tiers cote) ∨
          dt' + dx = double (tiers cote) + 1 := by
        rcases hsum with h1 | h1
        · left; rw [hdouble]; omega
        · right; rw [hdouble]; omega
      have hres :
          Etat n ((t + tiers cote + 1) + dt') (x + (dx : ℤ)) ≠ F :=
        ihSub dt' dx hsub_dx hsub_sum
      have ht_eq : (t + dt : ℕ) = (t + tiers cote + 1) + dt' := by
        rw [hdt_eq]; omega
      rw [ht_eq]; exact hres
  | DD_C t x cote hcote hmod hbrick _hsub ihSub =>
    -- cote = 3k + 2, brick at offset 2k + 1, sub-DD has cote 2k + 1, k = tiers cote.
    intro dt dx hdx hsum
    have hk : 1 ≤ tiers cote := le_tiers_trois cote (by omega)
    have htriple : (tiers cote + tiers cote + tiers cote) + 2 = cote :=
      SStriple_tiers cote hmod
    have hdouble : double (tiers cote) = tiers cote + tiers cote := by
      unfold double; rfl
    by_cases hcase : 2 * tiers cote + 1 ≤ dx
    · -- Brick case: dx ∈ [2k + 1, 3k + 2].
      obtain ⟨dx_b, hdxb⟩ : ∃ dx_b : ℕ, dx = (2 * tiers cote + 1) + dx_b :=
        ⟨dx - (2 * tiers cote + 1), by omega⟩
      have hN : dx = (double (tiers cote) + 1) + dx_b := by
        rw [hdouble]; omega
      have hcell_eq :
          (x + (dx : ℤ)) =
            (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) + (dx_b : ℤ) := by
        rw [hN]; push_cast; ring
      rw [hcell_eq]
      apply C_basic_not_F n hbrick dt dx_b
      rcases hsum with h1 | h1
      · left; omega
      · right; refine ⟨?_, ?_⟩ <;> omega
    · -- Sub-DD case: dx < 2k + 1.
      push_neg at hcase
      obtain ⟨dt', hdt_eq⟩ : ∃ dt' : ℕ, dt = (tiers cote + 1) + dt' :=
        ⟨dt - (tiers cote + 1), by omega⟩
      have hsub_dx : dx ≤ double (tiers cote) + 1 := by rw [hdouble]; omega
      have hsub_sum :
          dt' + dx = double (tiers cote) + 1 ∨
          dt' + dx = (double (tiers cote) + 1) + 1 := by
        rcases hsum with h1 | h1
        · left; rw [hdouble]; omega
        · right; rw [hdouble]; omega
      have hres :
          Etat n ((t + tiers cote + 1) + dt') (x + (dx : ℤ)) ≠ F :=
        ihSub dt' dx hsub_dx hsub_sum
      have ht_eq : (t + dt : ℕ) = (t + tiers cote + 1) + dt' := by
        rw [hdt_eq]; omega
      rw [ht_eq]; exact hres

/-! ### Final assembly

For `0 ≤ x ≤ n − 1` and `t < 2n − 2`, every cell `(t, x)` is non-F.

**Coverage achieved by existing lemmas:**

  * `t = 0`: `base1` (G at x = 0; L for 1 ≤ x ≤ n − 1).
  * `1 ≤ t ≤ x − 1`, `1 ≤ x ≤ n − 1`: `early_quiet_zone` (all L).
  * `t = 2n − 3`: `sommet_1` (all G).
  * `Ht0_DD` family + `DD_not_F`: For each `m ∈ [0, n − 4]`, the wedge
    `DD n (1 + m) 0 (m + 3)` (from `Ht0_DD n 0 (n - 2) … base1 m`)
    covers cells `((1 + m) + δt, δx)` with `δx ≤ m + 3` and
    `δt + δx ∈ {m + 3, m + 4}`. In `(t, x)` coordinates:

      `t + x = 2m + 4` or `2m + 5`,  with  `x ≤ m + 3`, `m ≤ t − 1`.

    Equivalently: cell `(t, x)` is covered iff some valid `m` exists,
    i.e., `t + x ∈ [4, 2n − 3]` and `x ≤ ⌊(t + x − 2)/2⌋ + 1` (which
    simplifies to `x ≤ t + 1` for the odd case, `x ≤ t + 2` for even).

**Coverage gap (still requires `sorry`).** Two regions of the
rectangle `[0, n − 1] × [0, 2n − 3]` are not covered by the above:

  * **Left shadow** (small, `n`-independent): cells with `t + x ≤ 3`
    and `x ≤ t`. Concretely `(1, 0)`, `(1, 1)`, `(2, 0)`, `(2, 1)`,
    `(3, 0)`. These are determined by `init` and 1–3 `δ` steps and
    can be discharged by direct computation, but require a new lemma
    (e.g., a `Ht0_End2`-style export of `deux_end n 1 0` from
    `base1`, plus a one-step `Etat n 1 0 = A` lemma).
  * **Right shadow**: cells with `t + x ∈ [2n − 2, 3n − 4]` and
    `t ≤ 2n − 4` and `x ≤ n − 1`. For `n = 4`: `(3, 3)`, `(4, 2)`,
    `(4, 3)`. These cells are "interior" to the global wedge but
    not on its outer two anti-diagonals — they're covered only by
    `Ht0_DD` members with `m ≥ 1`, which exist only for `n ≥ 5`.
    For `n = 4`, this region requires the right-side dynamics
    (analogous to `Ht0_DD` but anchored at the right phantom `base2`),
    which is not currently exported.

Both gaps are tractable with additional infrastructure but each needs
a new family of lemmas. The `omega`-trivial part is the geometric
case-split; the work is in surfacing the missing wedge families
and shadow-region computations. -/

lemma not_fire_before (h : 4 ≤ n) (t : ℕ) (ht : t < 2 * n - 2)
    (x : ℤ) (hx : 0 ≤ x) (hxn : x ≤ (n : ℤ) - 1) :
    Etat n t x ≠ F := by
  sorry

end FsspMazoyer
end CellularAutomatas
