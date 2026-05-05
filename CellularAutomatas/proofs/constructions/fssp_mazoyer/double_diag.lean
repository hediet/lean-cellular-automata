/-
  Mazoyer FSSP -- the recursive `DD` predicate (port of `double_diag.v`).
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.basic_bricks
import CellularAutomatas.proofs.constructions.fssp_mazoyer.border

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

variable (n : ℕ)

/-! ### The recursive wedge type `DD`

`DD n t x cote` says: starting at corner `(t, x)`, an entire wedge of
side `cote` performs synchronization correctly. It bottoms out at
`quatre_end` (cote = 3) / `cinq_end` (cote = 4), and recursively
combines a basic brick with a smaller `DD`.
-/

inductive DD : ℕ → ℤ → ℕ → Prop
  | DD_4 (t : ℕ) (x : ℤ) :
      quatre_end n t x → DD t x 3
  | DD_5 (t : ℕ) (x : ℤ) :
      cinq_end n t x → DD t x 4
  | DD_A (t : ℕ) (x : ℤ) (cote : ℕ) :
      6 ≤ cote →
      Omod3 cote →
      A_basic n t (x + (double (tiers cote) - 1 : ℕ)) (tiers cote + 1) →
      DD (t + tiers cote + 1) x (double (tiers cote) - 1) →
      DD t x cote
  | DD_B (t : ℕ) (x : ℤ) (cote : ℕ) :
      7 ≤ cote →
      Unmod3 cote →
      B_basic n t (x + (double (tiers cote) : ℕ)) (tiers cote + 1) →
      DD (t + tiers cote + 1) x (double (tiers cote)) →
      DD t x cote
  | DD_C (t : ℕ) (x : ℤ) (cote : ℕ) :
      5 ≤ cote →
      Deuxmod3 cote →
      C_basic n t (x + (double (tiers cote) + 1 : ℕ)) (tiers cote + 1) →
      DD (t + tiers cote + 1) x (double (tiers cote) + 1) →
      DD t x cote

/-- `DD` produces two consecutive `G`s at the bottom-left vertex.
    (Coq's `DD_GG`.)

    Strategy: induct on `DD`. The two base cases use `quatre_GG` /
    `cinq_GG` directly. Each recursive case, the IH provides two `G`s
    at the bottom-left of the *inner* (smaller) wedge -- by Omod3 / Unmod3
    / Deuxmod3 arithmetic, the inner-wedge's `t + side` equals the
    outer wedge's `t + cote`, so the IH already produces what we want
    after a single arithmetic rewrite. -/
lemma DD_GG (t : ℕ) (x : ℤ) (cote : ℕ) :
    DD n t x cote →
    G_Etat n (t + cote) x ∧ G_Etat n (t + cote + 1) x := by
  intro h
  induction h with
  | DD_4 t x h =>
      show G_Etat n (t + 3) x ∧ G_Etat n (t + 3 + 1) x
      exact quatre_GG n t x h
  | DD_5 t x h =>
      show G_Etat n (t + 4) x ∧ G_Etat n (t + 4 + 1) x
      exact cinq_GG n t x h
  | DD_A t x cote hle hmod _ _ ih =>
      have hpos : 1 ≤ double (tiers cote) := lt_O_deuxtiers cote (by omega)
      have hpd  : double (tiers cote) + tiers cote = cote :=
        plus_deuxtiers_untiers cote hmod
      have heq  : (t + tiers cote + 1) + (double (tiers cote) - 1) = t + cote := by
        omega
      rw [heq] at ih
      exact ih
  | DD_B t x cote _ hmod _ _ ih =>
      have hpd : (double (tiers cote) + tiers cote) + 1 = cote :=
        Splus_deuxtiers_untiers cote hmod
      have heq : (t + tiers cote + 1) + double (tiers cote) = t + cote := by omega
      rw [heq] at ih
      exact ih
  | DD_C t x cote _ hmod _ _ ih =>
      have hpd : (double (tiers cote) + tiers cote) + 2 = cote :=
        SSplus_deuxtiers_untiers cote hmod
      have heq : (t + tiers cote + 1) + (double (tiers cote) + 1) = t + cote := by
        omega
      rw [heq] at ih
      exact ih

/-! ### Closure under "two more L's in the trailing column" -/

/-- `DD` is preserved by extending the right edge with two `L` rows.
    Inducts on `DD`: each constructor either uses
    `quatre_quatre`/`cinq_cinq` (base cases) or applies the analogous
    `A_A`/`B_B`/`C_C` brick-iteration plus the IH. -/
theorem DD_hh (t : ℕ) (x : ℤ) (cote : ℕ) :
    DD n t x cote →
    L_Etat n (t + 2) (x + cote) →
    L_Etat n (t + 3) (x + cote) →
    DD n (t + 2) x cote := by
  intro hdd
  induction hdd with
  | DD_4 t x h =>
      intro hL1 hL2
      show DD n (t + 2) x 3
      exact DD.DD_4 (t + 2) x (quatre_quatre n t x h hL1 hL2)
  | DD_5 t x h =>
      intro hL1 hL2
      show DD n (t + 2) x 4
      exact DD.DD_5 (t + 2) x (cinq_cinq n t x h hL1 hL2)
  | DD_A t x cote hle hmod hA _ ih =>
      intro hL1 hL2
      have hpos : 1 ≤ double (tiers cote) := lt_O_deuxtiers cote (by omega)
      have hpd  : double (tiers cote) + tiers cote = cote :=
        plus_deuxtiers_untiers cote hmod
      have hcol :
          x + (cote : ℤ)
            = x + ((double (tiers cote) - 1 : ℕ) : ℤ) + ((tiers cote + 1 : ℕ) : ℤ) := by
        omega
      rw [hcol] at hL1 hL2
      have newA :
          A_basic n (t + 2) (x + ((double (tiers cote) - 1 : ℕ) : ℤ)) (tiers cote + 1) :=
        A_A n t (x + ((double (tiers cote) - 1 : ℕ) : ℤ)) (tiers cote + 1) hA hL1 hL2
      have newL1 :
          L_Etat n ((t + tiers cote + 1) + 2)
            (x + ((double (tiers cote) - 1 : ℕ) : ℤ)) := by
        have h := newA.diag0.bottomLeft
        have ht : (t + 2) + (tiers cote + 1) = (t + tiers cote + 1) + 2 := by omega
        rw [ht] at h
        exact h
      have newL2 :
          L_Etat n ((t + tiers cote + 1) + 3)
            (x + ((double (tiers cote) - 1 : ℕ) : ℤ)) := by
        have h := newA.diag1.bottomLeft
        have ht : ((t + 2) + 1) + (tiers cote + 1) = (t + tiers cote + 1) + 3 := by omega
        rw [ht] at h
        exact h
      have newDD :
          DD n ((t + tiers cote + 1) + 2) x (double (tiers cote) - 1) := ih newL1 newL2
      have ht' : (t + tiers cote + 1) + 2 = (t + 2) + tiers cote + 1 := by omega
      rw [ht'] at newDD
      exact DD.DD_A (t + 2) x cote hle hmod newA newDD
  | DD_B t x cote hle hmod hB _ ih =>
      intro hL1 hL2
      have hpd : (double (tiers cote) + tiers cote) + 1 = cote :=
        Splus_deuxtiers_untiers cote hmod
      have hcol :
          x + (cote : ℤ)
            = x + ((double (tiers cote) : ℕ) : ℤ) + ((tiers cote + 1 : ℕ) : ℤ) := by
        omega
      rw [hcol] at hL1 hL2
      have newB :
          B_basic n (t + 2) (x + ((double (tiers cote) : ℕ) : ℤ)) (tiers cote + 1) :=
        B_B n t (x + ((double (tiers cote) : ℕ) : ℤ)) (tiers cote + 1) hB hL1 hL2
      have newL1 :
          L_Etat n ((t + tiers cote + 1) + 2)
            (x + ((double (tiers cote) : ℕ) : ℤ)) := by
        have h := newB.diag0.bottomLeft
        have ht : (t + 2) + (tiers cote + 1) = (t + tiers cote + 1) + 2 := by omega
        rw [ht] at h
        exact h
      have newL2 :
          L_Etat n ((t + tiers cote + 1) + 3)
            (x + ((double (tiers cote) : ℕ) : ℤ)) := by
        have h := newB.diag1.bottomLeft
        have ht : ((t + 2) + 1) + (tiers cote + 1) = (t + tiers cote + 1) + 3 := by omega
        rw [ht] at h
        exact h
      have newDD :
          DD n ((t + tiers cote + 1) + 2) x (double (tiers cote)) := ih newL1 newL2
      have ht' : (t + tiers cote + 1) + 2 = (t + 2) + tiers cote + 1 := by omega
      rw [ht'] at newDD
      exact DD.DD_B (t + 2) x cote hle hmod newB newDD
  | DD_C t x cote hle hmod hC _ ih =>
      intro hL1 hL2
      have hpd : (double (tiers cote) + tiers cote) + 2 = cote :=
        SSplus_deuxtiers_untiers cote hmod
      have hcol :
          x + (cote : ℤ)
            = x + ((double (tiers cote) + 1 : ℕ) : ℤ) + ((tiers cote + 1 : ℕ) : ℤ) := by
        omega
      rw [hcol] at hL1 hL2
      have newC :
          C_basic n (t + 2) (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) (tiers cote + 1) :=
        C_C n t (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) (tiers cote + 1) hC hL1 hL2
      have newL1 :
          L_Etat n ((t + tiers cote + 1) + 2)
            (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) := by
        have h := newC.diag0.bottomLeft
        have ht : (t + 2) + (tiers cote + 1) = (t + tiers cote + 1) + 2 := by omega
        rw [ht] at h
        exact h
      have newL2 :
          L_Etat n ((t + tiers cote + 1) + 3)
            (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) := by
        have h := newC.diag1.bottomLeft
        have ht : ((t + 2) + 1) + (tiers cote + 1) = (t + tiers cote + 1) + 3 := by omega
        rw [ht] at h
        exact h
      have newDD :
          DD n ((t + tiers cote + 1) + 2) x (double (tiers cote) + 1) := ih newL1 newL2
      have ht' : (t + tiers cote + 1) + 2 = (t + 2) + tiers cote + 1 := by omega
      rw [ht'] at newDD
      exact DD.DD_C (t + 2) x cote hle hmod newC newDD

/-! ### "Side-up" closure: feed an extra L-column on the right and grow
       the side by 1. This is the harder of the two closure lemmas
       because the brick type rotates (A→B→C→A). -/

theorem DD_hddollar (t : ℕ) (x : ℤ) (cote : ℕ) :
    DD n t x cote →
    L_Etat n (t + 1) (x + (cote + 1)) →
    L_Etat n (t + 2) (x + (cote + 1)) →
    DD n (t + 1) x (cote + 1) := by
  intro hdd
  induction hdd with
  | DD_4 t x h =>
      intro hL1 hL2
      -- cote = 3, target: DD n (t+1) x 4 via DD_5 + quatre_cinq.
      show DD n (t + 1) x 4
      have hL1' : L_Etat n (t + 1) (x + 4) := by
        have heq : x + ((3 + 1 : ℕ) : ℤ) = x + 4 := by push_cast; ring
        rw [← heq]; exact hL1
      have hL2' : L_Etat n (t + 2) (x + 4) := by
        have heq : x + ((3 + 1 : ℕ) : ℤ) = x + 4 := by push_cast; ring
        rw [← heq]; exact hL2
      exact DD.DD_5 (t + 1) x (quatre_cinq n t x h hL1' hL2')
  | DD_5 t x h =>
      intro hL1 hL2
      -- cote = 4, target: DD n (t+1) x 5 via DD_C side 5 + cinq_quatre.
      show DD n (t + 1) x 5
      have hL1' : L_Etat n (t + 1) (x + 5) := by
        have heq : x + ((4 + 1 : ℕ) : ℤ) = x + 5 := by push_cast; ring
        rw [← heq]; exact hL1
      have hL2' : L_Etat n (t + 2) (x + 5) := by
        have heq : x + ((4 + 1 : ℕ) : ℤ) = x + 5 := by push_cast; ring
        rw [← heq]; exact hL2
      have hcq : C_basic n (t + 1) (x + 3) 2 ∧ quatre_end n (t + 3) x :=
        cinq_quatre n t x h hL1' hL2'
      have hC : C_basic n (t + 1) (x + ((double (tiers 5) + 1 : ℕ) : ℤ)) (tiers 5 + 1) := by
        change C_basic n (t + 1) (x + ((3 : ℕ) : ℤ)) 2
        have hcast : ((3 : ℕ) : ℤ) = (3 : ℤ) := by norm_cast
        rw [hcast]
        exact hcq.1
      have hInner : DD n ((t + 1) + tiers 5 + 1) x (double (tiers 5) + 1) := by
        change DD n (t + 3) x 3
        exact DD.DD_4 (t + 3) x hcq.2
      have hd5 : Deuxmod3 5 := by unfold Deuxmod3; decide
      exact DD.DD_C (t + 1) x 5 (by decide) hd5 hC hInner
  | DD_A t x cote hle hmod hA _ ih =>
      intro hL1 hL2
      -- A → B rotation: new cote = cote + 1, Unmod3.
      have hpos : 1 ≤ double (tiers cote) := lt_O_deuxtiers cote (by omega)
      have hpd  : double (tiers cote) + tiers cote = cote :=
        plus_deuxtiers_untiers cote hmod
      have htiers : tiers cote = tiers (cote + 1) := tiers_S cote hmod
      have hmod' : Unmod3 (cote + 1) := Omod3_Unmod3 cote hmod
      have hsize' : 7 ≤ cote + 1 := by omega
      -- L's at column (x + (d-1) + 1) + (tiers cote + 1) = x + (↑cote + 1).
      have hcol :
          x + ((cote : ℤ) + 1)
            = x + ((double (tiers cote) - 1 : ℕ) : ℤ) + 1 + ((tiers cote + 1 : ℕ) : ℤ) := by
        omega
      rw [hcol] at hL1 hL2
      have newB' :
          B_basic n (t + 1) (x + ((double (tiers cote) - 1 : ℕ) : ℤ) + 1) (tiers cote + 1) :=
        A_B n t (x + ((double (tiers cote) - 1 : ℕ) : ℤ)) (tiers cote + 1) hA hL1 hL2
      have hcolB :
          x + ((double (tiers cote) - 1 : ℕ) : ℤ) + 1
            = x + ((double (tiers cote) : ℕ) : ℤ) := by omega
      rw [hcolB] at newB'
      have newL1 :
          L_Etat n ((t + tiers cote + 1) + 1)
            (x + ((double (tiers cote) - 1 + 1 : ℕ) : ℤ)) := by
        have h := newB'.diag0.bottomLeft
        have ht : (t + 1) + (tiers cote + 1) = (t + tiers cote + 1) + 1 := by omega
        have hx :
            x + ((double (tiers cote) : ℕ) : ℤ)
              = x + ((double (tiers cote) - 1 + 1 : ℕ) : ℤ) := by omega
        rw [ht, hx] at h
        exact h
      have newL2 :
          L_Etat n ((t + tiers cote + 1) + 2)
            (x + ((double (tiers cote) - 1 + 1 : ℕ) : ℤ)) := by
        have h := newB'.diag1.bottomLeft
        have ht : ((t + 1) + 1) + (tiers cote + 1) = (t + tiers cote + 1) + 2 := by omega
        have hx :
            x + ((double (tiers cote) : ℕ) : ℤ)
              = x + ((double (tiers cote) - 1 + 1 : ℕ) : ℤ) := by omega
        rw [ht, hx] at h
        exact h
      have innerDD :
          DD n ((t + tiers cote + 1) + 1) x (double (tiers cote) - 1 + 1) :=
        ih newL1 newL2
      have hsideEq : double (tiers cote) - 1 + 1 = double (tiers cote) := by omega
      rw [hsideEq] at innerDD
      have ht' : (t + tiers cote + 1) + 1 = (t + 1) + tiers (cote + 1) + 1 := by
        rw [← htiers]; omega
      rw [ht'] at innerDD
      have hd' : double (tiers cote) = double (tiers (cote + 1)) := by rw [htiers]
      rw [hd'] at innerDD
      have newB :
          B_basic n (t + 1) (x + ((double (tiers (cote + 1)) : ℕ) : ℤ))
            (tiers (cote + 1) + 1) := by
        rw [← htiers]; exact newB'
      exact DD.DD_B (t + 1) x (cote + 1) hsize' hmod' newB innerDD
  | DD_B t x cote hle hmod hB _ ih =>
      intro hL1 hL2
      -- B → C rotation.
      have hpd : (double (tiers cote) + tiers cote) + 1 = cote :=
        Splus_deuxtiers_untiers cote hmod
      have htiers : tiers cote = tiers (cote + 1) := tiers_SS cote hmod
      have hmod' : Deuxmod3 (cote + 1) := Unmod3_Deuxmod3 cote hmod
      have hsize' : 5 ≤ cote + 1 := by omega
      -- L's at column (x + d + 1) + (tiers cote + 1) = x + (↑cote + 1).
      have hcol :
          x + ((cote : ℤ) + 1)
            = x + ((double (tiers cote) : ℕ) : ℤ) + 1 + ((tiers cote + 1 : ℕ) : ℤ) := by
        omega
      rw [hcol] at hL1 hL2
      have newC' :
          C_basic n (t + 1) (x + ((double (tiers cote) : ℕ) : ℤ) + 1) (tiers cote + 1) :=
        B_C n t (x + ((double (tiers cote) : ℕ) : ℤ)) (tiers cote + 1) hB hL1 hL2
      have hcolC :
          x + ((double (tiers cote) : ℕ) : ℤ) + 1
            = x + ((double (tiers cote) + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcolC] at newC'
      have newL1 :
          L_Etat n ((t + tiers cote + 1) + 1)
            (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) := by
        have h := newC'.diag0.bottomLeft
        have ht : (t + 1) + (tiers cote + 1) = (t + tiers cote + 1) + 1 := by omega
        rw [ht] at h
        exact h
      have newL2 :
          L_Etat n ((t + tiers cote + 1) + 2)
            (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) := by
        have h := newC'.diag1.bottomLeft
        have ht : ((t + 1) + 1) + (tiers cote + 1) = (t + tiers cote + 1) + 2 := by omega
        rw [ht] at h
        exact h
      have innerDD :
          DD n ((t + tiers cote + 1) + 1) x (double (tiers cote) + 1) :=
        ih newL1 newL2
      have ht' : (t + tiers cote + 1) + 1 = (t + 1) + tiers (cote + 1) + 1 := by
        rw [← htiers]; omega
      rw [ht'] at innerDD
      have hd' :
          (double (tiers cote) + 1 : ℕ) = (double (tiers (cote + 1)) + 1 : ℕ) := by
        rw [htiers]
      rw [hd'] at innerDD
      have newC :
          C_basic n (t + 1) (x + ((double (tiers (cote + 1)) + 1 : ℕ) : ℤ))
            (tiers (cote + 1) + 1) := by
        rw [← htiers]; exact newC'
      exact DD.DD_C (t + 1) x (cote + 1) hsize' hmod' newC innerDD
  | DD_C t x cote hle hmod hC hDD _ =>
      intro hL1 hL2
      -- C → A rotation; uses DD_hh (not the IH) on the inner DD because
      -- the side stays the same but the time shifts by 2.
      have hpd : (double (tiers cote) + tiers cote) + 2 = cote :=
        SSplus_deuxtiers_untiers cote hmod
      have htiers : tiers cote + 1 = tiers (cote + 1) := tiers_SSS cote hmod
      have hmod' : Omod3 (cote + 1) := Deuxmod3_Omod3 cote hmod
      have hsize' : 6 ≤ cote + 1 := by omega
      -- L's at column (x + (d+1)) + (tiers cote + 1 + 1) = x + (↑cote + 1).
      have hcol :
          x + ((cote : ℤ) + 1)
            = x + ((double (tiers cote) + 1 : ℕ) : ℤ)
              + ((tiers cote + 1 + 1 : ℕ) : ℤ) := by
        omega
      rw [hcol] at hL1 hL2
      have newA' :
          A_basic n (t + 1) (x + ((double (tiers cote) + 1 : ℕ) : ℤ))
            (tiers cote + 1 + 1) :=
        C_A n t (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) (tiers cote + 1) hC hL1 hL2
      have newL1 :
          L_Etat n ((t + tiers cote + 1) + 2)
            (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) := by
        have h := newA'.diag0.bottomLeft
        have ht : (t + 1) + (tiers cote + 1 + 1) = (t + tiers cote + 1) + 2 := by omega
        rw [ht] at h
        exact h
      have newL2 :
          L_Etat n ((t + tiers cote + 1) + 3)
            (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) := by
        have h := newA'.diag1.bottomLeft
        have ht : ((t + 1) + 1) + (tiers cote + 1 + 1) = (t + tiers cote + 1) + 3 := by omega
        rw [ht] at h
        exact h
      have innerDD :
          DD n ((t + tiers cote + 1) + 2) x (double (tiers cote) + 1) :=
        DD_hh n (t + tiers cote + 1) x (double (tiers cote) + 1) hDD newL1 newL2
      have ht' : (t + tiers cote + 1) + 2 = (t + 1) + tiers (cote + 1) + 1 := by
        rw [← htiers]; omega
      rw [ht'] at innerDD
      have hsideEq :
          (double (tiers cote) + 1 : ℕ) = double (tiers (cote + 1)) - 1 := by
        rw [← htiers]
        unfold double
        omega
      rw [hsideEq] at innerDD
      have hSizeBrick : tiers cote + 1 + 1 = tiers (cote + 1) + 1 := by omega
      rw [hSizeBrick] at newA'
      have hAnchor :
          x + ((double (tiers cote) + 1 : ℕ) : ℤ)
            = x + ((double (tiers (cote + 1)) - 1 : ℕ) : ℤ) := by
        rw [hsideEq]
      rw [hAnchor] at newA'
      exact DD.DD_A (t + 1) x (cote + 1) hsize' hmod' newA' innerDD

end FsspMazoyer
end CellularAutomatas
