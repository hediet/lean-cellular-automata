/-
  Mazoyer FSSP -- the trapezoid lemmas: brick + G-wall ⇒ G-wall + smaller DD
  (port of `trapeze.v`).
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.reflection
import CellularAutomatas.proofs.constructions.fssp_mazoyer.vertical

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

variable (n : ℕ)

/-! ### Auxiliary arithmetic -/

lemma R1 (m : ℕ) : 1 < m → double m = 3 + (double (m + 1 - 3) + 1) := by
  intro h; unfold double; omega
lemma R1' (m : ℕ) : 1 < m → (double m - 1) = 2 + (double (m + 1 - 3) + 1) := by
  intro h; unfold double; omega
lemma R2 (m : ℕ) : 2 < m → 0 < m + 1 - 3 := by
  intro h; omega
lemma R3 (m : ℕ) : 2 < m → m = (m + 1 - 3) + 2 := by
  intro h; omega

/-! ### The smallest case: a length-1 row -/

variable (t : ℕ) (x : ℤ)

lemma H2_Vg :
    Horizontale_t1 t x 0 (G_Etat n) (C_Etat n) (L_Etat n) →
    Verticale t (x + 3) 2 (G_Etat n) →
    Verticale (t + 1) x 1 (G_Etat n) := by
  intro Hh _
  -- `Ht1_VV` with `cote = 0` gives `Verticale (t+1) x (double 0 + 1) G`,
  -- and `double 0 + 1 = 1`.
  have h := Ht1_VV n t x 0 Hh
  simpa [double] using h

lemma H2_Hh :
    Horizontale_t1 t x 0 (G_Etat n) (C_Etat n) (L_Etat n) →
    Verticale t (x + 3) 2 (G_Etat n) →
    Horizontale_t1 (t + 1) x 0 (G_Etat n) (B_Etat n) (G_Etat n) := by
  intro Hh Hv
  -- Cells of the input row.
  have e_x : Etat n t x = G := Hh.head
  have e_xp1 : Etat n t (x + 1) = C := Hh.next1
  have e_xp2 : Etat n t (x + 2) = L := by
    have h := Hh.tail.pointwise 0 (Nat.zero_le _)
    simpa using h
  have e_xp3 : Etat n t (x + 3) = G := by
    have h := Hv.pointwise 0 (Nat.zero_le _)
    simpa using h
  refine ⟨?_, ?_, ⟨fun dx hdx => ?_⟩⟩
  · -- head: `G_Etat n (t+1) x` via δ ? G C = G.
    show Etat n (t + 1) x = G
    rw [un_pas, e_x, e_xp1]
    rfl
  · -- next1: `B_Etat n (t+1) (x+1)` via δ G C L = B.
    show Etat n (t + 1) (x + 1) = B
    rw [un_pas, show ((x + 1 : ℤ) - 1) = x from by ring,
        show ((x + 1 : ℤ) + 1) = x + 2 from by ring,
        e_x, e_xp1, e_xp2]
    rfl
  · -- tail: only `dx = 0` is in range; show `G_Etat n (t+1) (x+2)` via δ C L G = G.
    obtain rfl : dx = 0 := Nat.le_zero.mp hdx
    show Etat n (t + 1) ((x + 2) + ((0 : ℕ) : ℤ)) = G
    have heq : ((x + 2 : ℤ) + ((0 : ℕ) : ℤ)) = x + 2 := by push_cast; ring
    rw [heq, un_pas, show ((x + 2 : ℤ) - 1) = x + 1 from by ring,
        show ((x + 2 : ℤ) + 1) = x + 3 from by ring,
        e_xp1, e_xp2, e_xp3]
    rfl

lemma H2_Hg :
    Horizontale_t1 t x 0 (G_Etat n) (C_Etat n) (L_Etat n) →
    Verticale t (x + 3) 2 (G_Etat n) →
    Horizontale (t + 2) x 2 (G_Etat n) := by
  intro Hh Hv
  -- Reuse `H2_Hh` to get the `G:B:G` row at time `t+1`.
  have hh1 := H2_Hh n t x Hh Hv
  have eGx  : G_Etat n (t + 1) x := hh1.head
  have eBx1 : B_Etat n (t + 1) (x + 1) := hh1.next1
  have eGx2 : G_Etat n (t + 1) (x + 2) := by
    have h := hh1.tail.pointwise 0 (Nat.zero_le _)
    simpa using h
  -- The right-edge G at column `x+3` at time `t+1` (from `Hv`).
  have eGx3 : G_Etat n (t + 1) (x + 3) := Hv.pointwise 1 (by omega)
  -- (t+2, x): apex law `G + B → G`.
  have h2x : G_Etat n (t + 2) x := GB_G n (t + 1) x eGx eBx1
  -- (t+2, x+1): apex law `G + B + G → G`.
  have h2x1 : G_Etat n (t + 2) (x + 1) :=
    GBG_dollarG n (t + 1) x eGx eBx1 eGx2
  -- (t+2, x+2): direct δ B G G = G.
  have h2x2 : G_Etat n (t + 2) (x + 2) := by
    show Etat n (t + 2) (x + 2) = G
    change Etat n ((t + 1) + 1) (x + 2) = G
    rw [un_pas, show ((x + 2 : ℤ) - 1) = x + 1 from by ring,
        show ((x + 2 : ℤ) + 1) = x + 3 from by ring,
        show Etat n (t + 1) (x + 1) = B from eBx1,
        show Etat n (t + 1) (x + 2) = G from eGx2,
        show Etat n (t + 1) (x + 3) = G from eGx3]
    rfl
  exact hor_deux (t + 2) x (G_Etat n) h2x h2x1 h2x2

/-! ### A-trapezoid -/

lemma Ha_Vg (cote : ℕ) :
    A_basic n t x (cote + 1) →
    Verticale (t + 1) ((x + cote) + 2) (triple cote) (G_Etat n) →
    Verticale ((t + cote) + 2) (x + 1) (double cote - 1) (G_Etat n) := by
  intro Ha Hv
  have hcote : 2 ≤ cote := by have := Ha.size; omega
  -- The two top G cells of the right wall, used by both `A_Vg` and `A_ZCB`.
  have eqX : ((x + 1) + ((cote + 1 : ℕ) : ℤ)) = (x + cote) + 2 := by push_cast; ring
  have hg1 : G_Etat n (t + 1) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 1) _ = G
    rw [eqX]
    exact Hv.pointwise 0 (Nat.zero_le _)
  have hg2 : G_Etat n (t + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 2) _ = G
    rw [eqX]
    exact Hv.pointwise 1 (by unfold triple; omega)
  -- V1 := the 2-cell `Verticale` from `A_Vg` at `(t + cote + 2, x + 1)`.
  have hAVg : Verticale ((t + cote) + 2) (x + 1) 1 (G_Etat n) := by
    have h := A_Vg n t x (cote + 1) Ha hg1 hg2
    have heq : (t + 1) + (cote + 1) = (t + cote) + 2 := by omega
    rw [heq] at h; exact h
  -- The ZCB built from the brick + two G's.
  have hZCB : ZCB n (t + 1) (x + 1) (cote + 1) :=
    A_ZCB n t x (cote + 1) Ha hg1 hg2
  -- Right-edge sub-wall consumed by `ZCB_Ht1`.
  have hsub : Verticale ((t + 1) + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ))
              (cote + 1) (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 3) ((x + cote) + 2)
              (triple cote) (cote + 1) (G_Etat n)
              (by omega) (by unfold triple; omega) Hv
    have ht : (t + 1) + 2 = t + 3 := by omega
    show Verticale _ _ (cote + 1) (G_Etat n)
    rw [ht, eqX]; exact h
  -- The `G:C:L^*` row at the bottom of the ZCB.
  have hHt1 : Horizontale_t1 ((t + 1) + ((cote + 1) + 1)) (x + 1)
              ((cote + 1) - 3) (G_Etat n) (C_Etat n) (L_Etat n) :=
    ZCB_Ht1 n (t + 1) (x + 1) (cote + 1) (by omega) hZCB hsub
  -- Translate the row downward to `Verticale` via `Ht1_VV`.
  have hVV0 : Verticale (((t + 1) + ((cote + 1) + 1)) + 1) (x + 1)
              (double ((cote + 1) - 3) + 1) (G_Etat n) :=
    Ht1_VV n _ (x + 1) ((cote + 1) - 3) hHt1
  -- Reshape its time-base to match `vv_vert`.
  have hVV : Verticale (((t + cote) + 2) + 1 + 1) (x + 1)
              (double ((cote + 1) - 3) + 1) (G_Etat n) := by
    have ht : ((t + 1) + ((cote + 1) + 1)) + 1 = ((t + cote) + 2) + 1 + 1 := by omega
    rw [ht] at hVV0; exact hVV0
  -- Combine the 2-cell wall from `A_Vg` with the long wall from `Ht1_VV`.
  have hCombined :=
    vv_vert ((t + cote) + 2) (x + 1) 1 (double ((cote + 1) - 3) + 1)
            (G_Etat n) hAVg hVV
  -- Match `(1 + 1) + (double((cote+1)-3) + 1)` with `double cote - 1`.
  have hmatch : (1 + 1) + (double ((cote + 1) - 3) + 1) = double cote - 1 := by
    unfold double; omega
  rw [hmatch] at hCombined
  exact hCombined

lemma Ha3_Hg :
    A_basic n t x 3 →
    Verticale (t + 1) (x + 4) 6 (G_Etat n) →
    Horizontale (t + 7) (x + 1) 2 (G_Etat n) := by
  intro Ha Hv
  -- Build the ZCB of side 3 from `A_basic` and the right wall.
  have hg1 : G_Etat n (t + 1) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 1) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 0 (Nat.zero_le _)
  have hg2 : G_Etat n (t + 2) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 2) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 1 (by omega)
  have hZCB : ZCB n (t + 1) (x + 1) 3 := A_ZCB n t x 3 Ha hg1 hg2
  -- Sub-wall consumed by `ZCB_Ht1`.
  have hsub : Verticale ((t + 1) + 2) ((x + 1) + (3 : ℕ)) 3 (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 3) (x + 4) 6 3 (G_Etat n)
              (by omega) (by omega) Hv
    show Verticale (t + 3) ((x + 1) + ((3 : ℕ) : ℤ)) 3 (G_Etat n)
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact h
  -- The `G:C:L^*` row of length 0 at the bottom of the ZCB.
  have hHt1 : Horizontale_t1 ((t + 1) + (3 + 1)) (x + 1) (3 - 3)
              (G_Etat n) (C_Etat n) (L_Etat n) :=
    ZCB_Ht1 n (t + 1) (x + 1) 3 (by omega) hZCB hsub
  -- Reshape: `(t+1) + (3 + 1) = t + 5`, `3 - 3 = 0`.
  have hHt1' : Horizontale_t1 (t + 5) (x + 1) 0
              (G_Etat n) (C_Etat n) (L_Etat n) := by
    have ht : (t + 1) + (3 + 1) = t + 5 := by omega
    rw [ht] at hHt1
    exact hHt1
  -- The 2-cell vertical wall `Verticale (t+5) (x+4) 2 (G_Etat n)` for `H2_Hg`.
  have hVwall : Verticale (t + 5) ((x + 1) + 3) 2 (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 5) (x + 4) 6 2 (G_Etat n)
              (by omega) (by omega) Hv
    show Verticale (t + 5) (x + 1 + 3) 2 (G_Etat n)
    rw [show ((x + 1 : ℤ) + 3) = x + 4 from by ring]
    exact h
  -- Apply `H2_Hg` and reshape the time index.
  have h := H2_Hg n (t + 5) (x + 1) hHt1' hVwall
  have ht : (t + 5) + 2 = t + 7 := by omega
  rw [ht] at h
  exact h

lemma Hb3_Hg :
    B_basic n t x 3 →
    Verticale (t + 1) (x + 4) 7 (G_Etat n) →
    Horizontale (t + 8) (x + 1) 2 (G_Etat n) := by
  intro Hb Hv
  have hg1 : G_Etat n (t + 1) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 1) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 0 (Nat.zero_le _)
  have hg2 : G_Etat n (t + 2) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 2) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 1 (by omega)
  have hg3 : G_Etat n (t + 3) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 3) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 2 (by omega)
  have hZCB : ZCB n (t + 2) (x + 1) 3 := B_ZCB n t x 3 Hb hg1 hg2 hg3
  have hsub : Verticale ((t + 2) + 2) ((x + 1) + (3 : ℕ)) 3 (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 4) (x + 4) 7 3 (G_Etat n)
              (by omega) (by omega) Hv
    show Verticale (t + 4) ((x + 1) + ((3 : ℕ) : ℤ)) 3 (G_Etat n)
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact h
  have hHt1 : Horizontale_t1 ((t + 2) + (3 + 1)) (x + 1) (3 - 3)
              (G_Etat n) (C_Etat n) (L_Etat n) :=
    ZCB_Ht1 n (t + 2) (x + 1) 3 (by omega) hZCB hsub
  have hHt1' : Horizontale_t1 (t + 6) (x + 1) 0
              (G_Etat n) (C_Etat n) (L_Etat n) := by
    have ht : (t + 2) + (3 + 1) = t + 6 := by omega
    rw [ht] at hHt1
    exact hHt1
  have hVwall : Verticale (t + 6) ((x + 1) + 3) 2 (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 6) (x + 4) 7 2 (G_Etat n)
              (by omega) (by omega) Hv
    show Verticale (t + 6) (x + 1 + 3) 2 (G_Etat n)
    rw [show ((x + 1 : ℤ) + 3) = x + 4 from by ring]
    exact h
  have h := H2_Hg n (t + 6) (x + 1) hHt1' hVwall
  have ht : (t + 6) + 2 = t + 8 := by omega
  rw [ht] at h
  exact h

lemma Ha_DD (cote : ℕ) :
    2 < cote →
    A_basic n t x (cote + 1) →
    Verticale (t + 1) ((x + cote) + 2) (triple cote) (G_Etat n) →
    DD n (t + double cote) (x + 1) cote := by
  intro hcote Ha Hv
  have eqX : ((x + 1) + ((cote + 1 : ℕ) : ℤ)) = (x + cote) + 2 := by push_cast; ring
  have hg1 : G_Etat n (t + 1) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 1) _ = G; rw [eqX]
    exact Hv.pointwise 0 (Nat.zero_le _)
  have hg2 : G_Etat n (t + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 2) _ = G; rw [eqX]
    exact Hv.pointwise 1 (by unfold triple; omega)
  have hZCB : ZCB n (t + 1) (x + 1) (cote + 1) :=
    A_ZCB n t x (cote + 1) Ha hg1 hg2
  have hsub : Verticale ((t + 1) + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ))
              (cote + 1) (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 3) ((x + cote) + 2)
              (triple cote) (cote + 1) (G_Etat n)
              (by omega) (by unfold triple; omega) Hv
    have ht : (t + 1) + 2 = t + 3 := by omega
    show Verticale _ _ (cote + 1) (G_Etat n); rw [ht, eqX]; exact h
  have hHt1 : Horizontale_t1 ((t + 1) + ((cote + 1) + 1)) (x + 1)
              ((cote + 1) - 3) (G_Etat n) (C_Etat n) (L_Etat n) :=
    ZCB_Ht1 n (t + 1) (x + 1) (cote + 1) (by omega) hZCB hsub
  -- Reshape the row length to `(cote - 3) + 1` so `Ht1_DDf` applies.
  have hRowEq : (cote + 1) - 3 = (cote - 3) + 1 := by omega
  have hHt1' : Horizontale_t1 ((t + 1) + ((cote + 1) + 1)) (x + 1) ((cote - 3) + 1)
              (G_Etat n) (C_Etat n) (L_Etat n) := by rw [← hRowEq]; exact hHt1
  have hDD := Ht1_DDf n _ (x + 1) (cote - 3) hHt1'
  have heq1 : (((t + 1) + ((cote + 1) + 1)) + (cote - 3)) = t + double cote := by
    unfold double; omega
  have heq2 : (cote - 3) + 3 = cote := by omega
  rw [heq1, heq2] at hDD
  exact hDD

/-! ### B-trapezoid -/

lemma Hb_Vg (cote : ℕ) :
    B_basic n t x (cote + 1) →
    Verticale (t + 1) ((x + cote) + 2) (triple cote + 1) (G_Etat n) →
    Verticale ((t + cote) + 2) (x + 1) (double cote) (G_Etat n) := by
  intro Hb Hv
  have hcote : 2 ≤ cote := by have := Hb.size; omega
  have eqX : ((x + 1) + ((cote + 1 : ℕ) : ℤ)) = (x + cote) + 2 := by push_cast; ring
  have hg1 : G_Etat n (t + 1) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 1) _ = G; rw [eqX]
    exact Hv.pointwise 0 (Nat.zero_le _)
  have hg2 : G_Etat n (t + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 2) _ = G; rw [eqX]
    exact Hv.pointwise 1 (by unfold triple; omega)
  have hg3 : G_Etat n (t + 3) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 3) _ = G; rw [eqX]
    exact Hv.pointwise 2 (by unfold triple; omega)
  -- V1 := the 3-cell `Verticale` from `B_Vg`.
  have hBVg : Verticale ((t + cote) + 2) (x + 1) 2 (G_Etat n) := by
    have h := B_Vg n t x (cote + 1) Hb hg1 hg2 hg3
    have heq : (t + 1) + (cote + 1) = (t + cote) + 2 := by omega
    rw [heq] at h; exact h
  have hZCB : ZCB n (t + 2) (x + 1) (cote + 1) :=
    B_ZCB n t x (cote + 1) Hb hg1 hg2 hg3
  have hsub : Verticale ((t + 2) + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ))
              (cote + 1) (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 4) ((x + cote) + 2)
              (triple cote + 1) (cote + 1) (G_Etat n)
              (by omega) (by unfold triple; omega) Hv
    have ht : (t + 2) + 2 = t + 4 := by omega
    show Verticale _ _ (cote + 1) (G_Etat n); rw [ht, eqX]; exact h
  have hHt1 : Horizontale_t1 ((t + 2) + ((cote + 1) + 1)) (x + 1)
              ((cote + 1) - 3) (G_Etat n) (C_Etat n) (L_Etat n) :=
    ZCB_Ht1 n (t + 2) (x + 1) (cote + 1) (by omega) hZCB hsub
  have hVV0 : Verticale (((t + 2) + ((cote + 1) + 1)) + 1) (x + 1)
              (double ((cote + 1) - 3) + 1) (G_Etat n) :=
    Ht1_VV n _ (x + 1) ((cote + 1) - 3) hHt1
  have hVV : Verticale (((t + cote) + 2) + 2 + 1) (x + 1)
              (double ((cote + 1) - 3) + 1) (G_Etat n) := by
    have ht : ((t + 2) + ((cote + 1) + 1)) + 1 = ((t + cote) + 2) + 2 + 1 := by omega
    rw [ht] at hVV0; exact hVV0
  have hCombined :=
    vv_vert ((t + cote) + 2) (x + 1) 2 (double ((cote + 1) - 3) + 1)
            (G_Etat n) hBVg hVV
  have hmatch : (2 + 1) + (double ((cote + 1) - 3) + 1) = double cote := by
    unfold double; omega
  rw [hmatch] at hCombined
  exact hCombined

lemma Hb_DD (cote : ℕ) :
    2 < cote →
    B_basic n t x (cote + 1) →
    Verticale (t + 1) ((x + cote) + 2) (triple cote + 1) (G_Etat n) →
    DD n (t + double cote + 1) (x + 1) cote := by
  intro hcote Hb Hv
  have eqX : ((x + 1) + ((cote + 1 : ℕ) : ℤ)) = (x + cote) + 2 := by push_cast; ring
  have hg1 : G_Etat n (t + 1) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 1) _ = G; rw [eqX]
    exact Hv.pointwise 0 (Nat.zero_le _)
  have hg2 : G_Etat n (t + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 2) _ = G; rw [eqX]
    exact Hv.pointwise 1 (by unfold triple; omega)
  have hg3 : G_Etat n (t + 3) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 3) _ = G; rw [eqX]
    exact Hv.pointwise 2 (by unfold triple; omega)
  have hZCB : ZCB n (t + 2) (x + 1) (cote + 1) :=
    B_ZCB n t x (cote + 1) Hb hg1 hg2 hg3
  have hsub : Verticale ((t + 2) + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ))
              (cote + 1) (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 4) ((x + cote) + 2)
              (triple cote + 1) (cote + 1) (G_Etat n)
              (by omega) (by unfold triple; omega) Hv
    have ht : (t + 2) + 2 = t + 4 := by omega
    show Verticale _ _ (cote + 1) (G_Etat n); rw [ht, eqX]; exact h
  have hHt1 : Horizontale_t1 ((t + 2) + ((cote + 1) + 1)) (x + 1)
              ((cote + 1) - 3) (G_Etat n) (C_Etat n) (L_Etat n) :=
    ZCB_Ht1 n (t + 2) (x + 1) (cote + 1) (by omega) hZCB hsub
  have hRowEq : (cote + 1) - 3 = (cote - 3) + 1 := by omega
  have hHt1' : Horizontale_t1 ((t + 2) + ((cote + 1) + 1)) (x + 1) ((cote - 3) + 1)
              (G_Etat n) (C_Etat n) (L_Etat n) := by rw [← hRowEq]; exact hHt1
  have hDD := Ht1_DDf n _ (x + 1) (cote - 3) hHt1'
  have heq1 : (((t + 2) + ((cote + 1) + 1)) + (cote - 3)) = t + double cote + 1 := by
    unfold double; omega
  have heq2 : (cote - 3) + 3 = cote := by omega
  rw [heq1, heq2] at hDD
  exact hDD

/-! ### C-trapezoid (smallest case `cote = 2`) -/

section CSpecial
variable (Hc : C_basic n t x 2)
variable (Hv : Verticale (t + 1) (x + 3) 5 (G_Etat n))

include Hc Hv in
lemma G22 : G_Etat n (t + 2) (x + 2) := by
  -- δ (C at (t+1, x+1)) (L at (t+1, x+2)) (G at (t+1, x+3)) = G.
  have e1 : Etat n (t+1) (x+1) = C := Hc.diag0.interior 1 1 (by omega) (by omega) (by omega)
  have e2 : Etat n (t+1) (x+2) = L := Hc.diag1.apex
  have e3 : Etat n (t+1) (x+3) = G := Hv.pointwise 0 (by omega)
  show Etat n (t+2) (x+2) = G
  change Etat n ((t+1)+1) (x+2) = G
  rw [un_pas, show ((x+2:ℤ)-1) = x+1 from by ring,
      show ((x+2:ℤ)+1) = x+3 from by ring,
      e1, e2, e3]
  rfl

include Hc Hv in
lemma G31 : G_Etat n (t + 3) (x + 1) := by
  -- δ L C G = G with the cells from `Hc` and `G22`.
  have e1 : Etat n (t+2) x = L := Hc.diag0.bottomLeft
  have e2 : Etat n (t+2) (x+1) = C :=
    Hc.diag1.interior 1 1 (by omega) (by omega) (by omega)
  have e3 : Etat n (t+2) (x+2) = G := G22 n t x Hc Hv
  show Etat n (t+3) (x+1) = G
  change Etat n ((t+2)+1) (x+1) = G
  rw [un_pas, show ((x+1:ℤ)-1) = x from by ring,
      show ((x+1:ℤ)+1) = x+2 from by ring,
      e1, e2, e3]
  rfl

include Hc Hv in
lemma A32 : A_Etat n (t + 3) (x + 2) := by
  -- δ C G G = A: cells from `Hc.diag1.interior`, `G22`, and `Hv` at `dt = 1`.
  have e1 : Etat n (t+2) (x+1) = C :=
    Hc.diag1.interior 1 1 (by omega) (by omega) (by omega)
  have e2 : Etat n (t+2) (x+2) = G := G22 n t x Hc Hv
  have e3 : Etat n (t+2) (x+3) = G := Hv.pointwise 1 (by omega)
  show Etat n (t+3) (x+2) = A
  change Etat n ((t+2)+1) (x+2) = A
  rw [un_pas, show ((x+2:ℤ)-1) = x+1 from by ring,
      show ((x+2:ℤ)+1) = x+3 from by ring,
      e1, e2, e3]
  rfl

include Hc Hv in
lemma G41 : G_Etat n (t + 4) (x + 1) := by
  -- One-step apex δ-law: G + A → G (left).
  apply GA_G n (t + 3) (x + 1) (G31 n t x Hc Hv)
  show Etat n (t + 3) (x + 1 + 1) = A
  rw [show ((x : ℤ) + 1 + 1) = x + 2 from by ring]
  exact A32 n t x Hc Hv

include Hc Hv in
lemma C42 : C_Etat n (t + 4) (x + 2) := by
  -- One-step apex δ-law: G + A → C (right).
  have h := GA_dollarC n (t + 3) (x + 1) (G31 n t x Hc Hv) ?_
  · -- h : C_Etat n (t + 4) (x + 1 + 1); reshape to (x + 2).
    show Etat n (t + 4) (x + 2) = C
    rw [show ((x : ℤ) + 2) = x + 1 + 1 from by ring]
    exact h
  · show Etat n (t + 3) (x + 1 + 1) = A
    rw [show ((x : ℤ) + 1 + 1) = x + 2 from by ring]
    exact A32 n t x Hc Hv

include Hc Hv in
lemma G51 : G_Etat n (t + 5) (x + 1) := by
  apply GC_G n (t + 4) (x + 1) (G41 n t x Hc Hv)
  show Etat n (t + 4) (x + 1 + 1) = C
  rw [show ((x : ℤ) + 1 + 1) = x + 2 from by ring]
  exact C42 n t x Hc Hv

include Hc Hv in
lemma B52 : B_Etat n (t + 5) (x + 2) := by
  have h := GC_dollarB n (t + 4) (x + 1) (G41 n t x Hc Hv) ?_
  · show Etat n (t + 5) (x + 2) = B
    rw [show ((x : ℤ) + 2) = x + 1 + 1 from by ring]
    exact h
  · show Etat n (t + 4) (x + 1 + 1) = C
    rw [show ((x : ℤ) + 1 + 1) = x + 2 from by ring]
    exact C42 n t x Hc Hv

include Hc Hv in
lemma Hc2_Vg : Verticale (t + 3) (x + 1) 3 (G_Etat n) := by
  -- Build a 4-cell vertical wall via `vert_trois`.
  have h31 : G_Etat n (t + 3) (x + 1) := G31 n t x Hc Hv
  have h41 : G_Etat n (t + 4) (x + 1) := G41 n t x Hc Hv
  have h51 : G_Etat n (t + 5) (x + 1) := G51 n t x Hc Hv
  have h52 : B_Etat n (t + 5) (x + 2) := B52 n t x Hc Hv
  have h61 : G_Etat n (t + 6) (x + 1) := by
    apply GB_G n (t + 5) (x + 1) h51
    show Etat n (t + 5) (x + 1 + 1) = B
    rw [show ((x : ℤ) + 1 + 1) = x + 2 from by ring]
    exact h52
  exact vert_trois (t + 3) (x + 1) (G_Etat n) h31 h41 h51 h61

include Hc Hv in
lemma Hc2_Hg : Horizontale (t + 6) (x + 1) 1 (G_Etat n) := by
  -- Build the 2-cell horizontal G-segment at row t+6.
  have h51 : G_Etat n (t + 5) (x + 1) := G51 n t x Hc Hv
  have h52 : B_Etat n (t + 5) (x + 2) := B52 n t x Hc Hv
  have h53 : G_Etat n (t + 5) (x + 3) := Hv.pointwise 4 (by omega)
  have h61 : G_Etat n (t + 6) (x + 1) := by
    apply GB_G n (t + 5) (x + 1) h51
    show Etat n (t + 5) (x + 1 + 1) = B
    rw [show ((x : ℤ) + 1 + 1) = x + 2 from by ring]
    exact h52
  have h62 : G_Etat n (t + 6) (x + 1 + 1) := by
    have h := GBG_dollarG n (t + 5) (x + 1) h51 ?_ ?_
    · -- h : G_Etat n (t + 6) (x + 1 + 1).
      exact h
    · show Etat n (t + 5) (x + 1 + 1) = B
      rw [show ((x : ℤ) + 1 + 1) = x + 2 from by ring]
      exact h52
    · show Etat n (t + 5) (x + 1 + 2) = G
      rw [show ((x : ℤ) + 1 + 2) = x + 3 from by ring]
      exact h53
  exact hor_un (t + 6) (x + 1) (G_Etat n) h61 h62

end CSpecial

/-! ### General C-trapezoid -/

lemma Hc_Vg (cote : ℕ) :
    C_basic n t x (cote + 1) →
    Verticale (t + 1) ((x + cote) + 2) (triple cote + 2) (G_Etat n) →
    Verticale ((t + cote) + 2) (x + 1) (double cote + 1) (G_Etat n) := by
  intro Hc Hv
  have hcote : 1 ≤ cote := by have := Hc.size; omega
  -- Two cases: cote = 1 (base) and cote ≥ 2 (recursion).
  rcases Nat.lt_or_ge 1 cote with hge | hle
  · -- cote ≥ 2: use C_Vg + C_ZCB + ZCB_Ht1 + Ht1_VV.
    have eqX : ((x + 1) + ((cote + 1 : ℕ) : ℤ)) = (x + cote) + 2 := by push_cast; ring
    have hg1 : G_Etat n (t + 1) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
      show Etat n (t + 1) _ = G; rw [eqX]
      exact Hv.pointwise 0 (Nat.zero_le _)
    have hg2 : G_Etat n (t + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
      show Etat n (t + 2) _ = G; rw [eqX]
      exact Hv.pointwise 1 (by unfold triple; omega)
    have hg3 : G_Etat n (t + 3) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
      show Etat n (t + 3) _ = G; rw [eqX]
      exact Hv.pointwise 2 (by unfold triple; omega)
    have hg4 : G_Etat n (t + 4) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
      show Etat n (t + 4) _ = G; rw [eqX]
      exact Hv.pointwise 3 (by unfold triple; omega)
    -- V1 := the 4-cell `Verticale` from `C_Vg`.
    have hCVg : Verticale ((t + cote) + 2) (x + 1) 3 (G_Etat n) := by
      have h := C_Vg n t x (cote + 1) (by omega) Hc hg1 hg2 hg3 hg4
      have heq : (t + 1) + (cote + 1) = (t + cote) + 2 := by omega
      rw [heq] at h; exact h
    have hZCB : ZCB n (t + 3) (x + 1) (cote + 1) :=
      C_ZCB n t x (cote + 1) (by omega) Hc hg1 hg2 hg3 hg4
    have hsub : Verticale ((t + 3) + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ))
                (cote + 1) (G_Etat n) := by
      have h := inclus_vert (t + 1) (t + 5) ((x + cote) + 2)
                (triple cote + 2) (cote + 1) (G_Etat n)
                (by omega) (by unfold triple; omega) Hv
      have ht : (t + 3) + 2 = t + 5 := by omega
      show Verticale _ _ (cote + 1) (G_Etat n); rw [ht, eqX]; exact h
    have hHt1 : Horizontale_t1 ((t + 3) + ((cote + 1) + 1)) (x + 1)
                ((cote + 1) - 3) (G_Etat n) (C_Etat n) (L_Etat n) :=
      ZCB_Ht1 n (t + 3) (x + 1) (cote + 1) (by omega) hZCB hsub
    have hVV0 : Verticale (((t + 3) + ((cote + 1) + 1)) + 1) (x + 1)
                (double ((cote + 1) - 3) + 1) (G_Etat n) :=
      Ht1_VV n _ (x + 1) ((cote + 1) - 3) hHt1
    have hVV : Verticale (((t + cote) + 2) + 3 + 1) (x + 1)
                (double ((cote + 1) - 3) + 1) (G_Etat n) := by
      have ht : ((t + 3) + ((cote + 1) + 1)) + 1 = ((t + cote) + 2) + 3 + 1 := by omega
      rw [ht] at hVV0; exact hVV0
    have hCombined :=
      vv_vert ((t + cote) + 2) (x + 1) 3 (double ((cote + 1) - 3) + 1)
              (G_Etat n) hCVg hVV
    have hmatch : (3 + 1) + (double ((cote + 1) - 3) + 1) = double cote + 1 := by
      unfold double; omega
    rw [hmatch] at hCombined
    exact hCombined
  · -- cote = 1: bottom out via `Hc2_Vg`.
    obtain rfl : cote = 1 := by omega
    -- After substitution: cote = 1.
    -- Hc : C_basic n t x 2; Hv : Verticale (t+1) ((x + ↑1) + 2) (triple 1 + 2) G.
    -- Reshape `Hv` into `Verticale (t+1) (x+3) 5 G_Etat`.
    have hHv : Verticale (t + 1) (x + 3) 5 (G_Etat n) := by
      have h := Hv
      have heqx : (x + ((1 : ℕ) : ℤ)) + 2 = x + 3 := by push_cast; ring
      have heqh : triple 1 + 2 = 5 := by decide
      rw [heqh, heqx] at h
      exact h
    have hres := Hc2_Vg n t x Hc hHv
    -- Goal: Verticale ((t + ↑1) + 2) (x + 1) (double 1 + 1) (G_Etat n)
    -- Reshape.
    have heqt : (t + (1 : ℕ)) + 2 = t + 3 := by omega
    have heqd : double 1 + 1 = 3 := by decide
    rw [heqt, heqd]; exact hres

lemma Hc3_Hg :
    C_basic n t x 3 →
    Verticale (t + 1) (x + 4) 8 (G_Etat n) →
    Horizontale (t + 9) (x + 1) 2 (G_Etat n) := by
  intro Hc Hv
  have hg1 : G_Etat n (t + 1) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 1) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 0 (Nat.zero_le _)
  have hg2 : G_Etat n (t + 2) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 2) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 1 (by omega)
  have hg3 : G_Etat n (t + 3) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 3) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 2 (by omega)
  have hg4 : G_Etat n (t + 4) ((x + 1) + (3 : ℕ)) := by
    show Etat n (t + 4) _ = G
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact Hv.pointwise 3 (by omega)
  have hZCB : ZCB n (t + 3) (x + 1) 3 := C_ZCB n t x 3 (by omega) Hc hg1 hg2 hg3 hg4
  have hsub : Verticale ((t + 3) + 2) ((x + 1) + (3 : ℕ)) 3 (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 5) (x + 4) 8 3 (G_Etat n)
              (by omega) (by omega) Hv
    show Verticale (t + 5) ((x + 1) + ((3 : ℕ) : ℤ)) 3 (G_Etat n)
    rw [show ((x + 1 : ℤ) + ((3 : ℕ) : ℤ)) = x + 4 from by push_cast; ring]
    exact h
  have hHt1 : Horizontale_t1 ((t + 3) + (3 + 1)) (x + 1) (3 - 3)
              (G_Etat n) (C_Etat n) (L_Etat n) :=
    ZCB_Ht1 n (t + 3) (x + 1) 3 (by omega) hZCB hsub
  have hHt1' : Horizontale_t1 (t + 7) (x + 1) 0
              (G_Etat n) (C_Etat n) (L_Etat n) := by
    have ht : (t + 3) + (3 + 1) = t + 7 := by omega
    rw [ht] at hHt1
    exact hHt1
  have hVwall : Verticale (t + 7) ((x + 1) + 3) 2 (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 7) (x + 4) 8 2 (G_Etat n)
              (by omega) (by omega) Hv
    show Verticale (t + 7) (x + 1 + 3) 2 (G_Etat n)
    rw [show ((x + 1 : ℤ) + 3) = x + 4 from by ring]
    exact h
  have h := H2_Hg n (t + 7) (x + 1) hHt1' hVwall
  have ht : (t + 7) + 2 = t + 9 := by omega
  rw [ht] at h
  exact h

lemma Hc_DD (cote : ℕ) :
    2 < cote →
    C_basic n t x (cote + 1) →
    Verticale (t + 1) ((x + cote) + 2) (triple cote + 2) (G_Etat n) →
    DD n (t + double cote + 2) (x + 1) cote := by
  intro hcote Hc Hv
  have eqX : ((x + 1) + ((cote + 1 : ℕ) : ℤ)) = (x + cote) + 2 := by push_cast; ring
  have hg1 : G_Etat n (t + 1) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 1) _ = G; rw [eqX]
    exact Hv.pointwise 0 (Nat.zero_le _)
  have hg2 : G_Etat n (t + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 2) _ = G; rw [eqX]
    exact Hv.pointwise 1 (by unfold triple; omega)
  have hg3 : G_Etat n (t + 3) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 3) _ = G; rw [eqX]
    exact Hv.pointwise 2 (by unfold triple; omega)
  have hg4 : G_Etat n (t + 4) ((x + 1) + ((cote + 1 : ℕ) : ℤ)) := by
    show Etat n (t + 4) _ = G; rw [eqX]
    exact Hv.pointwise 3 (by unfold triple; omega)
  have hZCB : ZCB n (t + 3) (x + 1) (cote + 1) :=
    C_ZCB n t x (cote + 1) (by omega) Hc hg1 hg2 hg3 hg4
  have hsub : Verticale ((t + 3) + 2) ((x + 1) + ((cote + 1 : ℕ) : ℤ))
              (cote + 1) (G_Etat n) := by
    have h := inclus_vert (t + 1) (t + 5) ((x + cote) + 2)
              (triple cote + 2) (cote + 1) (G_Etat n)
              (by omega) (by unfold triple; omega) Hv
    have ht : (t + 3) + 2 = t + 5 := by omega
    show Verticale _ _ (cote + 1) (G_Etat n); rw [ht, eqX]; exact h
  have hHt1 : Horizontale_t1 ((t + 3) + ((cote + 1) + 1)) (x + 1)
              ((cote + 1) - 3) (G_Etat n) (C_Etat n) (L_Etat n) :=
    ZCB_Ht1 n (t + 3) (x + 1) (cote + 1) (by omega) hZCB hsub
  have hRowEq : (cote + 1) - 3 = (cote - 3) + 1 := by omega
  have hHt1' : Horizontale_t1 ((t + 3) + ((cote + 1) + 1)) (x + 1) ((cote - 3) + 1)
              (G_Etat n) (C_Etat n) (L_Etat n) := by rw [← hRowEq]; exact hHt1
  have hDD := Ht1_DDf n _ (x + 1) (cote - 3) hHt1'
  have heq1 : (((t + 3) + ((cote + 1) + 1)) + (cote - 3)) = t + double cote + 2 := by
    unfold double; omega
  have heq2 : (cote - 3) + 3 = cote := by omega
  rw [heq1, heq2] at hDD
  exact hDD

end FsspMazoyer
end CellularAutomatas
