/-
  Mazoyer FSSP -- the final theorem `firing_squad` (port of `final.v`).

  Conversion to our `n`-cell convention:
  Coq's `N` becomes `n - 1` (so `n = N + 1`); Coq's axiom `2 < N`
  becomes `4 ≤ n`. Coq's right-phantom column `S N` is our column `n`.

  Note on `diagonale`: the original scaffolding stated
  `DD n (n - 2) 0 n`, but this is shifted by one in both `t` and `cote`
  relative to what `Ht0_DDf` produces from `base1` and what `sommet_1`
  consumes via `DD_Hg`. The corrected spec, matching Coq's
  `DD (pred (pred N)) 0 N`, is `DD n (n - 3) 0 (n - 1)`.
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.sommet

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

variable (n : ℕ)

/-- The initial all-`L` row to the right of cell 0 (length `n - 2`). -/
lemma base1 (h : 4 ≤ n) :
    Horizontale_t0 0 0 (n - 2) (G_Etat n) (L_Etat n) where
  head := show Etat n 0 0 = G from G00 n (by omega)
  tail :=
    { pointwise := fun dx _ => by
        -- goal: `L_Etat n 0 ((0 : ℤ) + 1 + dx)` ↦ `Etat n 0 _ = L`
        show Etat n 0 ((0 : ℤ) + 1 + (dx : ℤ)) = L
        have hx0 : (0 : ℤ) < (0 : ℤ) + 1 + (dx : ℤ) := by push_cast; omega
        have hxn : (0 : ℤ) + 1 + (dx : ℤ) < (n : ℤ) := by push_cast; omega
        exact base_L n (by omega) _ hx0 hxn }

/-- The recursive seed `DD` covering the entire array.
    (Coq: `DD (pred (pred N)) 0 N`.) -/
lemma diagonale (h : 4 ≤ n) : DD n (n - 3) 0 (n - 1) := by
  -- `Ht0_DDf` applied to `base1` produces
  -- `DD n (0 + ((n - 2) - 1)) 0 ((n - 2) + 1)`,
  -- which is exactly `DD n (n - 3) 0 (n - 1)`.
  have hb := base1 n h
  have hd := Ht0_DDf n 0 (n - 2) (by omega) hb
  have et : (0 : ℕ) + (n - 2 - 1) = n - 3 := by omega
  have el : (n - 2) + 1 = n - 1 := by omega
  rw [et, el] at hd
  exact hd

/-- The right-phantom row `G : C : L^*`. -/
lemma base2 (h : 4 ≤ n) :
    Horizontale_t1 0 (n : ℤ) (n - 2) (G_Etat n) (C_Etat n) (L_Etat n) where
  head  := show Etat n 0 (n : ℤ) = G from G0N n (by omega)
  next1 := show Etat n 0 ((n : ℤ) + 1) = C from C0N1 n (by omega)
  tail  :=
    { pointwise := fun dx _ => by
        -- goal: `Etat n 0 ((n : ℤ) + 2 + dx) = L`
        show Etat n 0 ((n : ℤ) + 2 + (dx : ℤ)) = L
        have hx : (n : ℤ) + 1 < (n : ℤ) + 2 + (dx : ℤ) := by omega
        exact basedollar_L n (by omega) _ hx }

/-- Vertical `G` wall on column `n` for the entire firing window. -/
lemma vert_droite (h : 4 ≤ n) :
    Verticale 1 (n : ℤ) (2 * n - 3) (G_Etat n) := by
  have hb := base2 n h
  have hv := Ht1_VV n 0 (n : ℤ) (n - 2) hb
  -- `hv : Verticale (0 + 1) n (double (n - 2) + 1) (G_Etat n)`
  have et : (0 : ℕ) + 1 = 1 := by omega
  have eh : double (n - 2) + 1 = 2 * n - 3 := by unfold double; omega
  rw [et, eh] at hv
  exact hv

/-- Single-cell extraction: column `n` is `G` at the firing time. -/
lemma GN1 (h : 4 ≤ n) :
    G_Etat n (2 * n - 3) (n : ℤ) := by
  have hv := vert_droite n h
  -- `hv.pointwise (2*n - 4)` gives `G_Etat n (1 + (2*n - 4)) n`
  have hpt := hv.pointwise (2 * n - 4) (by omega)
  have e : (1 : ℕ) + (2 * n - 4) = 2 * n - 3 := by omega
  rw [e] at hpt
  exact hpt

/-- The `2n − 3` row is all `G`. -/
lemma sommet_1 (h : 4 ≤ n) :
    Horizontale (2 * n - 3) 0 (n - 1) (G_Etat n) := by
  have hd := diagonale n h
  -- Crop the right-edge G-wall to the `n - 1` rows that `DD_Hg` consumes.
  have hv : Verticale (n - 2) (n : ℤ) (n - 1) (G_Etat n) :=
    inclus_vert 1 (n - 2) (n : ℤ) (2 * n - 3) (n - 1) (G_Etat n)
      (by omega) (by omega) (vert_droite n h)
  -- Reshape `hv` to the exact form `DD_Hg` expects:
  -- `Verticale ((n - 3) + 1) ((0 : ℤ) + ((n - 1 : ℕ) : ℤ) + 1) (n - 1) ...`
  have hvshape : Verticale ((n - 3) + 1) ((0 : ℤ) + ((n - 1 : ℕ) : ℤ) + 1)
                          (n - 1) (G_Etat n) := by
    have et : (n - 3) + 1 = n - 2 := by omega
    have ex : (0 : ℤ) + ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by
      have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; rfl
      rw [hcast]; ring
    rw [et, ex]; exact hv
  -- Apply the apex theorem.
  have hg : Horizontale ((n - 3) + (n - 1) + 1) 0 (n - 1) (G_Etat n) :=
    DD_Hg n (n - 3) 0 (n - 1) hd hvshape
  have et : (n - 3) + (n - 1) + 1 = 2 * n - 3 := by omega
  rw [et] at hg
  exact hg

/-- The final theorem: at time `2(n - 1) = 2n − 2`, every cell
    `0 .. n − 1` is in state `F`. -/
theorem firing_squad (h : 4 ≤ n) :
    Horizontale (2 * n - 2) 0 (n - 1) (F_Etat n) := by
  have hs := sommet_1 n h
  have hg := GN1 n h
  -- `Hg_Hf` expects the right-edge G at column `((n - 1 : ℕ) + 1 : ℤ) = (n : ℤ)`.
  have hg' : G_Etat n (2 * n - 3) (((n - 1 : ℕ) : ℤ) + 1) := by
    have e : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by
      have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; rfl
      rw [hcast]; ring
    rw [e]; exact hg
  have hf : Horizontale ((2 * n - 3) + 1) 0 (n - 1) (F_Etat n) :=
    Hg_Hf n (2 * n - 3) (n - 1) (by omega) hs hg'
  have et : (2 * n - 3) + 1 = 2 * n - 2 := by omega
  rw [et] at hf
  exact hf

end FsspMazoyer
end CellularAutomatas
