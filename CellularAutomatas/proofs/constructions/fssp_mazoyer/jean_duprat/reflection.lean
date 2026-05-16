/-
  Mazoyer FSSP -- the "above-the-brick" wedge predicates `UA`, `UAB`,
  `ZCB`, plus `*_Vg` walls.

  Lean 4 port of `reflection.v` from Jean Duprat's Coq proof of the
  Firing Squad Synchronization Problem (Mazoyer's solution).
  Original source: https://github.com/rocq-archive/firing-squad
  Commit: 821676dce0353798b0651d058ffb22b65fb09097
  License: LGPL 2.1
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.jean_duprat.basic_bricks

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

variable (n : ℕ)

/-! ### `loi` / `loi_droite` lifters (redeclared private; the analogues in
    `basic_bricks.lean` are private and not visible here). -/

private lemma loi_etat (a b c d : Couleur) (hδ : δ a b c = d) :
    loi (fun (t : ℕ) (x : ℤ) => Etat n t x = a)
        (fun (t : ℕ) (x : ℤ) => Etat n t x = b)
        (fun (t : ℕ) (x : ℤ) => Etat n t x = c)
        (fun (t : ℕ) (x : ℤ) => Etat n t x = d) := by
  intro t x hP hQ hR
  show Etat n (t + 1) (x + 1) = d
  rw [un_pas]
  have eL : (x + 1 - 1 : ℤ) = x := by ring
  have eR : (x + 1 + 1 : ℤ) = x + 2 := by ring
  rw [eL, eR, hP, hQ, hR, hδ]

private lemma loi_droite_etat (q r s : Couleur) (h : ∀ c : Couleur, δ c q r = s) :
    loi_droite (fun (t : ℕ) (x : ℤ) => Etat n t x = q)
               (fun (t : ℕ) (x : ℤ) => Etat n t x = r)
               (fun (t : ℕ) (x : ℤ) => Etat n t x = s) := by
  intro t x hQ hR
  show Etat n (t + 1) x = s
  rw [un_pas, hQ, hR]
  exact h (Etat n t (x - 1))

private lemma δ_GB_G : ∀ c : Couleur, δ c G B = G := by intro c; cases c <;> rfl
private lemma δ_GC_G : ∀ c : Couleur, δ c G C = G := by intro c; cases c <;> rfl

/-! ### Wedge predicates -/

/-- `UA t x cote` -- a `Diag` of `G/A/G` of side `cote`. -/
structure UA (t : ℕ) (x : ℤ) (cote : ℕ) : Prop where
  size  : 1 < cote
  diag  : Diag t x cote (G_Etat n) (A_Etat n) (G_Etat n)

/-- `UAB t x cote` -- a `Diag'` of `G/G/B/G` (top row carries `G`)
    plus a `Diag` of `G/A/G` one step later. -/
structure UAB (t : ℕ) (x : ℤ) (cote : ℕ) : Prop where
  size  : 2 < cote
  diag0 : Diag' t      x cote (G_Etat n) (G_Etat n) (B_Etat n) (G_Etat n)
  diag1 : Diag (t + 1) x cote (G_Etat n) (A_Etat n) (G_Etat n)

/-- `ZCB t x cote` -- a `Diag` of `G/C/G` plus a `Diag` of `G/B/G`. -/
structure ZCB (t : ℕ) (x : ℤ) (cote : ℕ) : Prop where
  size  : 1 < cote
  diag0 : Diag t       x cote (G_Etat n) (C_Etat n) (G_Etat n)
  diag1 : Diag (t + 1) x cote (G_Etat n) (B_Etat n) (G_Etat n)

/-! ### Constructions: brick + G-wall on the right ⇒ wedge -/

lemma B_UA (t : ℕ) (x : ℤ) (cote : ℕ) :
    B_basic n t x cote →
    G_Etat n (t + 1) ((x + 1) + cote) →
    UA n (t + 1) (x + 1) cote := by
  intro h hg
  -- D'D_D needs three loi premises (hRPPQ, hQQQQ, hPQQP).
  have hRPPQ : loi (G_Etat n) (L_Etat n) (G_Etat n) (A_Etat n) :=
    loi_etat n G L G A rfl
  have hQQQQ : loi (B_Etat n) (B_Etat n) (A_Etat n) (A_Etat n) :=
    loi_etat n B B A A rfl
  have hPQQP : loi (L_Etat n) (B_Etat n) (A_Etat n) (G_Etat n) :=
    loi_etat n L B A G rfl
  -- Combine `B_basic` diags via `D'D_D` to obtain G/A/G triangle one row down.
  have d :
      Diag (t + 1) (x + 1) cote (G_Etat n) (A_Etat n) (G_Etat n) :=
    D'D_D t x cote (L_Etat n) (B_Etat n) (G_Etat n) (L_Etat n) (B_Etat n)
          (G_Etat n) (A_Etat n) hRPPQ hQQQQ hPQQP h.diag0 h.diag1 hg
  have hs : 1 < cote := by have := h.size; omega
  exact ⟨hs, d⟩

lemma C_UAB (t : ℕ) (x : ℤ) (cote : ℕ) :
    2 < cote →
    C_basic n t x cote →
    G_Etat n (t + 1) ((x + 1) + cote) →
    G_Etat n (t + 2) ((x + 1) + cote) →
    UAB n (t + 1) (x + 1) cote := by
  intro hcote h hg1 hg2
  -- DD_D' needs four loi premises (hQPPR, hQQRQ, hQQQQ, hPQQP).
  have hQPPR : loi (C_Etat n) (L_Etat n) (G_Etat n) (G_Etat n) :=
    loi_etat n C L G G rfl
  have hQQRQ : loi (C_Etat n) (C_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n C C G B rfl
  have hQQQQ : loi (C_Etat n) (C_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n C C B B rfl
  have hPQQP : loi (L_Etat n) (C_Etat n) (B_Etat n) (G_Etat n) :=
    loi_etat n L C B G rfl
  -- D_D'D needs three loi premises (hQRPQ, hQQQQ, hPPQP).
  have hQRPQ : loi (C_Etat n) (G_Etat n) (G_Etat n) (A_Etat n) :=
    loi_etat n C G G A rfl
  have hQQQQ' : loi (C_Etat n) (B_Etat n) (A_Etat n) (A_Etat n) :=
    loi_etat n C B A A rfl
  have hPPQP : loi (L_Etat n) (G_Etat n) (A_Etat n) (G_Etat n) :=
    loi_etat n L G A G rfl
  -- Top: `DD_D'` produces the `Diag'` row at t+1.
  have d0 :
      Diag' (t + 1) (x + 1) cote (G_Etat n) (G_Etat n) (B_Etat n) (G_Etat n) :=
    DD_D' t x cote (L_Etat n) (C_Etat n) (L_Etat n) (C_Etat n)
          (G_Etat n) (G_Etat n) (B_Etat n)
          hQPPR hQQRQ hQQQQ hPQQP hcote h.diag0 h.diag1 hg1
  -- Below: `D_D'D` makes the next row (a `Diag` of G/A/G).
  have d1 :
      Diag (t + 2) (x + 1) cote (G_Etat n) (A_Etat n) (G_Etat n) :=
    D_D'D (t + 1) x cote (L_Etat n) (C_Etat n) (G_Etat n) (G_Etat n) (B_Etat n)
          (G_Etat n) (A_Etat n) hQRPQ hQQQQ' hPPQP h.diag1 d0 hg2
  exact ⟨hcote, d0, d1⟩

lemma A_ZCB (t : ℕ) (x : ℤ) (cote : ℕ) :
    A_basic n t x cote →
    G_Etat n (t + 1) ((x + 1) + cote) →
    G_Etat n (t + 2) ((x + 1) + cote) →
    ZCB n (t + 1) (x + 1) cote := by
  intro h hg1 hg2
  -- DD_D needs three loi premises (hQPPQ, hQQQQ, hPQQP).
  have hQPPQ : loi (A_Etat n) (L_Etat n) (G_Etat n) (C_Etat n) :=
    loi_etat n A L G C rfl
  have hQQQQ : loi (A_Etat n) (A_Etat n) (C_Etat n) (C_Etat n) :=
    loi_etat n A A C C rfl
  have hPQQP : loi (L_Etat n) (A_Etat n) (C_Etat n) (G_Etat n) :=
    loi_etat n L A C G rfl
  -- D_DD needs three loi premises (hQQPQ', hQQQQ', hPPQP).
  have hQQPQ' : loi (A_Etat n) (C_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n A C G B rfl
  have hQQQQ' : loi (A_Etat n) (C_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n A C B B rfl
  have hPPQP : loi (L_Etat n) (G_Etat n) (B_Etat n) (G_Etat n) :=
    loi_etat n L G B G rfl
  -- Diag G/C/G via `DD_D` from the two A-rows.
  have d0 :
      Diag (t + 1) (x + 1) cote (G_Etat n) (C_Etat n) (G_Etat n) :=
    DD_D t x cote (L_Etat n) (A_Etat n) (L_Etat n) (A_Etat n)
         (G_Etat n) (C_Etat n) hQPPQ hQQQQ hPQQP h.size h.diag0 h.diag1 hg1
  -- Diag G/B/G via `D_DD` combining the A-row at t+1 with the new G/C/G row.
  have d1 :
      Diag (t + 2) (x + 1) cote (G_Etat n) (B_Etat n) (G_Etat n) :=
    D_DD (t + 1) x cote (L_Etat n) (A_Etat n) (G_Etat n) (C_Etat n)
         (G_Etat n) (B_Etat n) hQQPQ' hQQQQ' hPPQP h.diag1 d0 hg2
  have hs : 1 < cote := by have := h.size; omega
  exact ⟨hs, d0, d1⟩

lemma B_ZCB (t : ℕ) (x : ℤ) (cote : ℕ) :
    B_basic n t x cote →
    G_Etat n (t + 1) ((x + 1) + cote) →
    G_Etat n (t + 2) ((x + 1) + cote) →
    G_Etat n (t + 3) ((x + 1) + cote) →
    ZCB n (t + 2) (x + 1) cote := by
  intro h hg1 hg2 hg3
  -- First obtain the G/A/G triangle one row above via `B_UA`.
  have hUA : UA n (t + 1) (x + 1) cote := B_UA n t x cote h hg1
  -- D_DD needs three loi premises (hQQPQ, hQQQQ, hPPQP).
  have hQQPQ : loi (B_Etat n) (A_Etat n) (G_Etat n) (C_Etat n) :=
    loi_etat n B A G C rfl
  have hQQQQ : loi (B_Etat n) (A_Etat n) (C_Etat n) (C_Etat n) :=
    loi_etat n B A C C rfl
  have hPPQP : loi (L_Etat n) (G_Etat n) (C_Etat n) (G_Etat n) :=
    loi_etat n L G C G rfl
  -- DDD needs four loi premises plus a loi_droite.
  have hPQPQ : loi (G_Etat n) (C_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n G C G B rfl
  have hQQPQ' : loi (A_Etat n) (C_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n A C G B rfl
  have hQQQQ' : loi (A_Etat n) (C_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n A C B B rfl
  have hPQQQ : loi (G_Etat n) (C_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n G C B B rfl
  have hXPQP : loi_droite (G_Etat n) (B_Etat n) (G_Etat n) :=
    loi_droite_etat n G B G δ_GB_G
  -- Diag G/C/G via `D_DD` combining B-row at t+1 with the UA triangle.
  have d0 :
      Diag (t + 2) (x + 1) cote (G_Etat n) (C_Etat n) (G_Etat n) :=
    D_DD (t + 1) x cote (L_Etat n) (B_Etat n) (G_Etat n) (A_Etat n)
         (G_Etat n) (C_Etat n) hQQPQ hQQQQ hPPQP h.diag1 hUA.diag hg2
  -- Diag G/B/G via `DDD` from the UA triangle and the new G/C/G triangle.
  have d1 :
      Diag (t + 3) (x + 1) cote (G_Etat n) (B_Etat n) (G_Etat n) :=
    DDD (t + 1) (x + 1) cote (G_Etat n) (A_Etat n) (G_Etat n) (C_Etat n)
        (G_Etat n) (B_Etat n) hPQPQ hQQPQ' hQQQQ' hPQQQ hXPQP hUA.diag d0 hg3
  have hs : 1 < cote := by have := h.size; omega
  exact ⟨hs, d0, d1⟩

lemma C_ZCB (t : ℕ) (x : ℤ) (cote : ℕ) :
    2 < cote →
    C_basic n t x cote →
    G_Etat n (t + 1) ((x + 1) + cote) →
    G_Etat n (t + 2) ((x + 1) + cote) →
    G_Etat n (t + 3) ((x + 1) + cote) →
    G_Etat n (t + 4) ((x + 1) + cote) →
    ZCB n (t + 3) (x + 1) cote := by
  intro hcote h hg1 hg2 hg3 hg4
  -- First obtain the UAB wedge above via `C_UAB`.
  have hUAB : UAB n (t + 1) (x + 1) cote := C_UAB n t x cote hcote h hg1 hg2
  -- D'DD needs three loi premises plus a loi_droite.
  have hQQPQ : loi (B_Etat n) (A_Etat n) (G_Etat n) (C_Etat n) :=
    loi_etat n B A G C rfl
  have hQQQQ : loi (B_Etat n) (A_Etat n) (C_Etat n) (C_Etat n) :=
    loi_etat n B A C C rfl
  have hPQQQ : loi (G_Etat n) (A_Etat n) (C_Etat n) (C_Etat n) :=
    loi_etat n G A C C rfl
  have hXPQP_C : loi_droite (G_Etat n) (C_Etat n) (G_Etat n) :=
    loi_droite_etat n G C G δ_GC_G
  -- DDD needs four loi premises plus a loi_droite.
  have hPQPQ : loi (G_Etat n) (C_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n G C G B rfl
  have hQQPQ' : loi (A_Etat n) (C_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n A C G B rfl
  have hQQQQ' : loi (A_Etat n) (C_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n A C B B rfl
  have hPQQQ' : loi (G_Etat n) (C_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n G C B B rfl
  have hXPQP_B : loi_droite (G_Etat n) (B_Etat n) (G_Etat n) :=
    loi_droite_etat n G B G δ_GB_G
  -- Diag G/C/G via `D'DD` combining the Diag' G/G/B/G with the Diag G/A/G.
  have d0 :
      Diag (t + 3) (x + 1) cote (G_Etat n) (C_Etat n) (G_Etat n) :=
    D'DD (t + 1) (x + 1) cote (G_Etat n) (B_Etat n) (G_Etat n) (G_Etat n) (A_Etat n)
         (G_Etat n) (C_Etat n) hQQPQ hQQQQ hPQQQ hXPQP_C hUAB.diag0 hUAB.diag1 hg3
  -- Diag G/B/G via `DDD` from the G/A/G and G/C/G triangles.
  have d1 :
      Diag (t + 4) (x + 1) cote (G_Etat n) (B_Etat n) (G_Etat n) :=
    DDD (t + 2) (x + 1) cote (G_Etat n) (A_Etat n) (G_Etat n) (C_Etat n)
        (G_Etat n) (B_Etat n) hPQPQ hQQPQ' hQQQQ' hPQQQ' hXPQP_B hUAB.diag1 d0 hg4
  have hs : 1 < cote := by omega
  exact ⟨hs, d0, d1⟩

/-! ### Strip-peeling lemmas -/

lemma ZCB_GLC (t : ℕ) (x : ℤ) (cote : ℕ) :
    2 < cote →
    ZCB n t x cote →
    Verticale (t + 2) (x + cote) cote (G_Etat n) →
    Diag ((t + 1) + 1) (x + 1) (cote - 1) (G_Etat n) (L_Etat n) (C_Etat n) := by
  intro hcote hZ hV
  have hcs   : (cote - 1) + 1 = cote := by omega
  have h1c   : 1 < cote - 1 := by omega
  -- Reform the two ZCB diags as `(cote - 1) + 1`.
  have d0 : Diag t x ((cote - 1) + 1) (G_Etat n) (C_Etat n) (G_Etat n) := by
    rw [hcs]; exact hZ.diag0
  have d1 : Diag (t + 1) x ((cote - 1) + 1) (G_Etat n) (B_Etat n) (G_Etat n) := by
    rw [hcs]; exact hZ.diag1
  -- The corner G at (t + 2, x + cote), reformed as `(x + (cote - 1)) + 1`.
  have hG : G_Etat n (t + 2) ((x + (cote - 1 : ℕ)) + 1) := by
    have h := hV.pointwise 0 (by omega)
    have hge : 1 ≤ cote := by omega
    have eq : (x + ((cote - 1 : ℕ) : ℤ)) + 1 = x + ((cote : ℕ) : ℤ) := by
      rw [Nat.cast_sub hge]; push_cast; ring
    rw [eq]; exact h
  -- DDdollar_D needs three loi premises (hQQPQ, hQQQQ, hPQQR).
  have hQQPQ : loi (C_Etat n) (B_Etat n) (G_Etat n) (L_Etat n) :=
    loi_etat n C B G L rfl
  have hQQQQ : loi (C_Etat n) (B_Etat n) (L_Etat n) (L_Etat n) :=
    loi_etat n C B L L rfl
  have hPQQR : loi (G_Etat n) (B_Etat n) (L_Etat n) (C_Etat n) :=
    loi_etat n G B L C rfl
  -- Combine via `DDdollar_D` with `cote' := cote - 1`.
  exact DDdollar_D t x (cote - 1)
        (G_Etat n) (C_Etat n) (G_Etat n) (B_Etat n)
        (G_Etat n) (L_Etat n) (C_Etat n)
        hQQPQ hQQQQ hPQQR h1c d0 d1 hG

lemma ZCB_l (t : ℕ) (x : ℤ) (cote : ℕ) :
    2 < cote →
    ZCB n t x cote →
    Verticale (t + 2) (x + cote) cote (G_Etat n) →
    Semi_Diag ((t + 1) + 2) (x + 2) (cote - 2) (G_Etat n) (L_Etat n) := by
  intro hcote hZ hV
  have h0    : 0 < cote - 2 := by omega
  have hcs2  : (cote - 2) + 2 = cote := by omega
  have hcs1  : (cote - 2) + 1 = cote - 1 := by omega
  -- Reform the B-diag as `(cote-2) + 2`.
  have d0 : Diag (t + 1) x ((cote - 2) + 2) (G_Etat n) (B_Etat n) (G_Etat n) := by
    rw [hcs2]; exact hZ.diag1
  -- The G/L/C triangle of side (cote-1) from `ZCB_GLC`, reformed as `(cote-2)+1`.
  have dGLC := ZCB_GLC n t x cote hcote hZ hV
  have d1 : Diag ((t + 1) + 1) (x + 1) ((cote - 2) + 1)
              (G_Etat n) (L_Etat n) (C_Etat n) := by
    rw [hcs1]; exact dGLC
  -- The G corner at (t+3, x + cote), reformed as `(x + (cote-2)) + 2`.
  have hG : G_Etat n ((t + 1) + 2) ((x + (cote - 2 : ℕ)) + 2) := by
    have h := hV.pointwise 1 (by omega)
    have hge : 2 ≤ cote := by omega
    have eq_x : (x + ((cote - 2 : ℕ) : ℤ)) + 2 = x + ((cote : ℕ) : ℤ) := by
      rw [Nat.cast_sub hge]; push_cast; ring
    have eq_t : (t + 2) + 1 = (t + 1) + 2 := by omega
    rw [eq_x, ← eq_t]; exact h
  -- DD_d needs two loi premises (hQQPQ, hQQQQ).
  have hQQPQ : loi (B_Etat n) (L_Etat n) (G_Etat n) (L_Etat n) :=
    loi_etat n B L G L rfl
  have hQQQQ : loi (B_Etat n) (L_Etat n) (L_Etat n) (L_Etat n) :=
    loi_etat n B L L L rfl
  -- Combine via `DD_d` with `cote' := cote - 2`.
  exact DD_d (t + 1) x (cote - 2)
        (G_Etat n) (B_Etat n) (G_Etat n)
        (G_Etat n) (L_Etat n) (C_Etat n)
        (G_Etat n) (L_Etat n)
        hQQPQ hQQQQ h0 d0 d1 hG

lemma ZCB_ll (t : ℕ) (x : ℤ) (cote : ℕ) :
    3 < cote →
    ZCB n t x cote →
    Verticale (t + 2) (x + cote) cote (G_Etat n) →
    Semi_Diag ((t + 1) + 3) (x + 3) (cote - 3) (G_Etat n) (L_Etat n) := by
  intro hcote hZ hV
  have h0    : 0 < cote - 3 := by omega
  have hcs2  : (cote - 3) + 2 = cote - 1 := by omega
  have hcs1  : (cote - 3) + 1 = cote - 2 := by omega
  -- The G/L/C triangle of side (cote-1), reformed as `(cote-3)+2`.
  have dGLC := ZCB_GLC n t x cote (by omega) hZ hV
  have d0 : Diag (t + 2) (x + 1) ((cote - 3) + 2)
              (G_Etat n) (L_Etat n) (C_Etat n) := by
    rw [hcs2]; exact dGLC
  -- The G/L semi-diag of side (cote-2) from `ZCB_l`, reformed as `(cote-3)+1`.
  have dL := ZCB_l n t x cote (by omega) hZ hV
  have d1 : Semi_Diag ((t + 2) + 1) ((x + 1) + 1) ((cote - 3) + 1)
              (G_Etat n) (L_Etat n) := by
    rw [hcs1]
    have eq_t : (t + 2) + 1 = (t + 1) + 2 := by omega
    have eq_x : ((x : ℤ) + 1) + 1 = x + 2 := by ring
    rw [eq_t, eq_x]; exact dL
  -- The G corner at (t+4, x + cote), reformed as `((x+1) + (cote-3)) + 2`.
  have hG : G_Etat n ((t + 2) + 2) (((x + 1) + (cote - 3 : ℕ)) + 2) := by
    have h := hV.pointwise 2 (by omega)
    have hge : 3 ≤ cote := by omega
    have eq_x : ((x + 1 : ℤ) + ((cote - 3 : ℕ) : ℤ)) + 2 = x + ((cote : ℕ) : ℤ) := by
      rw [Nat.cast_sub hge]; push_cast; ring
    rw [eq_x]; exact h
  -- Dd_d needs two loi premises (hQQPQ, hQQQQ).
  have hQQPQ : loi (L_Etat n) (L_Etat n) (G_Etat n) (L_Etat n) :=
    loi_etat n L L G L rfl
  have hQQQQ : loi (L_Etat n) (L_Etat n) (L_Etat n) (L_Etat n) :=
    loi_etat n L L L L rfl
  -- Combine via `Dd_d` with `cote' := cote - 3`; bridge time/space indices.
  have result := Dd_d (t + 2) (x + 1) (cote - 3)
        (G_Etat n) (L_Etat n) (C_Etat n)
        (G_Etat n) (L_Etat n)
        (G_Etat n) (L_Etat n)
        hQQPQ hQQQQ h0 d0 d1 hG
  -- result : Semi_Diag ((t+2)+2) ((x+1)+2) (cote-3) G L
  -- goal   : Semi_Diag ((t+1)+3) (x+3)     (cote-3) G L
  have eq_t : (t + 2) + 2 = (t + 1) + 3 := by omega
  have eq_x : ((x : ℤ) + 1) + 2 = x + 3 := by ring
  rw [eq_t, eq_x] at result
  exact result

lemma ZCB_lll (t : ℕ) (x : ℤ) (cote : ℕ) (dcote : ℕ) :
    2 ≤ dcote → dcote < cote →
    ZCB n t x cote →
    Verticale (t + 2) (x + cote) cote (G_Etat n) →
    Semi_Diag ((t + 1) + dcote) (x + dcote) (cote - dcote) (G_Etat n) (L_Etat n) := by
  intro hge hlt hZ hV
  -- Inductive predicate: every dcote ≥ 2 below cote yields a Semi_Diag.
  let P : ℕ → Prop := fun p =>
    p < cote → Semi_Diag ((t + 1) + p) (x + (p : ℕ)) (cote - p) (G_Etat n) (L_Etat n)
  -- Base cases at p = 2 and p = 3.
  have base2 : P 2 := fun _ => ZCB_l n t x cote (by omega) hZ hV
  have base3 : P 3 := fun hlt3 => ZCB_ll n t x cote hlt3 hZ hV
  -- Step: P p ∧ P (p+1) ⇒ P (p+2), via `dd_d`.
  have step : ∀ p : ℕ, P p → P (p + 1) → P (p + 2) := by
    intro p hp1 hp2 hp_lt
    have sd1 := hp1 (by omega)
    have sd2 := hp2 (by omega)
    have h0 : 0 < cote - (p + 2) := by omega
    have hcs2 : (cote - (p + 2)) + 2 = cote - p := by omega
    have hcs1 : (cote - (p + 2)) + 1 = cote - (p + 1) := by omega
    have d0' : Semi_Diag ((t + 1) + p) (x + (p : ℕ))
                  ((cote - (p + 2)) + 2) (G_Etat n) (L_Etat n) := by
      rw [hcs2]; exact sd1
    have d1' : Semi_Diag (((t + 1) + p) + 1) ((x + ((p : ℕ) : ℤ)) + 1)
                  ((cote - (p + 2)) + 1) (G_Etat n) (L_Etat n) := by
      rw [hcs1]
      have eq_t : ((t + 1) + p) + 1 = (t + 1) + (p + 1) := by omega
      have eq_x : (x + ((p : ℕ) : ℤ)) + 1 = x + (((p + 1 : ℕ)) : ℤ) := by
        push_cast; ring
      rw [eq_t, eq_x]; exact sd2
    have hG' : G_Etat n (((t + 1) + p) + 2)
                  (((x + ((p : ℕ) : ℤ)) + ((cote - (p + 2) : ℕ) : ℤ)) + 2) := by
      have h := hV.pointwise (p + 1) (by omega)
      have eq_t : (t + 2) + (p + 1) = ((t + 1) + p) + 2 := by omega
      have hge_p : p + 2 ≤ cote := by omega
      have eq_x : ((x + ((p : ℕ) : ℤ)) + ((cote - (p + 2) : ℕ) : ℤ)) + 2
                    = x + ((cote : ℕ) : ℤ) := by
        rw [Nat.cast_sub hge_p]; push_cast; ring
      rw [eq_x, ← eq_t]; exact h
    -- dd_d needs two loi premises (hQQPQ, hQQQQ).
    have hQQPQ : loi (L_Etat n) (L_Etat n) (G_Etat n) (L_Etat n) :=
      loi_etat n L L G L rfl
    have hQQQQ : loi (L_Etat n) (L_Etat n) (L_Etat n) (L_Etat n) :=
      loi_etat n L L L L rfl
    have result := dd_d ((t + 1) + p) (x + ((p : ℕ) : ℤ)) (cote - (p + 2))
                        (G_Etat n) (L_Etat n) (G_Etat n) (L_Etat n)
                        (G_Etat n) (L_Etat n)
                        hQQPQ hQQQQ h0 d0' d1' hG'
    -- Bridge `((t+1)+p)+2 ↦ (t+1)+(p+2)` and `(x+↑p)+2 ↦ x+↑(p+2)`.
    have eq_t : ((t + 1) + p) + 2 = (t + 1) + (p + 2) := by omega
    have eq_x : (x + ((p : ℕ) : ℤ)) + 2 = x + (((p + 2 : ℕ)) : ℤ) := by
      push_cast; ring
    rw [← eq_t, ← eq_x]; exact result
  exact recur_nSn P 2 base2 base3 step dcote hge hlt

/-- `ZCB` + G-wall on the right ⇒ a `G C L^*` row at the bottom. -/
lemma ZCB_Ht1 (t : ℕ) (x : ℤ) (cote : ℕ) :
    2 < cote →
    ZCB n t x cote →
    Verticale (t + 2) (x + cote) cote (G_Etat n) →
    Horizontale_t1 (t + (cote + 1)) x (cote - 3)
      (G_Etat n) (C_Etat n) (L_Etat n) := by
  intro hcote hZ hV
  refine ⟨?_, ?_, ?_⟩
  · -- head : G_Etat n (t + (cote+1)) x = bottomLeft of `Diag (t+1) x cote G B G`.
    have h := hZ.diag1.bottomLeft
    have eq : (t + 1) + cote = t + (cote + 1) := by omega
    rw [← eq]; exact h
  · -- next1 : C_Etat n (t + (cote+1)) (x+1) = bottomLeft of ZCB_GLC.
    have hGLC := ZCB_GLC n t x cote hcote hZ hV
    have h := hGLC.bottomLeft
    have eq : ((t + 1) + 1) + (cote - 1) = t + (cote + 1) := by omega
    rw [← eq]; exact h
  · -- tail : Horizontale (t + (cote+1)) (x+2) (cote-3) L_Etat.
    refine ⟨fun dx hdx => ?_⟩
    have hd_lt : dx + 2 < cote := by omega
    have hd_ge : 2 ≤ dx + 2 := by omega
    have hLll := ZCB_lll n t x cote (dx + 2) hd_ge hd_lt hZ hV
    -- Take the bottom-left cell of this trapezoid.
    have hpos : 0 < cote - (dx + 2) := by omega
    have h := hLll.interior (cote - (dx + 2)) 0 hpos (by omega)
    -- Rewrite indices into the goal's form.
    have eq_t : ((t + 1) + (dx + 2)) + (cote - (dx + 2)) = t + (cote + 1) := by omega
    have eq_x : ((x + (((dx + 2 : ℕ)) : ℤ)) + (((0 : ℕ)) : ℤ)) = (x + 2) + (dx : ℤ) := by
      push_cast; ring
    rw [eq_t, eq_x] at h
    exact h

/-! ### G-walls produced by bricks (`*_Vg`) -/

lemma A_Vg (t : ℕ) (x : ℤ) (cote : ℕ) :
    A_basic n t x cote →
    G_Etat n (t + 1) ((x + 1) + cote) →
    G_Etat n (t + 2) ((x + 1) + cote) →
    Verticale ((t + 1) + cote) (x + 1) 1 (G_Etat n) := by
  intro h hg1 hg2
  have hZ := A_ZCB n t x cote h hg1 hg2
  apply vert_un
  · exact hZ.diag0.bottomLeft
  · -- (t+1)+cote+1 = (t+2)+cote
    have h := hZ.diag1.bottomLeft
    have eq : ((t + 1) + cote) + 1 = (t + 2) + cote := by omega
    rw [eq]; exact h

lemma B_Vg (t : ℕ) (x : ℤ) (cote : ℕ) :
    B_basic n t x cote →
    G_Etat n (t + 1) ((x + 1) + cote) →
    G_Etat n (t + 2) ((x + 1) + cote) →
    G_Etat n (t + 3) ((x + 1) + cote) →
    Verticale ((t + 1) + cote) (x + 1) 2 (G_Etat n) := by
  intro h hg1 hg2 hg3
  have hUA  : UA  n (t + 1) (x + 1) cote := B_UA  n t x cote h hg1
  have hZCB : ZCB n (t + 2) (x + 1) cote := B_ZCB n t x cote h hg1 hg2 hg3
  apply vert_deux
  · exact hUA.diag.bottomLeft
  · have h := hZCB.diag0.bottomLeft
    have eq : ((t + 1) + cote) + 1 = (t + 2) + cote := by omega
    rw [eq]; exact h
  · have h := hZCB.diag1.bottomLeft
    have eq : ((t + 1) + cote) + 2 = (t + 3) + cote := by omega
    rw [eq]; exact h

lemma C_Vg (t : ℕ) (x : ℤ) (cote : ℕ) :
    2 < cote →
    C_basic n t x cote →
    G_Etat n (t + 1) ((x + 1) + cote) →
    G_Etat n (t + 2) ((x + 1) + cote) →
    G_Etat n (t + 3) ((x + 1) + cote) →
    G_Etat n (t + 4) ((x + 1) + cote) →
    Verticale ((t + 1) + cote) (x + 1) 3 (G_Etat n) := by
  intro hcote h hg1 hg2 hg3 hg4
  have hUAB : UAB n (t + 1) (x + 1) cote := C_UAB n t x cote hcote h hg1 hg2
  have hZCB : ZCB n (t + 3) (x + 1) cote := C_ZCB n t x cote hcote h hg1 hg2 hg3 hg4
  apply vert_trois
  · exact hUAB.diag0.bottomLeft
  · have h := hUAB.diag1.bottomLeft
    have eq : ((t + 1) + cote) + 1 = (t + 2) + cote := by omega
    rw [eq]; exact h
  · have h := hZCB.diag0.bottomLeft
    have eq : ((t + 1) + cote) + 2 = (t + 3) + cote := by omega
    rw [eq]; exact h
  · have h := hZCB.diag1.bottomLeft
    have eq : ((t + 1) + cote) + 3 = (t + 4) + cote := by omega
    rw [eq]; exact h

end FsspMazoyer
end CellularAutomatas
