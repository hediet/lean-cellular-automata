/-
  Mazoyer FSSP -- the apex theorem `DD_Hg` and `Hg_Hf`
  (port of `sommet.v`).
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.trapeze

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

variable (n : ℕ)

/-! ### Smallest-side cases (`cote = 3` and `cote = 4`) -/

section Quatre
variable (t : ℕ) (x : ℤ)
variable (He : quatre_end n t x) (Hv : Verticale (t + 1) (x + 4) 3 (G_Etat n))

include He Hv in
lemma C23 : C_Etat n (t + 2) (x + 3) := by
  -- δ at (t+2, x+3): left A (t+1, x+2), middle L (t+1, x+3), right G (t+1, x+4).
  have hA : Etat n (t + 1) (x + 2) = A := He.three.a2
  have hL : Etat n (t + 1) (x + 3) = L := He.l3b
  have hG : Etat n (t + 1) (x + 4) = G := by
    have h := Hv.pointwise 0 (Nat.zero_le _)
    simpa using h
  show Etat n (t + 2) (x + 3) = C
  change Etat n ((t + 1) + 1) (x + 3) = C
  rw [un_pas, show ((x + 3 : ℤ) - 1) = x + 2 from by ring,
      show ((x + 3 : ℤ) + 1) = x + 4 from by ring,
      hA, hL, hG]
  rfl

include He Hv in
lemma G32 : G_Etat n (t + 3) (x + 2) := by
  apply GC_G n (t + 2) (x + 2) He.three.g2
  show Etat n (t + 2) ((x + 2) + 1) = C
  rw [show ((x + 2 : ℤ) + 1) = x + 3 from by ring]
  exact C23 n t x He Hv

include He Hv in
private lemma quatre_B33 : B_Etat n (t + 3) (x + 3) := by
  have h := GC_dollarB n (t + 2) (x + 2) He.three.g2 ?_
  · show Etat n (t + 3) (x + 3) = B
    rw [show ((x : ℤ) + 3) = (x + 2) + 1 from by ring]
    exact h
  · show Etat n (t + 2) ((x + 2) + 1) = C
    rw [show ((x + 2 : ℤ) + 1) = x + 3 from by ring]
    exact C23 n t x He Hv

include He Hv in
lemma quatre_Hg : Horizontale (t + 4) x 3 (G_Etat n) := by
  have h0 : G_Etat n (t + 4) x := He.three.two.one.g1
  have hG30 : G_Etat n (t + 3) x := He.three.two.one.g0
  have hB31 : B_Etat n (t + 3) (x + 1) := He.three.two.b1
  have hG32 : G_Etat n (t + 3) (x + 2) := G32 n t x He Hv
  have h1 : G_Etat n (t + 4) (x + 1) :=
    GBG_dollarG n (t + 3) x hG30 hB31 hG32
  have hB33 : B_Etat n (t + 3) (x + 3) := quatre_B33 n t x He Hv
  have h2 : G_Etat n (t + 4) (x + 2) := by
    apply GB_G n (t + 3) (x + 2) hG32
    show Etat n (t + 3) ((x + 2) + 1) = B
    rw [show ((x + 2 : ℤ) + 1) = x + 3 from by ring]
    exact hB33
  have hG34 : G_Etat n (t + 3) (x + 4) := Hv.pointwise 2 (by omega)
  have h3 : G_Etat n (t + 4) (x + 3) := by
    have h := GBG_dollarG n (t + 3) (x + 2) hG32 ?_ ?_
    · show Etat n (t + 4) (x + 3) = G
      rw [show ((x : ℤ) + 3) = (x + 2) + 1 from by ring]
      exact h
    · show Etat n (t + 3) ((x + 2) + 1) = B
      rw [show ((x + 2 : ℤ) + 1) = x + 3 from by ring]
      exact hB33
    · show Etat n (t + 3) ((x + 2) + 2) = G
      rw [show ((x + 2 : ℤ) + 2) = x + 4 from by ring]
      exact hG34
  exact hor_trois (t + 4) x (G_Etat n) h0 h1 h2 h3
end Quatre

section Cinq
variable (t : ℕ) (x : ℤ)
variable (He : cinq_end n t x) (Hv : Verticale (t + 1) (x + 5) 4 (G_Etat n))

include He Hv in
lemma A24 : A_Etat n (t + 2) (x + 4) := by
  have hG : Etat n (t + 1) (x + 3) = G := He.g3
  have hL : Etat n (t + 1) (x + 4) = L := He.l4b
  have hG2 : Etat n (t + 1) (x + 5) = G := by
    have h := Hv.pointwise 0 (Nat.zero_le _)
    simpa using h
  show Etat n (t + 2) (x + 4) = A
  change Etat n ((t + 1) + 1) (x + 4) = A
  rw [un_pas, show ((x + 4 : ℤ) - 1) = x + 3 from by ring,
      show ((x + 4 : ℤ) + 1) = x + 5 from by ring,
      hG, hL, hG2]
  rfl

include He Hv in
lemma B33 : B_Etat n (t + 3) (x + 3) := by
  have hA : Etat n (t + 2) (x + 2) = A := He.three.a2
  have hB : Etat n (t + 2) (x + 3) = B := He.b3
  have hA' : Etat n (t + 2) (x + 4) = A := A24 n t x He Hv
  show Etat n (t + 3) (x + 3) = B
  change Etat n ((t + 2) + 1) (x + 3) = B
  rw [un_pas, show ((x + 3 : ℤ) - 1) = x + 2 from by ring,
      show ((x + 3 : ℤ) + 1) = x + 4 from by ring,
      hA, hB, hA']
  rfl

include He Hv in
lemma C34 : C_Etat n (t + 3) (x + 4) := by
  have hB : Etat n (t + 2) (x + 3) = B := He.b3
  have hA : Etat n (t + 2) (x + 4) = A := A24 n t x He Hv
  have hG : Etat n (t + 2) (x + 5) = G := Hv.pointwise 1 (by omega)
  show Etat n (t + 3) (x + 4) = C
  change Etat n ((t + 2) + 1) (x + 4) = C
  rw [un_pas, show ((x + 4 : ℤ) - 1) = x + 3 from by ring,
      show ((x + 4 : ℤ) + 1) = x + 5 from by ring,
      hB, hA, hG]
  rfl

include He Hv in
lemma G42 : G_Etat n (t + 4) (x + 2) := by
  apply GB_G n (t + 3) (x + 2) He.three.g2
  show Etat n (t + 3) ((x + 2) + 1) = B
  rw [show ((x + 2 : ℤ) + 1) = x + 3 from by ring]
  exact B33 n t x He Hv

include He Hv in
lemma B43 : B_Etat n (t + 4) (x + 3) := by
  have h := GBC_dollarB n (t + 3) (x + 2) He.three.g2 ?_ ?_
  · show Etat n (t + 4) (x + 3) = B
    rw [show ((x : ℤ) + 3) = (x + 2) + 1 from by ring]
    exact h
  · show Etat n (t + 3) ((x + 2) + 1) = B
    rw [show ((x + 2 : ℤ) + 1) = x + 3 from by ring]
    exact B33 n t x He Hv
  · show Etat n (t + 3) ((x + 2) + 2) = C
    rw [show ((x + 2 : ℤ) + 2) = x + 4 from by ring]
    exact C34 n t x He Hv

include He Hv in
lemma G44 : G_Etat n (t + 4) (x + 4) := by
  have hB : Etat n (t + 3) (x + 3) = B := B33 n t x He Hv
  have hC : Etat n (t + 3) (x + 4) = C := C34 n t x He Hv
  have hG : Etat n (t + 3) (x + 5) = G := Hv.pointwise 2 (by omega)
  show Etat n (t + 4) (x + 4) = G
  change Etat n ((t + 3) + 1) (x + 4) = G
  rw [un_pas, show ((x + 4 : ℤ) - 1) = x + 3 from by ring,
      show ((x + 4 : ℤ) + 1) = x + 5 from by ring,
      hB, hC, hG]
  rfl

include He Hv in
lemma cinq_Hg : Horizontale (t + 5) x 4 (G_Etat n) := by
  have h0 : G_Etat n (t + 5) x := He.three.two.one.g1
  have hG40 : G_Etat n (t + 4) x := He.three.two.one.g0
  have hB41 : B_Etat n (t + 4) (x + 1) := He.three.two.b1
  have hG42 : G_Etat n (t + 4) (x + 2) := G42 n t x He Hv
  have h1 : G_Etat n (t + 5) (x + 1) :=
    GBG_dollarG n (t + 4) x hG40 hB41 hG42
  have hB43 : B_Etat n (t + 4) (x + 3) := B43 n t x He Hv
  have h2 : G_Etat n (t + 5) (x + 2) := by
    apply GB_G n (t + 4) (x + 2) hG42
    show Etat n (t + 4) ((x + 2) + 1) = B
    rw [show ((x + 2 : ℤ) + 1) = x + 3 from by ring]
    exact hB43
  have hG44 : G_Etat n (t + 4) (x + 4) := G44 n t x He Hv
  have h3 : G_Etat n (t + 5) (x + 3) := by
    have h := GBG_dollarG n (t + 4) (x + 2) hG42 ?_ ?_
    · show Etat n (t + 5) (x + 3) = G
      rw [show ((x : ℤ) + 3) = (x + 2) + 1 from by ring]
      exact h
    · show Etat n (t + 4) ((x + 2) + 1) = B
      rw [show ((x + 2 : ℤ) + 1) = x + 3 from by ring]
      exact hB43
    · show Etat n (t + 4) ((x + 2) + 2) = G
      rw [show ((x + 2 : ℤ) + 2) = x + 4 from by ring]
      exact hG44
  have hG45 : G_Etat n (t + 4) (x + 5) := Hv.pointwise 3 (by omega)
  have h4 : G_Etat n (t + 5) (x + 4) := by
    show Etat n (t + 5) (x + 4) = G
    change Etat n ((t + 4) + 1) (x + 4) = G
    rw [un_pas, show ((x + 4 : ℤ) - 1) = x + 3 from by ring,
        show ((x + 4 : ℤ) + 1) = x + 5 from by ring,
        hB43, hG44, hG45]
    rfl
  exact hor_quatre (t + 5) x (G_Etat n) h0 h1 h2 h3 h4
end Cinq

/-! ### Auxiliary arithmetic for the recursion -/

lemma R1_DDHg (m : ℕ) : 6 ≤ m → double (tiers m) - 1 < m := by
  intro h
  unfold double tiers
  omega

/-! ### The apex theorem

`DD t x cote + G-wall on the right` ⇒ all-`G` row of length `cote + 1`
at time `t + cote + 1`. Proved by strong induction on `cote`. -/

theorem DD_Hg (t : ℕ) (x : ℤ) (cote : ℕ) :
    DD n t x cote →
    Verticale (t + 1) (x + cote + 1) cote (G_Etat n) →
    Horizontale (t + cote + 1) x cote (G_Etat n) := by
  -- Strong induction on `cote` via `recur2`, with `(t, x)` quantified inside.
  have key : ∀ cote : ℕ, ∀ (t : ℕ) (x : ℤ), DD n t x cote →
      Verticale (t + 1) (x + cote + 1) cote (G_Etat n) →
      Horizontale (t + cote + 1) x cote (G_Etat n) := by
    intro cote
    apply recur2 (fun cote => ∀ (t : ℕ) (x : ℤ), DD n t x cote →
        Verticale (t + 1) (x + cote + 1) cote (G_Etat n) →
        Horizontale (t + cote + 1) x cote (G_Etat n))
    clear cote
    intro cote ih t x hDD hV
    cases hDD with
    | DD_4 t x he =>
      -- cote = 3.
      show Horizontale (t + 3 + 1) x 3 (G_Etat n)
      have hV' : Verticale (t + 1) (x + 4) 3 (G_Etat n) := by
        have heq : x + ((3 : ℕ) : ℤ) + 1 = x + 4 := by push_cast; ring
        rw [heq] at hV; exact hV
      exact quatre_Hg n t x he hV'
    | DD_5 t x he =>
      -- cote = 4.
      show Horizontale (t + 4 + 1) x 4 (G_Etat n)
      have hV' : Verticale (t + 1) (x + 5) 4 (G_Etat n) := by
        have heq : x + ((4 : ℕ) : ℤ) + 1 = x + 5 := by push_cast; ring
        rw [heq] at hV; exact hV
      exact cinq_Hg n t x he hV'
    | DD_A t x cote hle hmod hbrick hsubDD =>
      -- Setting `k := tiers cote`. `cote = double k + k` (Omod3).
      -- Decompose the goal via `hh_hor`: cote = (double k - 1 + 1) + k.
      -- Left:  IH on side `double k - 1`, with V from `Ha_Vg`.
      -- Right: cote = 6 (k = 2) → use `Ha3_Hg`;
      --        cote ≥ 9 (k ≥ 3) → IH on side `k`, with DD from `Ha_DD`.
      show Horizontale (t + cote + 1) x cote (G_Etat n)
      -- Arithmetic facts about `tiers cote` and `double (tiers cote)`.
      have hk2     : 2 ≤ tiers cote := le_tiers_six cote hle
      have hpd     : double (tiers cote) + tiers cote = cote :=
        plus_deuxtiers_untiers cote hmod
      have hd_pos  : 1 ≤ double (tiers cote) := lt_O_deuxtiers cote (by omega)
      have htriple : triple (tiers cote) = cote := by
        have := triple_tiers cote hmod; unfold triple; omega
      have hpd_int : ((double (tiers cote) : ℤ)) + (tiers cote : ℤ) = (cote : ℤ) := by
        exact_mod_cast hpd
      have hd_cast : ((double (tiers cote) - 1 : ℕ) : ℤ)
                   = (double (tiers cote) : ℤ) - 1 := by push_cast; omega
      -- Right wall feeding `Ha_Vg` and `Ha_DD`.
      have hVbrick : Verticale (t + 1)
          (((x + ((double (tiers cote) - 1 : ℕ) : ℤ)) + (tiers cote : ℕ)) + 2)
          (triple (tiers cote)) (G_Etat n) := by
        have hpos : (((x + ((double (tiers cote) - 1 : ℕ) : ℤ)) + (tiers cote : ℕ)) + 2)
                  = x + (cote : ℤ) + 1 := by
          rw [hd_cast]; push_cast; linarith
        rw [hpos, htriple]; exact hV
      -- Decompose cote = (double k - 1 + 1) + k for `hh_hor`. We reshape
      -- the conclusion (without rewriting `t + cote + 1`) via `suffices`,
      -- then apply `hh_hor` whose conclusion has the matching shape.
      have hsplit : (double (tiers cote) - 1 + 1) + tiers cote = cote := by omega
      suffices hgoal : Horizontale (t + cote + 1) x
          ((double (tiers cote) - 1 + 1) + tiers cote) (G_Etat n) by
        rw [hsplit] at hgoal; exact hgoal
      apply hh_hor (t + cote + 1) x (double (tiers cote) - 1) (tiers cote) (G_Etat n)
      · -- Left: Horizontale (t + cote + 1) x (double k - 1) G.
        have hp_lt : double (tiers cote) - 1 < cote := R1_DDHg cote hle
        have hVsub : Verticale ((t + tiers cote + 1) + 1)
                     (x + ((double (tiers cote) - 1 : ℕ) : ℤ) + 1)
                     (double (tiers cote) - 1) (G_Etat n) := by
          have h := Ha_Vg n t (x + ((double (tiers cote) - 1 : ℕ) : ℤ)) (tiers cote)
                    hbrick hVbrick
          have ht : (t + tiers cote) + 2 = (t + tiers cote + 1) + 1 := by omega
          rw [ht] at h; exact h
        have hH := ih (double (tiers cote) - 1) hp_lt
                     (t + tiers cote + 1) x hsubDD hVsub
        have ht : (t + tiers cote + 1) + (double (tiers cote) - 1) + 1 = t + cote + 1 := by
          omega
        rw [ht] at hH; exact hH
      · -- Right: Horizontale (t + cote + 1) (x + ↑(double k - 1) + 1) k G.
        rcases Nat.lt_or_ge 2 (tiers cote) with hk_gt | hk_le
        · -- k ≥ 3: IH on side `k` via `Ha_DD`.
          have hp_lt : tiers cote < cote := lt_tiersn_n cote (by omega)
          have hDDsub :=
            Ha_DD n t (x + ((double (tiers cote) - 1 : ℕ) : ℤ)) (tiers cote)
                  hk_gt hbrick hVbrick
          have hVsub : Verticale ((t + double (tiers cote)) + 1)
                       ((x + ((double (tiers cote) - 1 : ℕ) : ℤ) + 1) + (tiers cote : ℕ) + 1)
                       (tiers cote) (G_Etat n) := by
            have h := inclus_vert (t + 1) ((t + double (tiers cote)) + 1)
                      (x + (cote : ℤ) + 1) cote (tiers cote) (G_Etat n)
                      (by omega) (by omega) hV
            have hpos : ((x + ((double (tiers cote) - 1 : ℕ) : ℤ) + 1) + (tiers cote : ℕ) + 1)
                      = x + (cote : ℤ) + 1 := by
              rw [hd_cast]; push_cast; linarith
            rw [hpos]; exact h
          have hH := ih (tiers cote) hp_lt (t + double (tiers cote))
                       ((x + ((double (tiers cote) - 1 : ℕ) : ℤ)) + 1) hDDsub hVsub
          have ht : (t + double (tiers cote)) + tiers cote + 1 = t + cote + 1 := by omega
          rw [ht] at hH; exact hH
        · -- k = 2 (cote = 6): use `Ha3_Hg`.
          have hk1   : tiers cote = 2 := by omega
          have hcote : cote = 6 := by
            have := hpd; rw [hk1] at this; unfold double at this; omega
          have hd_three : ((double (tiers cote) - 1 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) := by
            rw [hk1]; unfold double; norm_cast
          have hbrick' : A_basic n t (x + ((3 : ℕ) : ℤ)) 3 := by
            have h := hbrick
            rw [hd_three] at h
            have : tiers cote + 1 = 3 := by rw [hk1]
            rw [this] at h; exact h
          have hV' : Verticale (t + 1) (x + ((3 : ℕ) : ℤ) + 4) 6 (G_Etat n) := by
            have h := hV; rw [hcote] at h
            have heq : x + ((6 : ℕ) : ℤ) + 1 = x + ((3 : ℕ) : ℤ) + 4 := by push_cast; ring
            rw [heq] at h; exact h
          have hRes := Ha3_Hg n t (x + ((3 : ℕ) : ℤ)) hbrick' hV'
          -- Reshape to match the goal.
          have ht : t + 7 = t + cote + 1 := by omega
          rw [← ht, hd_three, hk1]
          exact hRes
    | DD_B t x cote hle hmod hbrick hsubDD =>
      -- `cote = double k + k + 1` (Unmod3). Decompose: cote = (double k + 1) + k.
      -- Left:  IH on side `double k`, with V from `Hb_Vg`.
      -- Right: cote = 7 (k = 2) → `Hb3_Hg`;
      --        cote ≥ 10 (k ≥ 3) → IH on side `k` with DD from `Hb_DD`.
      show Horizontale (t + cote + 1) x cote (G_Etat n)
      have hk2     : 2 ≤ tiers cote := by
        -- 7 ≤ cote ⇒ 2 ≤ tiers cote.
        have := le_tiers_six cote (by omega); exact this
      have hpd     : (double (tiers cote) + tiers cote) + 1 = cote :=
        Splus_deuxtiers_untiers cote hmod
      have htriple : triple (tiers cote) + 1 = cote := by
        have := Striple_tiers cote hmod; unfold triple; omega
      have hpd_int : ((double (tiers cote) : ℤ)) + (tiers cote : ℤ) + 1 = (cote : ℤ) := by
        exact_mod_cast hpd
      -- Right wall feeding `Hb_Vg` and `Hb_DD`.
      have hVbrick : Verticale (t + 1)
          (((x + ((double (tiers cote) : ℕ) : ℤ)) + (tiers cote : ℕ)) + 2)
          (triple (tiers cote) + 1) (G_Etat n) := by
        have hpos : (((x + ((double (tiers cote) : ℕ) : ℤ)) + (tiers cote : ℕ)) + 2)
                  = x + (cote : ℤ) + 1 := by
          push_cast; linarith
        rw [hpos, htriple]; exact hV
      -- Decompose cote = (double k + 1) + k.
      have hsplit : (double (tiers cote) + 1) + tiers cote = cote := by omega
      suffices hgoal : Horizontale (t + cote + 1) x
          ((double (tiers cote) + 1) + tiers cote) (G_Etat n) by
        rw [hsplit] at hgoal; exact hgoal
      apply hh_hor (t + cote + 1) x (double (tiers cote)) (tiers cote) (G_Etat n)
      · -- Left: Horizontale (t + cote + 1) x (double k) G.
        have hp_lt : double (tiers cote) < cote := lt_deuxtiersn_n cote (by omega)
        have hVsub : Verticale ((t + tiers cote + 1) + 1)
                     (x + ((double (tiers cote) : ℕ) : ℤ) + 1)
                     (double (tiers cote)) (G_Etat n) := by
          have h := Hb_Vg n t (x + ((double (tiers cote) : ℕ) : ℤ)) (tiers cote)
                    hbrick hVbrick
          have ht : (t + tiers cote) + 2 = (t + tiers cote + 1) + 1 := by omega
          rw [ht] at h; exact h
        have hH := ih (double (tiers cote)) hp_lt
                     (t + tiers cote + 1) x hsubDD hVsub
        have ht : (t + tiers cote + 1) + double (tiers cote) + 1 = t + cote + 1 := by omega
        rw [ht] at hH; exact hH
      · -- Right: Horizontale (t + cote + 1) (x + ↑double k + 1) k G.
        rcases Nat.lt_or_ge 2 (tiers cote) with hk_gt | hk_le
        · -- k ≥ 3: IH on side `k` via `Hb_DD`.
          have hp_lt : tiers cote < cote := lt_tiersn_n cote (by omega)
          have hDDsub :=
            Hb_DD n t (x + ((double (tiers cote) : ℕ) : ℤ)) (tiers cote)
                  hk_gt hbrick hVbrick
          have hVsub : Verticale ((t + double (tiers cote) + 1) + 1)
                       ((x + ((double (tiers cote) : ℕ) : ℤ) + 1) + (tiers cote : ℕ) + 1)
                       (tiers cote) (G_Etat n) := by
            have h := inclus_vert (t + 1) ((t + double (tiers cote) + 1) + 1)
                      (x + (cote : ℤ) + 1) cote (tiers cote) (G_Etat n)
                      (by omega) (by omega) hV
            have hpos : ((x + ((double (tiers cote) : ℕ) : ℤ) + 1) + (tiers cote : ℕ) + 1)
                      = x + (cote : ℤ) + 1 := by
              push_cast; linarith
            rw [hpos]; exact h
          have hH := ih (tiers cote) hp_lt (t + double (tiers cote) + 1)
                       ((x + ((double (tiers cote) : ℕ) : ℤ)) + 1) hDDsub hVsub
          have ht : (t + double (tiers cote) + 1) + tiers cote + 1 = t + cote + 1 := by omega
          rw [ht] at hH; exact hH
        · -- k = 2 (cote = 7): use `Hb3_Hg`.
          have hk1   : tiers cote = 2 := by omega
          have hcote : cote = 7 := by
            have := hpd; rw [hk1] at this; unfold double at this; omega
          have hd_four : ((double (tiers cote) : ℕ) : ℤ) = ((4 : ℕ) : ℤ) := by
            rw [hk1]; unfold double; norm_cast
          have hbrick' : B_basic n t (x + ((4 : ℕ) : ℤ)) 3 := by
            have h := hbrick
            rw [hd_four] at h
            have : tiers cote + 1 = 3 := by rw [hk1]
            rw [this] at h; exact h
          have hV' : Verticale (t + 1) (x + ((4 : ℕ) : ℤ) + 4) 7 (G_Etat n) := by
            have h := hV; rw [hcote] at h
            have heq : x + ((7 : ℕ) : ℤ) + 1 = x + ((4 : ℕ) : ℤ) + 4 := by push_cast; ring
            rw [heq] at h; exact h
          have hRes := Hb3_Hg n t (x + ((4 : ℕ) : ℤ)) hbrick' hV'
          have ht : t + 8 = t + cote + 1 := by omega
          rw [← ht, hd_four, hk1]
          exact hRes
    | DD_C t x cote hle hmod hbrick hsubDD =>
      -- `cote = double k + k + 2` (Deuxmod3). Decompose: cote = (double k + 1 + 1) + k.
      -- Left:  IH on side `double k + 1`, with V from `Hc_Vg`.
      -- Right: cote = 5 (k = 1) → `Hc2_Hg`;
      --        cote = 8 (k = 2) → `Hc3_Hg`;
      --        cote ≥ 11 (k ≥ 3) → IH on side `k` with DD from `Hc_DD`.
      show Horizontale (t + cote + 1) x cote (G_Etat n)
      have hk1     : 1 ≤ tiers cote := le_tiers_trois cote (by omega)
      have hpd     : (double (tiers cote) + tiers cote) + 2 = cote :=
        SSplus_deuxtiers_untiers cote hmod
      have htriple : triple (tiers cote) + 2 = cote := by
        have := SStriple_tiers cote hmod; unfold triple; omega
      have hpd_int : ((double (tiers cote) : ℤ)) + (tiers cote : ℤ) + 2 = (cote : ℤ) := by
        exact_mod_cast hpd
      have hd_cast : ((double (tiers cote) + 1 : ℕ) : ℤ)
                   = (double (tiers cote) : ℤ) + 1 := by push_cast; rfl
      -- Right wall feeding `Hc_Vg` and `Hc_DD`.
      have hVbrick : Verticale (t + 1)
          (((x + ((double (tiers cote) + 1 : ℕ) : ℤ)) + (tiers cote : ℕ)) + 2)
          (triple (tiers cote) + 2) (G_Etat n) := by
        have hpos : (((x + ((double (tiers cote) + 1 : ℕ) : ℤ)) + (tiers cote : ℕ)) + 2)
                  = x + (cote : ℤ) + 1 := by
          rw [hd_cast]; push_cast; linarith
        rw [hpos, htriple]; exact hV
      -- Decompose cote = (double k + 1 + 1) + k.
      have hsplit : (double (tiers cote) + 1 + 1) + tiers cote = cote := by omega
      suffices hgoal : Horizontale (t + cote + 1) x
          ((double (tiers cote) + 1 + 1) + tiers cote) (G_Etat n) by
        rw [hsplit] at hgoal; exact hgoal
      apply hh_hor (t + cote + 1) x (double (tiers cote) + 1) (tiers cote) (G_Etat n)
      · -- Left: Horizontale (t + cote + 1) x (double k + 1) G.
        have hp_lt : double (tiers cote) + 1 < cote := lt_Sdeuxtiersn_n cote (by omega)
        have hVsub : Verticale ((t + tiers cote + 1) + 1)
                     (x + ((double (tiers cote) + 1 : ℕ) : ℤ) + 1)
                     (double (tiers cote) + 1) (G_Etat n) := by
          have h := Hc_Vg n t (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) (tiers cote)
                    hbrick hVbrick
          have ht : (t + tiers cote) + 2 = (t + tiers cote + 1) + 1 := by omega
          rw [ht] at h; exact h
        have hH := ih (double (tiers cote) + 1) hp_lt
                     (t + tiers cote + 1) x hsubDD hVsub
        have ht : (t + tiers cote + 1) + (double (tiers cote) + 1) + 1 = t + cote + 1 := by
          omega
        rw [ht] at hH; exact hH
      · -- Right: Horizontale (t + cote + 1) (x + ↑(double k + 1) + 1) k G.
        rcases Nat.lt_or_ge 2 (tiers cote) with hk_gt | hk_le
        · -- k ≥ 3: IH on side `k` via `Hc_DD`.
          have hp_lt : tiers cote < cote := lt_tiersn_n cote (by omega)
          have hDDsub :=
            Hc_DD n t (x + ((double (tiers cote) + 1 : ℕ) : ℤ)) (tiers cote)
                  hk_gt hbrick hVbrick
          have hVsub : Verticale ((t + double (tiers cote) + 2) + 1)
                       ((x + ((double (tiers cote) + 1 : ℕ) : ℤ) + 1) + (tiers cote : ℕ) + 1)
                       (tiers cote) (G_Etat n) := by
            have h := inclus_vert (t + 1) ((t + double (tiers cote) + 2) + 1)
                      (x + (cote : ℤ) + 1) cote (tiers cote) (G_Etat n)
                      (by omega) (by omega) hV
            have hpos : ((x + ((double (tiers cote) + 1 : ℕ) : ℤ) + 1) + (tiers cote : ℕ) + 1)
                      = x + (cote : ℤ) + 1 := by
              rw [hd_cast]; push_cast; linarith
            rw [hpos]; exact h
          have hH := ih (tiers cote) hp_lt (t + double (tiers cote) + 2)
                       ((x + ((double (tiers cote) + 1 : ℕ) : ℤ)) + 1) hDDsub hVsub
          have ht : (t + double (tiers cote) + 2) + tiers cote + 1 = t + cote + 1 := by omega
          rw [ht] at hH; exact hH
        · -- k ≤ 2: split on k = 1 or k = 2.
          rcases Nat.lt_or_ge 1 (tiers cote) with hk_gt2 | hk_le1
          · -- k = 2 (cote = 8): use `Hc3_Hg`.
            have hk_eq : tiers cote = 2 := by omega
            have hcote : cote = 8 := by
              have := hpd; rw [hk_eq] at this; unfold double at this; omega
            have hd_five : ((double (tiers cote) + 1 : ℕ) : ℤ) = ((5 : ℕ) : ℤ) := by
              rw [hk_eq]; unfold double; norm_cast
            have hbrick' : C_basic n t (x + ((5 : ℕ) : ℤ)) 3 := by
              have h := hbrick
              rw [hd_five] at h
              have : tiers cote + 1 = 3 := by rw [hk_eq]
              rw [this] at h; exact h
            have hV' : Verticale (t + 1) (x + ((5 : ℕ) : ℤ) + 4) 8 (G_Etat n) := by
              have h := hV; rw [hcote] at h
              have heq : x + ((8 : ℕ) : ℤ) + 1 = x + ((5 : ℕ) : ℤ) + 4 := by push_cast; ring
              rw [heq] at h; exact h
            have hRes := Hc3_Hg n t (x + ((5 : ℕ) : ℤ)) hbrick' hV'
            have ht : t + 9 = t + cote + 1 := by omega
            rw [← ht, hd_five, hk_eq]
            exact hRes
          · -- k = 1 (cote = 5): use `Hc2_Hg`.
            have hk_eq : tiers cote = 1 := by omega
            have hcote : cote = 5 := by
              have := hpd; rw [hk_eq] at this; unfold double at this; omega
            have hd_three : ((double (tiers cote) + 1 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) := by
              rw [hk_eq]; unfold double; norm_cast
            have hbrick' : C_basic n t (x + ((3 : ℕ) : ℤ)) 2 := by
              have h := hbrick
              rw [hd_three] at h
              have : tiers cote + 1 = 2 := by rw [hk_eq]
              rw [this] at h; exact h
            have hV' : Verticale (t + 1) (x + ((3 : ℕ) : ℤ) + 3) 5 (G_Etat n) := by
              have h := hV; rw [hcote] at h
              have heq : x + ((5 : ℕ) : ℤ) + 1 = x + ((3 : ℕ) : ℤ) + 3 := by push_cast; ring
              rw [heq] at h; exact h
            have hRes := Hc2_Hg n t (x + ((3 : ℕ) : ℤ)) hbrick' hV'
            have ht : t + 6 = t + cote + 1 := by omega
            rw [← ht, hd_three, hk_eq]
            exact hRes
  exact key cote t x

/-! ### G-row + G to the right ⇒ F-row -/

lemma Hg_Hf (t : ℕ) (long : ℕ) :
    0 < long →
    Horizontale t 0 long (G_Etat n) →
    G_Etat n t (long + 1) →
    Horizontale (t + 1) 0 long (F_Etat n) := by
  intro hlong hH hGr
  refine ⟨fun dx hdx => ?_⟩
  show Etat n (t + 1) ((0 : ℤ) + (dx : ℤ)) = F
  have heq0 : ((0 : ℤ) + (dx : ℤ)) = (dx : ℤ) := by ring
  rw [heq0]
  rcases Nat.eq_zero_or_pos dx with hdx0 | hdxp
  · -- dx = 0: column 0. δ L G G = F.
    subst hdx0
    have hL : Etat n t (-1) = L := L_outside n t (-1) (by norm_num)
    have hG0 : Etat n t 0 = G := by
      have h := hH.pointwise 0 (Nat.zero_le _)
      simpa using h
    have hG1 : Etat n t 1 = G := by
      have h := hH.pointwise 1 (by omega)
      simpa using h
    show Etat n (t + 1) ((0 : ℕ) : ℤ) = F
    have hcast0 : (((0 : ℕ) : ℤ)) = 0 := by norm_num
    rw [hcast0, un_pas, show ((0 : ℤ) - 1) = (-1) from by ring,
        show ((0 : ℤ) + 1) = 1 from by ring, hL, hG0, hG1]
    rfl
  · -- 1 ≤ dx ≤ long: all three neighbours are G. δ G G G = F.
    have hG_left : Etat n t ((dx : ℤ) - 1) = G := by
      have h := hH.pointwise (dx - 1) (by omega)
      have heq : ((0 : ℤ) + ((dx - 1 : ℕ) : ℤ)) = (dx : ℤ) - 1 := by
        have hge : 1 ≤ dx := hdxp
        rw [Nat.cast_sub hge]; push_cast; ring
      rw [heq] at h; exact h
    have hG_mid : Etat n t (dx : ℤ) = G := by
      have h := hH.pointwise dx hdx
      simpa using h
    have hG_right : Etat n t ((dx : ℤ) + 1) = G := by
      rcases Nat.lt_or_ge dx long with hlt | hge
      · have h := hH.pointwise (dx + 1) (by omega)
        have heq : ((0 : ℤ) + ((dx + 1 : ℕ) : ℤ)) = (dx : ℤ) + 1 := by
          push_cast; ring
        rw [heq] at h; exact h
      · have heq : dx = long := by omega
        subst heq
        exact hGr
    rw [un_pas, hG_left, hG_mid, hG_right]
    rfl

end FsspMazoyer
end CellularAutomatas
