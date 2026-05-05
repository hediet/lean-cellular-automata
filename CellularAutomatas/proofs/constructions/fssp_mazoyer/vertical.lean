/-
  Mazoyer FSSP -- bridges from horizontal rows to `DD` and to
  vertical G-walls (port of `vertical.v`).
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.double_diag

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

variable (n : ℕ)

/-! ### δ-evaluation lemmas used in `Ht0_End2`.

    These are all `rfl` once the relevant pattern matches reduce. -/

private lemma δ_LGL : δ L G L = A := rfl
private lemma δ_GLL : δ G L L = C := rfl
private lemma δ_LAC : δ L A C = G := rfl
private lemma δ_ACany (c : Couleur) : δ A C c = B := rfl
private lemma δ_LLany (c : Couleur) : δ L L c = L := rfl

/-! ### Local helper: two adjacent `L`s yield an `L` one step later.

This is the L-stability property used by `rec_triangle_inf` in the
proof of `Hor_tr_inf`, and is also useful directly. -/

private lemma LL_L (t : ℕ) (x : ℤ) :
    L_Etat n t x → L_Etat n t (x + 1) → L_Etat n (t + 1) (x + 1) := by
  intro h0 h1
  show Etat n (t + 1) (x + 1) = L
  rw [un_pas]
  have e : (x + 1 - 1 : ℤ) = x := by ring
  rw [e]
  show δ (Etat n t x) (Etat n t (x + 1)) (Etat n t (x + 1 + 1)) = L
  rw [show Etat n t x = L from h0, show Etat n t (x + 1) = L from h1]
  exact δ_LLany _

/-! ### From a `G:C:L^*` row to staircase / triangle -/

lemma Ht1_End2 (t : ℕ) (x : ℤ) (long : ℕ) :
    Horizontale_t1 t x long (G_Etat n) (C_Etat n) (L_Etat n) →
    deux_end n t x := by
  intro H
  obtain ⟨g, c, _⟩ := H
  refine ⟨c, GC_dollarB n t x g c, ?_⟩
  refine ⟨GC_G n t x g c, ?_⟩
  exact GB_G n (t + 1) x (GC_G n t x g c) (GC_dollarB n t x g c)

/-- All-`L` row extends downward as a triangle of `L`s. -/
lemma Hor_tr_inf (t : ℕ) (x : ℤ) (cote : ℕ) :
    Horizontale t x cote (L_Etat n) →
    Triangle_inf t x cote (L_Etat n) := by
  intro h
  exact rec_triangle_inf t x cote (L_Etat n) h
    (fun t' x' h0 h1 => LL_L n t' x' h0 h1)

lemma Ht1_End4 (t : ℕ) (x : ℤ) (long : ℕ) :
    0 < long →
    Horizontale_t1 t x long (G_Etat n) (C_Etat n) (L_Etat n) →
    quatre_end n t x := by
  intro hlong H
  have h2end : deux_end n t x := Ht1_End2 n t x long H
  obtain ⟨_, _, hHor⟩ := H
  have hL_t_2 : L_Etat n t (x + 2) := by
    have h := hHor.pointwise 0 (by omega)
    simpa using h
  have hL_t_3 : L_Etat n t (x + 3) := by
    have h := hHor.pointwise 1 hlong
    have e : (x + 2 : ℤ) + ((1 : ℕ) : ℤ) = x + 3 := by push_cast; ring
    rw [e] at h; exact h
  have hL_t1_3 : L_Etat n (t + 1) (x + 3) := by
    -- `LL_L` wants its second argument shaped as `x + 2 + 1`.
    have hL_t_3' : L_Etat n t (x + 2 + 1) := by
      have e : (x + 2 + 1 : ℤ) = x + 3 := by ring
      rw [e]; exact hL_t_3
    have h := LL_L n t (x + 2) hL_t_2 hL_t_3'
    have e : (x + 2 + 1 : ℤ) = x + 3 := by ring
    rw [e] at h; exact h
  exact deux_quatre n t x h2end hL_t_2 hL_t_3 hL_t1_3

/-! ### From a `G:C:L^*` row to `DD` -/

lemma Ht1_bissect (t : ℕ) (x : ℤ) (cote : ℕ) :
    0 < cote →
    Horizontale_t1 t x cote (G_Etat n) (C_Etat n) (L_Etat n) →
    ∀ dx : ℕ, dx + 1 ≤ cote →
      L_Etat n (t + dx) ((x + 2) + (dx + 1)) ∧
      L_Etat n (t + dx + 1) ((x + 2) + (dx + 1)) := by
  intro _ H dx hdx
  have hT : Triangle_inf t (x + 2) cote (L_Etat n) :=
    Hor_tr_inf n t (x + 2) cote H.tail
  refine ⟨?_, ?_⟩
  · exact hT.pointwise dx (dx + 1) hdx (by omega)
  · exact hT.pointwise (dx + 1) (dx + 1) hdx (le_refl _)

theorem Ht1_DD (t : ℕ) (x : ℤ) (cote : ℕ) :
    0 < cote →
    Horizontale_t1 t x cote (G_Etat n) (C_Etat n) (L_Etat n) →
    ∀ dx : ℕ, dx + 1 ≤ cote → DD n (t + dx) x (dx + 3) := by
  intro hcote H dx
  induction dx with
  | zero =>
    intro _
    show DD n (t + 0) x 3
    exact DD.DD_4 _ _ (Ht1_End4 n t x cote hcote H)
  | succ k ih =>
    intro hdx
    have ihDD : DD n (t + k) x (k + 3) := ih (by omega)
    obtain ⟨hL1, hL2⟩ := Ht1_bissect n t x cote hcote H (k + 1) hdx
    -- `hL1 : L_Etat n (t + (k+1)) (x + 2 + (↑(k+1) + 1))` after push_cast normalization.
    -- We need: `L_Etat n (((t+k)+1)) (x + ↑((k+3)+1))`.
    have ecoord : x + 2 + (((k + 1 : ℕ) : ℤ) + 1) = x + (((k + 3 + 1 : ℕ) : ℤ)) := by
      push_cast; ring
    rw [ecoord] at hL1 hL2
    show DD n (t + (k + 1)) x ((k + 1) + 3)
    exact DD_hddollar n (t + k) x (k + 3) ihDD hL1 hL2

lemma Ht1_DDf (t : ℕ) (x : ℤ) (haut : ℕ) :
    Horizontale_t1 t x (haut + 1) (G_Etat n) (C_Etat n) (L_Etat n) →
    DD n (t + haut) x (haut + 3) := by
  intro H
  exact Ht1_DD n t x (haut + 1) (by omega) H haut (by omega)

lemma Ht1_VV (t : ℕ) (x : ℤ) (cote : ℕ) :
    Horizontale_t1 t x cote (G_Etat n) (C_Etat n) (L_Etat n) →
    Verticale (t + 1) x (double cote + 1) (G_Etat n) := by
  intro H
  apply rec_vert (t + 1) x cote (G_Etat n)
  intro dt hdt
  match dt, hdt with
  | 0, _ =>
    -- `dt = 0`: collapse `double 0` to `0` and use `deux_GG ∘ Ht1_End2`.
    show G_Etat n (t + 1 + double 0) x ∧ G_Etat n (t + 1 + double 0 + 1) x
    exact deux_GG n t x (Ht1_End2 n t x cote H)
  | k + 1, hk =>
    have hcote_pos : 0 < cote := by omega
    have hk' : k + 1 ≤ cote := by omega
    have hDD : DD n (t + k) x (k + 3) := Ht1_DD n t x cote hcote_pos H k hk'
    have hgg := DD_GG n (t + k) x (k + 3) hDD
    -- `hgg.1 : G_Etat n ((t+k) + (k+3)) x = G_Etat n (t + 2k + 3) x`
    -- `hgg.2 : G_Etat n ((t+k) + (k+3) + 1) x = G_Etat n (t + 2k + 4) x`
    -- Goal time arg: `(t+1) + double (k+1)` and that `+1`.
    have e1 : (t + 1) + double (k + 1) = (t + k) + (k + 3) := by unfold double; omega
    have e2 : (t + 1) + double (k + 1) + 1 = (t + k) + (k + 3) + 1 := by
      unfold double; omega
    refine ⟨?_, ?_⟩
    · rw [e1]; exact hgg.1
    · rw [e2]; exact hgg.2

/-! ### From the initial `G:L^*` row to `DD` -/

lemma Ht0_bissect (t : ℕ) (long : ℕ) :
    1 < long →
    Horizontale_t0 t 0 long (G_Etat n) (L_Etat n) →
    ∀ dx : ℕ, dx + 1 ≤ long →
      L_Etat n (t + dx) (dx + 2) ∧ L_Etat n (t + dx + 1) (dx + 2) := by
  intro _ H dx hdx
  -- `H.tail : Horizontale t (0 + 1) long (L_Etat n)`. Don't normalize the `0 + 1`.
  have hT : Triangle_inf t (0 + 1) long (L_Etat n) :=
    Hor_tr_inf n t (0 + 1) long H.tail
  -- Triangle gives `L_Etat (t + dt) ((0 + 1 : ℤ) + ↑dx')`.
  -- Target uses `(↑dx + 2 : ℤ)` (the second arg of `L_Etat n` is ℤ).
  have e : ((0 : ℤ) + 1) + ((dx + 1 : ℕ) : ℤ) = ((dx : ℤ) + 2) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h := hT.pointwise dx (dx + 1) hdx (by omega)
    rw [e] at h; exact h
  · have h := hT.pointwise (dx + 1) (dx + 1) hdx (le_refl _)
    rw [e] at h; exact h

lemma Ht0_End2 (t : ℕ) (long : ℕ) :
    1 < long →
    Horizontale_t0 t 0 long (G_Etat n) (L_Etat n) →
    deux_end n (t + 1) 0 := by
  intro hlong H
  obtain ⟨hG, hHor⟩ := H
  -- Three base facts about the initial row at columns 0, 1, 2.
  have hE0 : Etat n t 0 = G := hG
  have hE1 : Etat n t 1 = L := by
    -- `hHor.pointwise 0 _ : L_Etat n t ((0 + 1 : ℤ) + ↑0)`.
    have h := hHor.pointwise 0 (by omega)
    simpa using h
  have hE2 : Etat n t 2 = L := by
    -- `hHor.pointwise 1 _ : L_Etat n t ((0 + 1 : ℤ) + ↑1)`.
    have h := hHor.pointwise 1 hlong.le
    have e : ((0 : ℤ) + 1) + ((1 : ℕ) : ℤ) = 2 := by push_cast
    rw [e] at h; exact h
  -- A10: `Etat (t+1) 0 = A` via `demi_pas`.
  have hA10 : Etat n (t + 1) 0 = A := by
    rw [demi_pas, hE0, hE1]
    rfl
  -- C11: `Etat (t+1) 1 = C` via `un_pas`.
  have hC11 : Etat n (t + 1) 1 = C := by
    show Etat n (t + 1) 1 = C
    rw [un_pas]
    have e0 : (1 - 1 : ℤ) = 0 := by ring
    have e2 : (1 + 1 : ℤ) = 2 := by ring
    rw [e0, e2, hE0, hE1, hE2]
    rfl
  -- G20: `Etat (t+2) 0 = G` via `demi_pas` (note `t+2 = (t+1)+1`).
  have hG20 : Etat n (t + 2) 0 = G := by
    show Etat n (t + 1 + 1) 0 = G
    rw [demi_pas, hA10, hC11]
    rfl
  -- B21: `Etat (t+2) 1 = B` via `un_pas`.
  have hB21 : Etat n (t + 2) 1 = B := by
    show Etat n (t + 1 + 1) 1 = B
    rw [un_pas]
    have e0 : (1 - 1 : ℤ) = 0 := by ring
    have e2 : (1 + 1 : ℤ) = 2 := by ring
    rw [e0, e2, hA10, hC11]
    -- Goal: `δ A C (Etat n (t+1) 2) = B`. Use `δ_ACany`.
    exact δ_ACany _
  -- Build `deux_end n (t+1) 0`.
  refine ⟨?_, ?_, ?_, ?_⟩
  · show C_Etat n (t + 1) (0 + 1)
    have e : (0 + 1 : ℤ) = 1 := by ring
    rw [e]; exact hC11
  · show B_Etat n (t + 1 + 1) (0 + 1)
    have e : (0 + 1 : ℤ) = 1 := by ring
    rw [e]; exact hB21
  · show G_Etat n (t + 1 + 1) 0
    exact hG20
  · -- `g1 : G_Etat n (t + 1 + 1 + 1) 0`. Use `GB_G` at `(t+2, 0)`.
    have hB21' : B_Etat n (t + 2) (0 + 1) := by
      show Etat n (t + 2) (0 + 1) = B
      have e : (0 + 1 : ℤ) = 1 := by ring
      rw [e]; exact hB21
    show G_Etat n (t + 1 + 1 + 1) 0
    exact GB_G n (t + 2) 0 hG20 hB21'

lemma Ht0_End4 (t : ℕ) (long : ℕ) :
    1 < long →
    Horizontale_t0 t 0 long (G_Etat n) (L_Etat n) →
    quatre_end n (t + 1) 0 := by
  intro hlong H
  have h2end : deux_end n (t + 1) 0 := Ht0_End2 n t long hlong H
  -- `bissect 0` gives `L_Etat t 2 ∧ L_Etat (t+1) 2` (we want the right half).
  -- `bissect 1` gives `L_Etat (t+1) 3 ∧ L_Etat (t+2) 3`.
  obtain ⟨_, hL_t1_2⟩ := Ht0_bissect n t long hlong H 0 (by omega)
  obtain ⟨hL_t1_3, hL_t2_3⟩ := Ht0_bissect n t long hlong H 1 (by omega)
  apply deux_quatre n (t + 1) 0 h2end
  · show L_Etat n (t + 1) (0 + 2)
    have e : (0 + 2 : ℤ) = ((0 : ℤ) + 2) := by ring
    rw [e]
    -- `hL_t1_2 : L_Etat n (t + 0 + 1) ((0 : ℤ) + 2)` with `t + 0 + 1 = t + 1` defeq.
    exact hL_t1_2
  · show L_Etat n (t + 1) (0 + 3)
    -- `hL_t1_3 : L_Etat n (t + 1) ((1 : ℤ) + 2) = L_Etat n (t+1) 3`.
    have e : (0 + 3 : ℤ) = ((1 : ℤ) + 2) := by ring
    rw [e]; exact hL_t1_3
  · show L_Etat n (t + 1 + 1) (0 + 3)
    -- `hL_t2_3 : L_Etat n (t + 1 + 1) ((1 : ℤ) + 2)`.
    have e : (0 + 3 : ℤ) = ((1 : ℤ) + 2) := by ring
    rw [e]; exact hL_t2_3

theorem Ht0_DD (t : ℕ) (long : ℕ) :
    1 < long →
    Horizontale_t0 t 0 long (G_Etat n) (L_Etat n) →
    ∀ dx : ℕ, dx + 2 ≤ long → DD n ((t + 1) + dx) 0 (dx + 3) := by
  intro hlong H dx
  induction dx with
  | zero =>
    intro _
    show DD n ((t + 1) + 0) 0 (0 + 3)
    exact DD.DD_4 _ _ (Ht0_End4 n t long hlong H)
  | succ k ih =>
    intro hdx
    have ihDD : DD n ((t + 1) + k) 0 (k + 3) := ih (by omega)
    obtain ⟨hL1, hL2⟩ := Ht0_bissect n t long hlong H (k + 2) (by omega)
    -- `hL1 : L_Etat n (t + (k+2)) ((↑(k+2) : ℤ) + 2)`
    -- `hL2 : L_Etat n (t + (k+2) + 1) ((↑(k+2) : ℤ) + 2)`
    -- Reshape coord: `(↑(k+2) + 2 : ℤ) = 0 + ↑((k+3)+1)`.
    have ecoord : ((k + 2 : ℕ) : ℤ) + 2 = (0 : ℤ) + ((k + 3 + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [ecoord] at hL1 hL2
    -- Time alignment: `t + (k+2) = (t+1) + k + 1` and `t + (k+2) + 1 = (t+1) + k + 2`.
    have et1 : t + (k + 2) = (t + 1) + k + 1 := by omega
    have et2 : t + (k + 2) + 1 = (t + 1) + k + 2 := by omega
    rw [et1] at hL1
    rw [et2] at hL2
    show DD n ((t + 1) + (k + 1)) 0 ((k + 1) + 3)
    exact DD_hddollar n ((t + 1) + k) 0 (k + 3) ihDD hL1 hL2

lemma Ht0_DDf (t : ℕ) (long : ℕ) :
    1 < long →
    Horizontale_t0 t 0 long (G_Etat n) (L_Etat n) →
    DD n (t + (long - 1)) 0 (long + 1) := by
  intro hlong H
  -- Apply `Ht0_DD` at `dx = long - 2`.
  have hDD := Ht0_DD n t long hlong H (long - 2) (by omega)
  -- `hDD : DD n ((t + 1) + (long - 2)) 0 ((long - 2) + 3)`.
  have et : (t + 1) + (long - 2) = t + (long - 1) := by omega
  have el : (long - 2) + 3 = long + 1 := by omega
  rw [et, el] at hDD
  exact hDD

end FsspMazoyer
end CellularAutomatas
