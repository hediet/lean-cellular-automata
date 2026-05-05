/-
  Mazoyer FSSP -- left-edge "staircase" predicates `un_end`..`cinq_end`
  (port of `bord.v`).
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.basic_bricks

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

variable (n : ℕ)

/-! ### The five staircase levels -/

structure un_end (t : ℕ) (x : ℤ) : Prop where
  g0 : G_Etat n t x
  g1 : G_Etat n (t + 1) x

structure deux_end (t : ℕ) (x : ℤ) : Prop where
  c1  : C_Etat n t (x + 1)
  b1  : B_Etat n (t + 1) (x + 1)
  one : un_end n (t + 1) x

structure trois_end (t : ℕ) (x : ℤ) : Prop where
  a2  : A_Etat n t (x + 2)
  g2  : G_Etat n (t + 1) (x + 2)
  two : deux_end n (t + 1) x

structure quatre_end (t : ℕ) (x : ℤ) : Prop where
  l3a   : L_Etat n t (x + 3)
  l3b   : L_Etat n (t + 1) (x + 3)
  three : trois_end n (t + 1) x

structure cinq_end (t : ℕ) (x : ℤ) : Prop where
  l4a   : L_Etat n t (x + 4)
  l4b   : L_Etat n (t + 1) (x + 4)
  g3    : G_Etat n (t + 1) (x + 3)
  b3    : B_Etat n (t + 2) (x + 3)
  three : trois_end n (t + 2) x

/-! ### Closure: extract two consecutive `G`s at column 0 -/

lemma un_GG (t : ℕ) (x : ℤ) :
    un_end n t x → G_Etat n t x ∧ G_Etat n (t + 1) x := by
  intro h
  exact ⟨h.g0, h.g1⟩

lemma deux_GG (t : ℕ) (x : ℤ) :
    deux_end n t x → G_Etat n (t + 1) x ∧ G_Etat n (t + 2) x := by
  intro h
  exact ⟨h.one.g0, h.one.g1⟩

lemma trois_GG (t : ℕ) (x : ℤ) :
    trois_end n t x → G_Etat n (t + 2) x ∧ G_Etat n (t + 3) x := by
  intro h
  exact ⟨h.two.one.g0, h.two.one.g1⟩

lemma quatre_GG (t : ℕ) (x : ℤ) :
    quatre_end n t x → G_Etat n (t + 3) x ∧ G_Etat n (t + 4) x := by
  intro h
  exact ⟨h.three.two.one.g0, h.three.two.one.g1⟩

lemma cinq_GG (t : ℕ) (x : ℤ) :
    cinq_end n t x → G_Etat n (t + 4) x ∧ G_Etat n (t + 5) x := by
  intro h
  exact ⟨h.three.two.one.g0, h.three.two.one.g1⟩

/-! ### Promotion lemmas (`bord.v` `*_*`) -/

lemma un_deux (t : ℕ) (x : ℤ) :
    un_end n t x →
    C_Etat n (t + 1) (x + 1) →
    B_Etat n (t + 2) (x + 1) →
    deux_end n (t + 1) x := by
  intro h hC hB
  -- `deux_end (t+1) x` needs `c1`, `b1` (given) and `one : un_end (t+2) x`.
  have g2 : G_Etat n (t + 2) x := GC_G n (t + 1) x h.g1 hC
  have g3 : G_Etat n (t + 3) x := GB_G n (t + 2) x g2 hB
  exact ⟨hC, hB, ⟨g2, g3⟩⟩

lemma deux_trois (t : ℕ) (x : ℤ) :
    deux_end n t x →
    A_Etat n (t + 1) (x + 2) →
    G_Etat n (t + 2) (x + 2) →
    trois_end n (t + 1) x := by
  intro h hA hG
  -- Build the new `C` and `B` cells at column x+1 via the corner δ-laws,
  -- then promote `un_end (t+1) x` to `deux_end (t+2) x` via `un_deux`.
  have hC' : C_Etat n (t + 2) (x + 1) := GBA_dollarC n (t + 1) x h.one.g0 h.b1 hA
  have hB' : B_Etat n (t + 3) (x + 1) := GC_dollarB n (t + 2) x h.one.g1 hC'
  have hdeux : deux_end n (t + 2) x := un_deux n (t + 1) x h.one hC' hB'
  exact ⟨hA, hG, hdeux⟩

lemma deux_quatre (t : ℕ) (x : ℤ) :
    deux_end n t x →
    L_Etat n t (x + 2) →
    L_Etat n t (x + 3) →
    L_Etat n (t + 1) (x + 3) →
    quatre_end n t x := by
  intro h hL2 hL3a hL3b
  -- Extract field equalities to feed into δ-rewrites.
  have hc1 : Etat n t (x + 1) = C := h.c1
  have hb1 : Etat n (t + 1) (x + 1) = B := h.b1
  have hL2e  : Etat n t (x + 2) = L := hL2
  have hL3ae : Etat n t (x + 3) = L := hL3a
  have hL3be : Etat n (t + 1) (x + 3) = L := hL3b
  -- A_Etat (t+1) (x+2): δ C L L = A (cell rule at column x+2 of row t).
  have hA12 : A_Etat n (t + 1) (x + 2) := by
    show Etat n (t + 1) (x + 2) = A
    rw [un_pas, show ((x + 2 : ℤ) - 1) = x + 1 from by ring,
        show ((x + 2 : ℤ) + 1) = x + 3 from by ring,
        hc1, hL2e, hL3ae]
    rfl
  have hAe : Etat n (t + 1) (x + 2) = A := hA12
  -- G_Etat (t+2) (x+2): δ B A L = G (cell rule at column x+2 of row t+1).
  have hG22 : G_Etat n (t + 2) (x + 2) := by
    show Etat n (t + 2) (x + 2) = G
    change Etat n ((t + 1) + 1) (x + 2) = G
    rw [un_pas, show ((x + 2 : ℤ) - 1) = x + 1 from by ring,
        show ((x + 2 : ℤ) + 1) = x + 3 from by ring,
        hb1, hAe, hL3be]
    rfl
  exact ⟨hL3a, hL3b, deux_trois n t x h hA12 hG22⟩

lemma trois_quatre (t : ℕ) (x : ℤ) :
    trois_end n t x →
    L_Etat n (t + 1) (x + 3) →
    L_Etat n (t + 2) (x + 3) →
    trois_end n (t + 2) x := by
  intro h hL13 hL23
  have hc1 : Etat n (t + 1) (x + 1) = C := h.two.c1
  have hb1 : Etat n (t + 2) (x + 1) = B := h.two.b1
  have hg2 : Etat n (t + 1) (x + 2) = G := h.g2
  have hL13e : Etat n (t + 1) (x + 3) = L := hL13
  have hL23e : Etat n (t + 2) (x + 3) = L := hL23
  -- A_Etat (t+2) (x+2): δ C G L = A.
  have hA22 : A_Etat n (t + 2) (x + 2) := by
    show Etat n (t + 2) (x + 2) = A
    change Etat n ((t + 1) + 1) (x + 2) = A
    rw [un_pas, show ((x + 2 : ℤ) - 1) = x + 1 from by ring,
        show ((x + 2 : ℤ) + 1) = x + 3 from by ring,
        hc1, hg2, hL13e]
    rfl
  have hAe : Etat n (t + 2) (x + 2) = A := hA22
  -- G_Etat (t+3) (x+2): δ B A L = G.
  have hG32 : G_Etat n (t + 3) (x + 2) := by
    show Etat n (t + 3) (x + 2) = G
    change Etat n ((t + 2) + 1) (x + 2) = G
    rw [un_pas, show ((x + 2 : ℤ) - 1) = x + 1 from by ring,
        show ((x + 2 : ℤ) + 1) = x + 3 from by ring,
        hb1, hAe, hL23e]
    rfl
  exact deux_trois n (t + 1) x h.two hA22 hG32

lemma trois_cinq (t : ℕ) (x : ℤ) :
    trois_end n t x →
    G_Etat n (t + 1) (x + 3) →
    B_Etat n (t + 2) (x + 3) →
    trois_end n (t + 2) x := by
  intro h hG13 hB23
  have hc1 : Etat n (t + 1) (x + 1) = C := h.two.c1
  have hb1 : Etat n (t + 2) (x + 1) = B := h.two.b1
  have hg2 : Etat n (t + 1) (x + 2) = G := h.g2
  have hG13e : Etat n (t + 1) (x + 3) = G := hG13
  have hB23e : Etat n (t + 2) (x + 3) = B := hB23
  -- A_Etat (t+2) (x+2): δ C G G = A.
  have hA22 : A_Etat n (t + 2) (x + 2) := by
    show Etat n (t + 2) (x + 2) = A
    change Etat n ((t + 1) + 1) (x + 2) = A
    rw [un_pas, show ((x + 2 : ℤ) - 1) = x + 1 from by ring,
        show ((x + 2 : ℤ) + 1) = x + 3 from by ring,
        hc1, hg2, hG13e]
    rfl
  have hAe : Etat n (t + 2) (x + 2) = A := hA22
  -- G_Etat (t+3) (x+2): δ B A B = G.
  have hG32 : G_Etat n (t + 3) (x + 2) := by
    show Etat n (t + 3) (x + 2) = G
    change Etat n ((t + 2) + 1) (x + 2) = G
    rw [un_pas, show ((x + 2 : ℤ) - 1) = x + 1 from by ring,
        show ((x + 2 : ℤ) + 1) = x + 3 from by ring,
        hb1, hAe, hB23e]
    rfl
  exact deux_trois n (t + 1) x h.two hA22 hG32

/-! ### Idempotence under "two more `L`s in the trailing column" -/

lemma quatre_quatre (t : ℕ) (x : ℤ) :
    quatre_end n t x →
    L_Etat n (t + 2) (x + 3) →
    L_Etat n (t + 3) (x + 3) →
    quatre_end n (t + 2) x := by
  intro h hL23 hL33
  -- `quatre_end (t+2) x` is just the two given `L`s plus
  -- `trois_end (t+3) x = trois_quatre n (t+1) x h.three hL23 hL33`.
  exact ⟨hL23, hL33, trois_quatre n (t + 1) x h.three hL23 hL33⟩

lemma cinq_cinq (t : ℕ) (x : ℤ) :
    cinq_end n t x →
    L_Etat n (t + 2) (x + 4) →
    L_Etat n (t + 3) (x + 4) →
    cinq_end n (t + 2) x := by
  intro h hL24 hL34
  have ha2 : Etat n (t + 2) (x + 2) = A := h.three.a2
  have hg32 : Etat n (t + 3) (x + 2) = G := h.three.g2
  have hb3 : Etat n (t + 2) (x + 3) = B := h.b3
  have hL24e : Etat n (t + 2) (x + 4) = L := hL24
  have hL34e : Etat n (t + 3) (x + 4) = L := hL34
  -- G_Etat (t+3) (x+3): δ A B L = G.
  have hG33 : G_Etat n (t + 3) (x + 3) := by
    show Etat n (t + 3) (x + 3) = G
    change Etat n ((t + 2) + 1) (x + 3) = G
    rw [un_pas, show ((x + 3 : ℤ) - 1) = x + 2 from by ring,
        show ((x + 3 : ℤ) + 1) = x + 4 from by ring,
        ha2, hb3, hL24e]
    rfl
  have hG33e : Etat n (t + 3) (x + 3) = G := hG33
  -- B_Etat (t+4) (x+3): δ G G L = B.
  have hB43 : B_Etat n (t + 4) (x + 3) := by
    show Etat n (t + 4) (x + 3) = B
    change Etat n ((t + 3) + 1) (x + 3) = B
    rw [un_pas, show ((x + 3 : ℤ) - 1) = x + 2 from by ring,
        show ((x + 3 : ℤ) + 1) = x + 4 from by ring,
        hg32, hG33e, hL34e]
    rfl
  refine ⟨hL24, hL34, hG33, hB43, ?_⟩
  exact trois_cinq n (t + 2) x h.three hG33 hB43

/-! ### Level-up: quatre_end + 2 L's ⇒ cinq_end -/

lemma quatre_cinq (t : ℕ) (x : ℤ) :
    quatre_end n t x →
    L_Etat n (t + 1) (x + 4) →
    L_Etat n (t + 2) (x + 4) →
    cinq_end n (t + 1) x := by
  intro h hL14 hL24
  have hl3b : Etat n (t + 1) (x + 3) = L := h.l3b
  have ha2  : Etat n (t + 1) (x + 2) = A := h.three.a2
  have hg32 : Etat n (t + 2) (x + 2) = G := h.three.g2
  have hL14e : Etat n (t + 1) (x + 4) = L := hL14
  have hL24e : Etat n (t + 2) (x + 4) = L := hL24
  -- G_Etat (t+2) (x+3): δ A L L = G.
  have hG23 : G_Etat n (t + 2) (x + 3) := by
    show Etat n (t + 2) (x + 3) = G
    change Etat n ((t + 1) + 1) (x + 3) = G
    rw [un_pas, show ((x + 3 : ℤ) - 1) = x + 2 from by ring,
        show ((x + 3 : ℤ) + 1) = x + 4 from by ring,
        ha2, hl3b, hL14e]
    rfl
  have hG23e : Etat n (t + 2) (x + 3) = G := hG23
  -- B_Etat (t+3) (x+3): δ G G L = B.
  have hB33 : B_Etat n (t + 3) (x + 3) := by
    show Etat n (t + 3) (x + 3) = B
    change Etat n ((t + 2) + 1) (x + 3) = B
    rw [un_pas, show ((x + 3 : ℤ) - 1) = x + 2 from by ring,
        show ((x + 3 : ℤ) + 1) = x + 4 from by ring,
        hg32, hG23e, hL24e]
    rfl
  refine ⟨hL14, hL24, hG23, hB33, ?_⟩
  exact trois_cinq n (t + 1) x h.three hG23 hB33

/-! ### The recursion driver -/

lemma cinq_quatre (t : ℕ) (x : ℤ) :
    cinq_end n t x →
    L_Etat n (t + 1) (x + 5) →
    L_Etat n (t + 2) (x + 5) →
    C_basic n (t + 1) (x + 3) 2 ∧ quatre_end n (t + 3) x := by
  intro h hL15 hL25
  -- Pull every cell we need into raw equalities.
  have hg3   : Etat n (t + 1) (x + 3) = G := h.g3
  have hb3   : Etat n (t + 2) (x + 3) = B := h.b3
  have hl4b  : Etat n (t + 1) (x + 4) = L := h.l4b
  have ha2   : Etat n (t + 2) (x + 2) = A := h.three.a2
  have hg32  : Etat n (t + 3) (x + 2) = G := h.three.g2
  have hL15e : Etat n (t + 1) (x + 5) = L := hL15
  have hL25e : Etat n (t + 2) (x + 5) = L := hL25
  -- C_Etat (t+2) (x+4): δ G L L = C.
  have hC24 : C_Etat n (t + 2) (x + 4) := by
    show Etat n (t + 2) (x + 4) = C
    change Etat n ((t + 1) + 1) (x + 4) = C
    rw [un_pas, show ((x + 4 : ℤ) - 1) = x + 3 from by ring,
        show ((x + 4 : ℤ) + 1) = x + 5 from by ring,
        hg3, hl4b, hL15e]
    rfl
  have hC24e : Etat n (t + 2) (x + 4) = C := hC24
  -- L_Etat (t+3) (x+3): δ A B C = L.
  have hL33 : L_Etat n (t + 3) (x + 3) := by
    show Etat n (t + 3) (x + 3) = L
    change Etat n ((t + 2) + 1) (x + 3) = L
    rw [un_pas, show ((x + 3 : ℤ) - 1) = x + 2 from by ring,
        show ((x + 3 : ℤ) + 1) = x + 4 from by ring,
        ha2, hb3, hC24e]
    rfl
  have hL33e : Etat n (t + 3) (x + 3) = L := hL33
  -- C_Etat (t+3) (x+4): δ B C L = C.
  have hC34 : C_Etat n (t + 3) (x + 4) := by
    show Etat n (t + 3) (x + 4) = C
    change Etat n ((t + 2) + 1) (x + 4) = C
    rw [un_pas, show ((x + 4 : ℤ) - 1) = x + 3 from by ring,
        show ((x + 4 : ℤ) + 1) = x + 5 from by ring,
        hb3, hC24e, hL25e]
    rfl
  have hC34e : Etat n (t + 3) (x + 4) = C := hC34
  -- L_Etat (t+4) (x+3): δ G L C = L.
  have hL43 : L_Etat n (t + 4) (x + 3) := by
    show Etat n (t + 4) (x + 3) = L
    change Etat n ((t + 3) + 1) (x + 3) = L
    rw [un_pas, show ((x + 3 : ℤ) - 1) = x + 2 from by ring,
        show ((x + 3 : ℤ) + 1) = x + 4 from by ring,
        hg32, hL33e, hC34e]
    rfl
  -- Build the C-brick of side 2 at (t+1, x+3) using `deux_Diag` twice.
  have diag0 : Diag (t + 1) (x + 3) 2 (L_Etat n) (C_Etat n) (L_Etat n) := by
    apply deux_Diag
    · -- apex L_Etat (t+1) ((x+3)+2) = L_Etat (t+1) (x+5)
      show Etat n (t + 1) ((x + 3) + 2) = L
      rw [show ((x + 3 : ℤ) + 2) = x + 5 from by ring]
      exact hL15
    · -- interior C_Etat (t+2) ((x+3)+1) = C_Etat (t+2) (x+4)
      show Etat n ((t + 1) + 1) ((x + 3) + 1) = C
      rw [show ((x + 3 : ℤ) + 1) = x + 4 from by ring]
      exact hC24
    · -- bottomLeft L_Etat ((t+1)+2) (x+3) = L_Etat (t+3) (x+3)
      exact hL33
  have diag1 : Diag (t + 2) (x + 3) 2 (L_Etat n) (C_Etat n) (L_Etat n) := by
    apply deux_Diag
    · -- apex L_Etat (t+2) (x+5)
      show Etat n (t + 2) ((x + 3) + 2) = L
      rw [show ((x + 3 : ℤ) + 2) = x + 5 from by ring]
      exact hL25
    · -- interior C_Etat (t+3) (x+4)
      show Etat n ((t + 2) + 1) ((x + 3) + 1) = C
      rw [show ((x + 3 : ℤ) + 1) = x + 4 from by ring]
      exact hC34
    · -- bottomLeft L_Etat (t+4) (x+3)
      exact hL43
  have hCbasic : C_basic n (t + 1) (x + 3) 2 := ⟨by decide, diag0, diag1⟩
  -- Build quatre_end (t+3) x: l3a, l3b are the L's just proved;
  -- the recursive trois_end (t+4) x is `trois_quatre` applied to h.three.
  have hquatre : quatre_end n (t + 3) x :=
    ⟨hL33, hL43, trois_quatre n (t + 2) x h.three hL33 hL43⟩
  exact ⟨hCbasic, hquatre⟩

end FsspMazoyer
end CellularAutomatas
