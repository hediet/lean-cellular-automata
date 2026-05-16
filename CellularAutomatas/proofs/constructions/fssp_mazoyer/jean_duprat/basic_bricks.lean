/-
  Mazoyer FSSP -- the basic bricks `A_basic`, `B_basic`, `C_basic`.

  Lean 4 port of `basic.v` from Jean Duprat's Coq proof of the
  Firing Squad Synchronization Problem (Mazoyer's solution).
  Original source: https://github.com/rocq-archive/firing-squad
  Commit: 821676dce0353798b0651d058ffb22b65fb09097
  License: LGPL 2.1
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.jean_duprat.etat
import CellularAutomatas.proofs.constructions.fssp_mazoyer.jean_duprat.constr

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

variable (n : ℕ)

/-! ### δ-table facts used in the apex / sommet lemmas.

These are the only `δ` evaluations needed below. They all hold
definitionally — `Transition_G` matches on the right neighbour first
(resp. `Transition_A`/`Transition_C` on the left), so the relevant
free arguments do not appear in the result. -/

private lemma δ_anyGA (c : Couleur) : δ c G A = G := rfl
private lemma δ_anyGB (c : Couleur) : δ c G B = G := rfl
private lemma δ_anyGC (c : Couleur) : δ c G C = G := rfl
private lemma δ_GAany (c : Couleur) : δ G A c = C := rfl
private lemma δ_GCany (c : Couleur) : δ G C c = B := rfl
private lemma δ_GBA : δ G B A = C := rfl
private lemma δ_GBG : δ G B G = G := rfl
private lemma δ_GBC : δ G B C = B := rfl

/-! ### `loi` / `loi_droite` lifters.

Every interior premise the combinators of `constr.lean` need has the
shape `loi P Q R T` where `P,Q,R,T` are `*_Etat n` predicates whose
underlying `Couleur`s satisfy a single δ-table fact `δ a b c = d`.
The following helper packages that observation. The boundary helper
`loi_droite_etat` covers the column-0 case where the left neighbour
is unconstrained (we case-split on it). -/

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

private lemma loi_droite_etat (q : Couleur) (h : ∀ c : Couleur, δ c L q = L) :
    loi_droite (fun (t : ℕ) (x : ℤ) => Etat n t x = L)
               (fun (t : ℕ) (x : ℤ) => Etat n t x = q)
               (fun (t : ℕ) (x : ℤ) => Etat n t x = L) := by
  intro t x hQ hR
  show Etat n (t + 1) x = L
  rw [un_pas, hQ, hR]
  exact h (Etat n t (x - 1))

private lemma δ_LA_L : ∀ c : Couleur, δ c L A = L := by intro c; cases c <;> rfl
private lemma δ_LB_L : ∀ c : Couleur, δ c L B = L := by intro c; cases c <;> rfl
private lemma δ_LC_L : ∀ c : Couleur, δ c L C = L := by intro c; cases c <;> rfl

/-! ### Brick predicates

A "basic brick" of type `?` of side `cote` is a pair of consecutive
diagonals (rows `t` and `t + 1`) whose interior carries the constant
state `?` and whose edges carry `L`. -/

structure A_basic (t : ℕ) (x : ℤ) (cote : ℕ) : Prop where
  size  : 2 < cote
  diag0 : Diag t       x cote (L_Etat n) (A_Etat n) (L_Etat n)
  diag1 : Diag (t + 1) x cote (L_Etat n) (A_Etat n) (L_Etat n)

structure B_basic (t : ℕ) (x : ℤ) (cote : ℕ) : Prop where
  size  : 2 < cote
  /-- Top row carries `G`, rest of interior carries `B`. -/
  diag0 : Diag' t      x cote (L_Etat n) (G_Etat n) (B_Etat n) (L_Etat n)
  diag1 : Diag (t + 1) x cote (L_Etat n) (B_Etat n) (L_Etat n)

structure C_basic (t : ℕ) (x : ℤ) (cote : ℕ) : Prop where
  size  : 1 < cote
  diag0 : Diag t       x cote (L_Etat n) (C_Etat n) (L_Etat n)
  diag1 : Diag (t + 1) x cote (L_Etat n) (C_Etat n) (L_Etat n)

/-! ### Vertical reuse: brick of same type two rows later -/

lemma A_A (t : ℕ) (x : ℤ) (cote : ℕ) :
    A_basic n t x cote →
    L_Etat n (t + 2) (x + cote) →
    L_Etat n (t + 3) (x + cote) →
    A_basic n (t + 2) x cote := by
  intro h h2 h3
  -- Five `loi`/`loi_droite` premises shared by both DDD applications.
  have hPQPQ : loi (L_Etat n) (A_Etat n) (L_Etat n) (A_Etat n) :=
    loi_etat n L A L A rfl
  have hQQPQ : loi (A_Etat n) (A_Etat n) (L_Etat n) (A_Etat n) :=
    loi_etat n A A L A rfl
  have hQQQQ : loi (A_Etat n) (A_Etat n) (A_Etat n) (A_Etat n) :=
    loi_etat n A A A A rfl
  have hPQQQ : loi (L_Etat n) (A_Etat n) (A_Etat n) (A_Etat n) :=
    loi_etat n L A A A rfl
  have hXPQP : loi_droite (L_Etat n) (A_Etat n) (L_Etat n) :=
    loi_droite_etat n A δ_LA_L
  -- new diag0 at row t+2 from original (diag0, diag1) via DDD
  have d0 :
      Diag (t + 2) x cote (L_Etat n) (A_Etat n) (L_Etat n) :=
    DDD t x cote (L_Etat n) (A_Etat n) (L_Etat n) (A_Etat n)
        (L_Etat n) (A_Etat n) hPQPQ hQQPQ hQQQQ hPQQQ hXPQP h.diag0 h.diag1 h2
  -- new diag1 at row t+3 from (original diag1, new d0) via DDD shifted by 1
  have d1 :
      Diag (t + 3) x cote (L_Etat n) (A_Etat n) (L_Etat n) :=
    DDD (t + 1) x cote (L_Etat n) (A_Etat n) (L_Etat n) (A_Etat n)
        (L_Etat n) (A_Etat n) hPQPQ hQQPQ hQQQQ hPQQQ hXPQP h.diag1 d0 h3
  exact ⟨h.size, d0, d1⟩

lemma B_B (t : ℕ) (x : ℤ) (cote : ℕ) :
    B_basic n t x cote →
    L_Etat n (t + 2) (x + cote) →
    L_Etat n (t + 3) (x + cote) →
    B_basic n (t + 2) x cote := by
  intro h h2 h3
  -- D'DD' takes 6 premises (hQQPR, hPQRQ, hQQRQ, hQQQQ, hPQQQ, hXPQP).
  -- DD'D takes 4 (hQRPQ, hQQQQ, hPQQQ, hXPQP).
  have hQQPR : loi (B_Etat n) (B_Etat n) (L_Etat n) (G_Etat n) :=
    loi_etat n B B L G rfl
  have hPQRQ : loi (L_Etat n) (B_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n L B G B rfl
  have hQQRQ : loi (B_Etat n) (B_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n B B G B rfl
  have hQQQQ : loi (B_Etat n) (B_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n B B B B rfl
  have hPQQQ : loi (L_Etat n) (B_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n L B B B rfl
  have hXPQP : loi_droite (L_Etat n) (B_Etat n) (L_Etat n) :=
    loi_droite_etat n B δ_LB_L
  have hQRPQ : loi (B_Etat n) (G_Etat n) (L_Etat n) (B_Etat n) :=
    loi_etat n B G L B rfl
  -- new diag0 at row t+2 (a `Diag'`) from original (diag0', diag1) via D'DD'
  have d0 :
      Diag' (t + 2) x cote (L_Etat n) (G_Etat n) (B_Etat n) (L_Etat n) :=
    D'DD' t x cote (L_Etat n) (B_Etat n) (G_Etat n) (L_Etat n) (B_Etat n)
          (L_Etat n) (G_Etat n) (B_Etat n)
          hQQPR hPQRQ hQQRQ hQQQQ hPQQQ hXPQP h.diag0 h.diag1 h2
  -- new diag1 at row t+3 from (original diag1, new d0) via DD'D shifted by 1
  have d1 :
      Diag (t + 3) x cote (L_Etat n) (B_Etat n) (L_Etat n) :=
    DD'D (t + 1) x cote (L_Etat n) (B_Etat n) (L_Etat n) (G_Etat n)
         (B_Etat n) (L_Etat n) (B_Etat n)
         hQRPQ hQQQQ hPQQQ hXPQP h.diag1 d0 h3
  exact ⟨h.size, d0, d1⟩

lemma C_C (t : ℕ) (x : ℤ) (cote : ℕ) :
    C_basic n t x cote →
    L_Etat n (t + 2) (x + cote) →
    L_Etat n (t + 3) (x + cote) →
    C_basic n (t + 2) x cote := by
  intro h h2 h3
  have hPQPQ : loi (L_Etat n) (C_Etat n) (L_Etat n) (C_Etat n) :=
    loi_etat n L C L C rfl
  have hQQPQ : loi (C_Etat n) (C_Etat n) (L_Etat n) (C_Etat n) :=
    loi_etat n C C L C rfl
  have hQQQQ : loi (C_Etat n) (C_Etat n) (C_Etat n) (C_Etat n) :=
    loi_etat n C C C C rfl
  have hPQQQ : loi (L_Etat n) (C_Etat n) (C_Etat n) (C_Etat n) :=
    loi_etat n L C C C rfl
  have hXPQP : loi_droite (L_Etat n) (C_Etat n) (L_Etat n) :=
    loi_droite_etat n C δ_LC_L
  have d0 :
      Diag (t + 2) x cote (L_Etat n) (C_Etat n) (L_Etat n) :=
    DDD t x cote (L_Etat n) (C_Etat n) (L_Etat n) (C_Etat n)
        (L_Etat n) (C_Etat n) hPQPQ hQQPQ hQQQQ hPQQQ hXPQP h.diag0 h.diag1 h2
  have d1 :
      Diag (t + 3) x cote (L_Etat n) (C_Etat n) (L_Etat n) :=
    DDD (t + 1) x cote (L_Etat n) (C_Etat n) (L_Etat n) (C_Etat n)
        (L_Etat n) (C_Etat n) hPQPQ hQQPQ hQQQQ hPQQQ hXPQP h.diag1 d0 h3
  exact ⟨h.size, d0, d1⟩

/-! ### Type rotation -/

/-- A → B (same side, shifted right). -/
lemma A_B (t : ℕ) (x : ℤ) (cote : ℕ) :
    A_basic n t x cote →
    L_Etat n (t + 1) ((x + 1) + cote) →
    L_Etat n (t + 2) ((x + 1) + cote) →
    B_basic n (t + 1) (x + 1) cote := by
  intro h h1 h2
  -- DD_D' takes 4 premises (hQPPR, hQQRQ, hQQQQ, hPQQP) followed by `2 < cote`.
  have hQPPR : loi (A_Etat n) (L_Etat n) (L_Etat n) (G_Etat n) :=
    loi_etat n A L L G rfl
  have hQQRQ : loi (A_Etat n) (A_Etat n) (G_Etat n) (B_Etat n) :=
    loi_etat n A A G B rfl
  have hQQQQ : loi (A_Etat n) (A_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n A A B B rfl
  have hPQQP : loi (L_Etat n) (A_Etat n) (B_Etat n) (L_Etat n) :=
    loi_etat n L A B L rfl
  -- D_D'D takes 3 premises (hQRPQ', hQQQQ', hPPQP).
  have hQRPQ' : loi (A_Etat n) (G_Etat n) (L_Etat n) (B_Etat n) :=
    loi_etat n A G L B rfl
  have hQQQQ' : loi (A_Etat n) (B_Etat n) (B_Etat n) (B_Etat n) :=
    loi_etat n A B B B rfl
  have hPPQP : loi (L_Etat n) (L_Etat n) (B_Etat n) (L_Etat n) :=
    loi_etat n L L B L rfl
  -- new diag0 (a `Diag'`) at row t+1, anchored at x+1, via DD_D'
  have d0 :
      Diag' (t + 1) (x + 1) cote (L_Etat n) (G_Etat n) (B_Etat n) (L_Etat n) :=
    DD_D' t x cote (L_Etat n) (A_Etat n) (L_Etat n) (A_Etat n)
          (L_Etat n) (G_Etat n) (B_Etat n)
          hQPPR hQQRQ hQQQQ hPQQP h.size h.diag0 h.diag1 h1
  -- new diag1 at row t+2, anchored at x+1, via D_D'D shifted by 1
  have d1 :
      Diag (t + 2) (x + 1) cote (L_Etat n) (B_Etat n) (L_Etat n) :=
    D_D'D (t + 1) x cote (L_Etat n) (A_Etat n) (L_Etat n) (G_Etat n)
          (B_Etat n) (L_Etat n) (B_Etat n)
          hQRPQ' hQQQQ' hPPQP h.diag1 d0 h2
  exact ⟨h.size, d0, d1⟩

/-- C → A (side grows by 1, anchor unchanged). -/
lemma C_A (t : ℕ) (x : ℤ) (cote : ℕ) :
    C_basic n t x cote →
    L_Etat n (t + 1) (x + (cote + 1)) →
    L_Etat n (t + 2) (x + (cote + 1)) →
    A_basic n (t + 1) x (cote + 1) := by
  intro h h1 h2
  -- DD_Ddollar takes 4 premises (hQPPQ, hQQQQ, hPQQQ, hXPQP).
  have hQPPQ : loi (C_Etat n) (L_Etat n) (L_Etat n) (A_Etat n) :=
    loi_etat n C L L A rfl
  have hQQQQ : loi (C_Etat n) (C_Etat n) (A_Etat n) (A_Etat n) :=
    loi_etat n C C A A rfl
  have hPQQQ : loi (L_Etat n) (C_Etat n) (A_Etat n) (A_Etat n) :=
    loi_etat n L C A A rfl
  have hXPQP : loi_droite (L_Etat n) (A_Etat n) (L_Etat n) :=
    loi_droite_etat n A δ_LA_L
  -- D_DDdollar takes 4 premises (hQQPQ', hQQQQ', hPQQQ', hXPQP shared).
  have hQQPQ' : loi (C_Etat n) (A_Etat n) (L_Etat n) (A_Etat n) :=
    loi_etat n C A L A rfl
  have hQQQQ' : loi (C_Etat n) (A_Etat n) (A_Etat n) (A_Etat n) :=
    loi_etat n C A A A rfl
  have hPQQQ' : loi (L_Etat n) (A_Etat n) (A_Etat n) (A_Etat n) :=
    loi_etat n L A A A rfl
  -- new diag0 at row t+1, side cote+1, via DD_Ddollar
  have d0 :
      Diag (t + 1) x (cote + 1) (L_Etat n) (A_Etat n) (L_Etat n) :=
    DD_Ddollar t x cote (L_Etat n) (C_Etat n) (L_Etat n) (C_Etat n)
               (L_Etat n) (A_Etat n)
               hQPPQ hQQQQ hPQQQ hXPQP h.diag0 h.diag1 h1
  -- new diag1 at row t+2, side cote+1, via D_DDdollar shifted by 1
  have d1 :
      Diag (t + 2) x (cote + 1) (L_Etat n) (A_Etat n) (L_Etat n) :=
    D_DDdollar (t + 1) x cote (L_Etat n) (C_Etat n) (L_Etat n) (A_Etat n)
               (L_Etat n) (A_Etat n)
               hQQPQ' hQQQQ' hPQQQ' hXPQP h.diag1 d0 h2
  -- size for A_basic: need 2 < cote + 1, follows from 1 < cote
  have hs : 2 < cote + 1 := by have := h.size; omega
  exact ⟨hs, d0, d1⟩

/-- B → C (same side, shifted right). -/
lemma B_C (t : ℕ) (x : ℤ) (cote : ℕ) :
    B_basic n t x cote →
    L_Etat n (t + 1) ((x + 1) + cote) →
    L_Etat n (t + 2) ((x + 1) + cote) →
    C_basic n (t + 1) (x + 1) cote := by
  intro h h1 h2
  -- D'D_D takes 3 premises (hRPPQ, hQQQQ, hPQQP).
  have hRPPQ : loi (G_Etat n) (L_Etat n) (L_Etat n) (C_Etat n) :=
    loi_etat n G L L C rfl
  have hQQQQ : loi (B_Etat n) (B_Etat n) (C_Etat n) (C_Etat n) :=
    loi_etat n B B C C rfl
  have hPQQP : loi (L_Etat n) (B_Etat n) (C_Etat n) (L_Etat n) :=
    loi_etat n L B C L rfl
  -- D_DD takes 3 premises (hQQPQ', hQQQQ', hPPQP).
  have hQQPQ' : loi (B_Etat n) (C_Etat n) (L_Etat n) (C_Etat n) :=
    loi_etat n B C L C rfl
  have hQQQQ' : loi (B_Etat n) (C_Etat n) (C_Etat n) (C_Etat n) :=
    loi_etat n B C C C rfl
  have hPPQP : loi (L_Etat n) (L_Etat n) (C_Etat n) (L_Etat n) :=
    loi_etat n L L C L rfl
  -- new diag0 at row t+1, anchored at x+1, via D'D_D
  have d0 :
      Diag (t + 1) (x + 1) cote (L_Etat n) (C_Etat n) (L_Etat n) :=
    D'D_D t x cote (L_Etat n) (B_Etat n) (G_Etat n) (L_Etat n) (B_Etat n)
          (L_Etat n) (C_Etat n)
          hRPPQ hQQQQ hPQQP h.diag0 h.diag1 h1
  -- new diag1 at row t+2 via D_DD shifted by 1
  have d1 :
      Diag (t + 2) (x + 1) cote (L_Etat n) (C_Etat n) (L_Etat n) :=
    D_DD (t + 1) x cote (L_Etat n) (B_Etat n) (L_Etat n) (C_Etat n)
         (L_Etat n) (C_Etat n)
         hQQPQ' hQQQQ' hPPQP h.diag1 d0 h2
  -- size for C_basic: need 1 < cote, follows from 2 < cote
  have hs : 1 < cote := by have := h.size; omega
  exact ⟨hs, d0, d1⟩

/-! ### Apex / vertex helpers (a.k.a. "sommet" lemmas of `basic.v`).

These describe how a `G` cell evolves when its right neighbour is
of various types. Each is one application of `δ`.

In the Lean port `un_pas` is `rfl` for *every* position (including
column 0): the recursion `Etat (t+1) p = δ (Etat t (p-1)) (Etat t p)
(Etat t (p+1))` holds unconditionally on `ℤ`. We therefore do not
need the Coq `case x` split between `un_pas` and `demi_pas`. -/

lemma GA_G (t : ℕ) (x : ℤ) :
    G_Etat n t x → A_Etat n t (x + 1) → G_Etat n (t + 1) x := by
  intro hG hA
  show Etat n (t + 1) x = G
  rw [un_pas, hG, hA]
  exact δ_anyGA _

lemma GB_G (t : ℕ) (x : ℤ) :
    G_Etat n t x → B_Etat n t (x + 1) → G_Etat n (t + 1) x := by
  intro hG hB
  show Etat n (t + 1) x = G
  rw [un_pas, hG, hB]
  exact δ_anyGB _

lemma GC_G (t : ℕ) (x : ℤ) :
    G_Etat n t x → C_Etat n t (x + 1) → G_Etat n (t + 1) x := by
  intro hG hC
  show Etat n (t + 1) x = G
  rw [un_pas, hG, hC]
  exact δ_anyGC _

lemma GA_dollarC (t : ℕ) (x : ℤ) :
    G_Etat n t x → A_Etat n t (x + 1) → C_Etat n (t + 1) (x + 1) := by
  intro hG hA
  show Etat n (t + 1) (x + 1) = C
  rw [un_pas]
  -- left neighbour at (t, (x+1) - 1) = (t, x), i.e. G; middle = A; right = anything
  have hxm1 : (x + 1 - 1 : ℤ) = x := by ring
  rw [hxm1, hG, hA]
  exact δ_GAany _

lemma GBA_dollarC (t : ℕ) (x : ℤ) :
    G_Etat n t x → B_Etat n t (x + 1) → A_Etat n t (x + 2) →
    C_Etat n (t + 1) (x + 1) := by
  intro hG hB hA
  show Etat n (t + 1) (x + 1) = C
  rw [un_pas]
  have hxm1 : (x + 1 - 1 : ℤ) = x := by ring
  have hxp2 : (x + 1 + 1 : ℤ) = x + 2 := by ring
  rw [hxm1, hxp2, hG, hB, hA]
  exact δ_GBA

lemma GBG_dollarG (t : ℕ) (x : ℤ) :
    G_Etat n t x → B_Etat n t (x + 1) → G_Etat n t (x + 2) →
    G_Etat n (t + 1) (x + 1) := by
  intro hG hB hG2
  show Etat n (t + 1) (x + 1) = G
  rw [un_pas]
  have hxm1 : (x + 1 - 1 : ℤ) = x := by ring
  have hxp2 : (x + 1 + 1 : ℤ) = x + 2 := by ring
  rw [hxm1, hxp2, hG, hB, hG2]
  exact δ_GBG

lemma GBC_dollarB (t : ℕ) (x : ℤ) :
    G_Etat n t x → B_Etat n t (x + 1) → C_Etat n t (x + 2) →
    B_Etat n (t + 1) (x + 1) := by
  intro hG hB hC
  show Etat n (t + 1) (x + 1) = B
  rw [un_pas]
  have hxm1 : (x + 1 - 1 : ℤ) = x := by ring
  have hxp2 : (x + 1 + 1 : ℤ) = x + 2 := by ring
  rw [hxm1, hxp2, hG, hB, hC]
  exact δ_GBC

lemma GC_dollarB (t : ℕ) (x : ℤ) :
    G_Etat n t x → C_Etat n t (x + 1) → B_Etat n (t + 1) (x + 1) := by
  intro hG hC
  show Etat n (t + 1) (x + 1) = B
  rw [un_pas]
  have hxm1 : (x + 1 - 1 : ℤ) = x := by ring
  rw [hxm1, hG, hC]
  exact δ_GCany _

end FsspMazoyer
end CellularAutomatas
