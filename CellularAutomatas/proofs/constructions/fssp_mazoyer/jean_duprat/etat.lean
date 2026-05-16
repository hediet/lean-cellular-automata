/-
  Mazoyer FSSP -- the per-state predicates and base configuration facts.

  Lean 4 port of `autom.v` (base section) from Jean Duprat's Coq proof
  of the Firing Squad Synchronization Problem (Mazoyer's solution).
  Original source: https://github.com/rocq-archive/firing-squad
  Commit: 821676dce0353798b0651d058ffb22b65fb09097
  License: LGPL 2.1

  The CA construction `Couleur`, `δ`, `Etat`, `init` is reused from
  the parent file `fssp_mazoyer.lean`.
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.jean_duprat.geom

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

/-! ### Per-state predicates (`A_Etat`, `B_Etat`, …)

The squad size convention: an `n = N + 1` cells configuration
means `N` is the *Coq* parameter (so `n ≥ 4` ↔ `2 < N`).
In the lemmas below `n` is fixed and corresponds to Coq's `N + 1`.
-/

variable (n : ℕ)

def A_Etat : Local_Prop := fun t x => Etat n t x = A
def B_Etat : Local_Prop := fun t x => Etat n t x = B
def C_Etat : Local_Prop := fun t x => Etat n t x = C
def G_Etat : Local_Prop := fun t x => Etat n t x = G
def L_Etat : Local_Prop := fun t x => Etat n t x = L
def F_Etat : Local_Prop := fun t x => Etat n t x = F

/-! ### Step laws (`autom.v` `un_pas`, `demi_pas`)

The `Etat` definition already gives a per-cell step: every cell at
position `p` evolves via `δ (Etat n t (p-1)) (Etat n t p) (Etat n t (p+1))`.
Coq's leftmost `demi_pas` rule `Etat (S t) 0 = δ L (Etat t 0) (Etat t 1)`
holds because `Etat n t (-1) = L` by the initial-config phantom (proved
via the `L_outside` lemma below). -/

lemma un_pas (t : ℕ) (p : ℤ) :
    Etat n (t + 1) p = δ (Etat n t (p - 1)) (Etat n t p) (Etat n t (p + 1)) :=
  rfl

/-- Cells with negative index are `L` at all times. (Coq's left phantom
    is `L`-only; the propagation works because `δ L L _ = L`, which is
    the `Transition_L` `c0 = L` branch — independent of the right
    neighbour.)  Note: the analogous right-side claim
    `Etat n t p = L` for `n+1 < p` is **false** in general — the `C`
    cell at position `n+1` immediately re-colours position `n+2` to
    `A`. We therefore only state the negative-index case (which is
    all that `demi_pas` needs). -/
lemma L_outside (t : ℕ) : ∀ (p : ℤ), p < 0 → Etat n t p = L := by
  induction t with
  | zero =>
    intro p hp
    show init n p = L
    have hn_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have h0  : p ≠ 0           := by omega
    have hn  : p ≠ (n : ℤ)     := by omega
    have hn1 : p ≠ (n : ℤ) + 1 := by omega
    simp [init, h0, hn, hn1]
  | succ t ih =>
    intro p hp
    show δ (Etat n t (p - 1)) (Etat n t p) (Etat n t (p + 1)) = L
    rw [ih (p - 1) (by omega), ih p hp]
    -- goal: `δ L L (Etat n t (p+1)) = L`. `Transition_L` matches on
    -- the left neighbour first and its `L` branch returns `L`
    -- regardless of the right neighbour, so this is `rfl`.
    rfl

/-- The leftmost cell evolves as if its left neighbour were `L`,
    matching Coq's `demi_pas`. -/
lemma demi_pas (t : ℕ) :
    Etat n (t + 1) 0 = δ L (Etat n t 0) (Etat n t 1) := by
  -- `Etat n (t+1) 0` reduces definitionally to
  -- `δ (Etat n t (-1)) (Etat n t 0) (Etat n t 1)`; replace the
  -- phantom left neighbour using `L_outside`.
  show δ (Etat n t (-1)) (Etat n t 0) (Etat n t 1)
        = δ L (Etat n t 0) (Etat n t 1)
  rw [L_outside n t (-1) (by norm_num)]

/-! ### Initial-row base lemmas (`autom.v` `G00`, `G0N`, `C0N1`,
    `base_L`, `basedollar_L`). -/

lemma G00 (_h : 1 ≤ n) : Etat n 0 0 = G := by
  show init n 0 = G
  simp [init]

lemma G0N (_h : 1 ≤ n) : Etat n 0 (n : ℤ) = G := by
  -- `init n n` returns `G` unconditionally: either `n = 0` (first
  -- branch) or the second `if (n : ℤ) = (n : ℤ)` fires.
  show init n (n : ℤ) = G
  simp [init]

lemma C0N1 (h : 1 ≤ n) : Etat n 0 ((n : ℤ) + 1) = C := by
  show init n ((n : ℤ) + 1) = C
  have hn_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have h1 : (n : ℤ) + 1 ≠ 0       := by omega
  have h2 : (n : ℤ) + 1 ≠ (n : ℤ) := by omega
  simp [init, h1, h2]

/-- Cells strictly between `0` and `n` (exclusive) are `L` at time 0. -/
lemma base_L (_h : 1 ≤ n) (x : ℤ) (hx0 : 0 < x) (hxn : x < (n : ℤ)) :
    Etat n 0 x = L := by
  show init n x = L
  have h0  : x ≠ 0           := by omega
  have hn  : x ≠ (n : ℤ)     := by omega
  have hn1 : x ≠ (n : ℤ) + 1 := by omega
  simp [init, h0, hn, hn1]

/-- Cells strictly past `n + 1` are `L` at time 0. -/
lemma basedollar_L (h : 1 ≤ n) (x : ℤ) (hx : (n : ℤ) + 1 < x) :
    Etat n 0 x = L := by
  show init n x = L
  have hn_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have h0  : x ≠ 0           := by omega
  have hn  : x ≠ (n : ℤ)     := by omega
  have hn1 : x ≠ (n : ℤ) + 1 := by omega
  simp [init, h0, hn, hn1]

end FsspMazoyer
end CellularAutomatas
