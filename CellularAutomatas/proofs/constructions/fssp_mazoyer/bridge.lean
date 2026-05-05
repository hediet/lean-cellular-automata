/-
  Mazoyer FSSP -- bridge from the `Etat`-style theorem to our
  `CellAutomaton α？ Bool` framework.

  The bridge uses the 7-state CA `FsspMazoyerCA.C` (`fssp_mazoyer_ca.lean`).
  Its `δ` is defined so that `Border` on the left substitutes for `L`
  and `Border` on the right substitutes for `G` -- mirroring exactly
  the right phantom `G` and left phantom `L` of Coq's `Etat`.

  This file:
  * Proves `F_absorbing` (`δ _ F _ = F` ⇒ once `F`, stays `F`).
  * Defines `to_ca` -- the inclusion `FsspMazoyer.Couleur → FsspMazoyerCA.Couleur`
    that maps every shared state to itself (no `Border` source).
  * States the bridge `cell_eq_Etat` linking the CA's `nextt` to the
    `Etat` framework on in-range cells. The proof requires inducting
    on `t` while tracking the right-phantom invariant `Etat n t n = G`
    for `t ≤ 2n − 2`; left as `sorry`.
  * Assembles `SolvesFSSPOptimal_FsspMazoyerCA` from `firing_squad`
    (forward direction) + `not_fire_before` (reverse) + `F_absorbing`.
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.final
import CellularAutomatas.proofs.constructions.fssp_mazoyer.not_fire
import CellularAutomatas.proofs.constructions.fssp_mazoyer_ca
import CellularAutomatas.proofs.fssp

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

/-! ### Embedding the 6-state `Couleur` into the 7-state CA alphabet -/

/-- Identity inclusion `FsspMazoyer.Couleur → FsspMazoyerCA.Couleur`.
    Every interior state maps to its CA namesake; the `Border` state
    of the CA is *not* in the image. -/
def to_ca : FsspMazoyer.Couleur → FsspMazoyerCA.Couleur
  | A => FsspMazoyerCA.Couleur.A
  | B => FsspMazoyerCA.Couleur.B
  | C => FsspMazoyerCA.Couleur.C
  | L => FsspMazoyerCA.Couleur.L
  | G => FsspMazoyerCA.Couleur.G
  | F => FsspMazoyerCA.Couleur.F

/-- `to_ca` is injective on the shared states (its image misses `Border`). -/
lemma to_ca_injective : Function.Injective to_ca := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [to_ca] at h)

/-- `to_ca x = F` iff `x = F`. -/
lemma to_ca_eq_F (x : FsspMazoyer.Couleur) :
    to_ca x = FsspMazoyerCA.Couleur.F ↔ x = F := by
  cases x <;> simp [to_ca]

/-! ### `F` is absorbing in the original Mazoyer dynamics

`δ _ F _ = F` definitionally (the `δ` matches on the middle cell first
and its `F` branch returns `F`). So once a cell becomes `F`, it stays
`F` forever. -/

lemma F_absorbing (n : ℕ) (t : ℕ) (x : ℤ) :
    Etat n t x = F → ∀ s : ℕ, Etat n (t + s) x = F := by
  intro hF s
  induction s with
  | zero => simpa using hF
  | succ s ih =>
    -- `Etat n (t + (s+1)) x` reduces def. to
    -- `δ (Etat n (t+s) (x-1)) (Etat n (t+s) x) (Etat n (t+s) (x+1))`,
    -- and `δ _ F _ = F` is `rfl`.
    show δ (Etat n (t + s) (x - 1)) (Etat n (t + s) x) (Etat n (t + s) (x + 1)) = F
    rw [ih]
    rfl

/-! ### Translate `cell n t x` (CA) ↔ `Etat n t x`

For in-range cells (`0 ≤ x ≤ n − 1`) and time `t ≤ 2n − 2`, the CA's
internal-state trace `nextt ⦋⟬fssp_left_side n⟭⦌ t x` equals
`to_ca (Etat n t x)`.

The proof needs an induction on `t` that simultaneously tracks two
boundary invariants:

  * `nextt … t (-1) = Border = embed none`  (left phantom is the CA's
    `Border` state; which the `δ` *interprets* as `L`).
  * `nextt … t n = Border` and the corresponding right-phantom δ rule
    `δ _ _ Border = MazoyerDelta _ _ G` reproduces the
    `Etat n t n = G` invariant of the original framework.

Cells `n + 1`, `n + 2`, … are also `Border` in the CA but `Etat n t k`
for `k ≥ n + 1` is *not* uniformly `L` (e.g. `Etat n 0 (n+1) = C`).
The `Etat`-side right-phantom column `n` is `G` for every `t`, which
is exactly what the CA's `Border ↦ G` substitution provides.

We restrict the bridge to in-range cells only; the *external* tape
of `Etat` (positions `≥ n`) is not relevant for the firing claim
(which is over positions `0..n − 1` only).

**Proof outline (sorry):** induction on `t`.
  * `t = 0`: both sides reduce to `init n x` resp. `embed (fssp_left_side n)[x]`.
    Direct case split on `x = 0` vs `x ∈ [1, n − 1]`.
  * `t + 1`: rewrite the CA step using the `Border ↦ L` (left edge) /
    `Border ↦ G` (right edge) substitutions, then apply the IH at
    `(t, x − 1)`, `(t, x)`, `(t, x + 1)`. The boundary cases at
    `x = 0` (left phantom is `Border`) and `x = n − 1` (right phantom
    at column `n` is `Border`) need the right-phantom invariant
    `Etat n t n = G`, which holds for all `t ≤ 2n − 2` (a separate
    induction; not yet proved). -/

lemma cell_eq_Etat (n : ℕ) (h : 4 ≤ n) (t : ℕ) (x : ℤ)
    (hx : 0 ≤ x) (hxn : x ≤ (n : ℤ) - 1) (ht : t ≤ 2 * n - 2) :
    FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t x = to_ca (Etat n t x) := by
  sorry

/-- Once we have `cell_eq_Etat`, the `comp` output (a `Bool`) at position
    `x ∈ [0, n − 1]` and time `t ≤ 2n − 2` is `true ↔ Etat n t x = F`. -/
lemma comp_eq_F (n : ℕ) (h : 4 ≤ n) (t : ℕ) (x : ℤ)
    (hx : 0 ≤ x) (hxn : x ≤ (n : ℤ) - 1) (ht : t ≤ 2 * n - 2) :
    FsspMazoyerCA.C.comp ⟬fssp_left_side n⟭ t x = true ↔ Etat n t x = F := by
  have heq := cell_eq_Etat n h t x hx hxn ht
  -- Unfold `comp = project ∘ nextt`.
  show FsspMazoyerCA.C.project (FsspMazoyerCA.C.nextt _ t x) = true ↔ _
  rw [heq]
  cases Etat n t x <;> simp [to_ca, FsspMazoyerCA.C]

/-! ### Final assembly -/

/-- The Mazoyer 7-state CA solves the optimal-time FSSP **for `n ≥ 4`**.
    The Coq proof requires the same precondition (`2 < N`).
    Cases `n ∈ {1, 2, 3}` are not handled by Mazoyer's construction. -/
theorem SolvesFSSPOptimal_FsspMazoyerCA :
    SolvesFSSPOptimal FsspMazoyerCA.C := by
  -- TODO: assembly.
  -- The forward direction: `t ≥ 2n − 2 ⇒ comp = true`.
  --   Use `firing_squad : Horizontale (2n - 2) 0 (n - 1) (F_Etat n)` to
  --   get `Etat n (2n - 2) x = F`, then `F_absorbing` to extend to all
  --   `t ≥ 2n - 2`, then `comp_eq_F` to translate.
  -- The reverse direction: `comp = true ⇒ t ≥ 2n − 2`.
  --   Contrapose: if `t < 2n − 2`, `not_fire_before` gives `Etat ≠ F`,
  --   so `comp_eq_F` gives `comp ≠ true`.
  -- The `quiescent_set` requirement: `δ _ b _ = b` for `b ∈ {Border, L}`.
  --   `Border` middle stays `Border` definitionally. For `L` middle with
  --   neighbours in `{Border, L}`: borders substitute to `L`/`G`, then
  --   `MazoyerDelta L L L = L` and `MazoyerDelta L L G = L` (the latter
  --   from the `Transition_L` `c0 = L` branch which returns `L` regardless
  --   of `c2`).
  -- All three pieces are decide-friendly given the helper lemmas;
  -- the main blocker is `cell_eq_Etat`.
  sorry

theorem SolvesFSSPOptimal_exists_via_mazoyer :
    ∃ C : CellAutomaton Bool？ Bool, SolvesFSSPOptimal C :=
  ⟨FsspMazoyerCA.C, SolvesFSSPOptimal_FsspMazoyerCA⟩

end FsspMazoyer
end CellularAutomatas
