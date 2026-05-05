/-
  Mazoyer's 6-state minimal-time FSSP CA, lifted into our
  `CellAutomaton α？ Bool` framework with a 7th explicit `Border` state.

  Background.
  -----------
  The Coq formalization (`external/firing-squad/autom.v`) places the
  "right phantom" pattern `[G, C, L, L, …]` directly on the integer line
  starting at position `N+1`. Lemma `vert_droite` proves that position
  `N+1` stays in state `G` for all `t ∈ [0, 2N]`, so the rightmost real
  cell `N` always sees `G` to its right.  Similarly, the Coq source's
  leftmost cell uses a hardcoded virtual neighbour `L`:
      Etat (t+1) 0 = δ L (Etat t 0) (Etat t 1).

  In our `CellAutomaton α？ Bool` framework, every off-array cell carries
  the same `embed none = Border` state and evolves under the same `δ`.
  We therefore add a 7th state `Border` and encode the asymmetry through
  the transition rule:

  *   `δ(_, Border, _) = Border`              -- border is a permanent wall
  *   `δ(Border, c1, c2) = MazoyerDelta(L, c1, c2)`     -- left phantom = L
  *   `δ(c0, c1, Border) = MazoyerDelta(c0, c1, G)`     -- right phantom = G
  *   `δ(c0, c1, c2)` (no `Border`) = `MazoyerDelta(c0, c1, c2)`

  By construction every cell inside `[0, n)` evolves exactly like the
  corresponding cell of Mazoyer's `Etat n`, so any correctness theorem
  proved in Coq transfers (with at most off-by-trivial reindexing). This
  file only sets up the construction and validates it with `native_decide`
  tests on small `n`.

  References.
  -----------
  Reuses the 6-state transition table of `fssp_mazoyer.lean` (which is in
  turn ported from `external/firing-squad/autom.v`). To keep the present
  file self-contained, the table is duplicated here -- this is mechanical
  and we may consolidate later.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.fssp

namespace CellularAutomatas
namespace FsspMazoyerCA

/-! ### Alphabet -/

/-- Mazoyer's six interior states plus an explicit `Border` state. -/
inductive Couleur
  | A | B | C | L | G | F | Border
deriving DecidableEq, Repr, Inhabited, Fintype

open Couleur

instance : Alphabet Couleur := {}

/-! ### Mazoyer's interior transition table

Verbatim copy of the helper functions from `autom.v` (and from
`fssp_mazoyer.lean`). All clauses defaulting to `F` for legacy `F`
self-loops are kept; the `Border` case is added at the end of each
helper as a `Border` self-loop -- this row is *never* reached when
the helper is invoked from `MazoyerDelta` proper, but it makes the
match exhaustive without `_ => Border` catch-alls. -/

private def TAA : Couleur → Couleur
  | A => A | B => B | C => C | L => A | G => B | F => F | Border => Border
private def TBA : Couleur → Couleur
  | A => F | B => G | C => C | L => G | G => C | F => F | Border => Border
private def TLA : Couleur → Couleur
  | A => A | B => L | C => G | L => A | G => F | F => F | Border => Border
private def TAB : Couleur → Couleur
  | A => B | B => B | C => L | L => G | G => F | F => F | Border => Border
private def TBB : Couleur → Couleur
  | A => A | B => B | C => C | L => G | G => B | F => F | Border => Border
private def TCB : Couleur → Couleur
  | A => A | B => F | C => F | L => L | G => L | F => F | Border => Border
private def TLB : Couleur → Couleur
  | A => G | B => B | C => L | L => F | G => B | F => F | Border => Border
private def TGB : Couleur → Couleur
  | A => C | B => F | C => B | L => C | G => G | F => F | Border => Border
private def TBC : Couleur → Couleur
  | A => F | B => F | C => C | L => C | G => G | F => F | Border => Border
private def TCC : Couleur → Couleur
  | A => A | B => B | C => C | L => C | G => B | F => F | Border => Border
private def TLC : Couleur → Couleur
  | A => A | B => G | C => C | L => C | G => G | F => F | Border => Border
private def TAL : Couleur → Couleur
  | A => L | B => L | C => L | L => G | G => C | F => F | Border => Border
private def TCL : Couleur → Couleur
  | A => L | B => L | C => L | L => A | G => G | F => F | Border => Border
private def TGL : Couleur → Couleur
  | A => L | B => L | C => L | L => C | G => A | F => F | Border => Border
private def TG_L : Couleur → Couleur  -- middle G, right L; param: left
  | A => B | B => B | C => A | L => A | G => B | F => F | Border => Border
private def TG_G : Couleur → Couleur  -- middle G, right G; param: left
  | A => F | B => G | C => A | L => F | G => F | F => F | Border => Border

/-- Transition with middle cell `A`. -/
private def MazoyerA (c0 c2 : Couleur) : Couleur :=
  match c0 with
  | A => TAA c2
  | B => TBA c2
  | C => A
  | L => TLA c2
  | G => C
  | F => F
  | Border => Border

/-- Transition with middle cell `B`. -/
private def MazoyerB (c0 c2 : Couleur) : Couleur :=
  match c0 with
  | A => TAB c2
  | B => TBB c2
  | C => TCB c2
  | L => TLB c2
  | G => TGB c2
  | F => F
  | Border => Border

/-- Transition with middle cell `C`. -/
private def MazoyerC (c0 c2 : Couleur) : Couleur :=
  match c0 with
  | A => B
  | B => TBC c2
  | C => TCC c2
  | L => TLC c2
  | G => B
  | F => F
  | Border => Border

/-- Transition with middle cell `L`. -/
private def MazoyerL (c0 c2 : Couleur) : Couleur :=
  match c0 with
  | A => TAL c2
  | B => L
  | C => TCL c2
  | L => L
  | G => TGL c2
  | F => L
  | Border => Border

/-- Transition with middle cell `G`. -/
private def MazoyerG (c0 c2 : Couleur) : Couleur :=
  match c2 with
  | A => G
  | B => G
  | C => G
  | L => TG_L c0
  | G => TG_G c0
  | F => G
  | Border => Border

/-- Mazoyer's *original* 6-state local rule, extended trivially to
    `Border` (which is never invoked from the lifted `δ` below
    except when the input is already `Border`). -/
private def MazoyerDelta (c0 c1 c2 : Couleur) : Couleur :=
  match c1 with
  | A => MazoyerA c0 c2
  | B => MazoyerB c0 c2
  | C => MazoyerC c0 c2
  | L => MazoyerL c0 c2
  | G => MazoyerG c0 c2
  | F => F
  | Border => Border

/-! ### Lifted transition rule with `Border` handling

* `Border` in the **middle**: stay `Border`.
* `Border` on the **left only**: pretend the left neighbour is `L`
  (matches Mazoyer's `Etat (t+1) 0 = δ L (Etat t 0) (Etat t 1)`).
* `Border` on the **right only**: pretend the right neighbour is `G`
  (matches `vert_droite`: position `N+1` is always `G`).
* No `Border`: use Mazoyer's δ unchanged.

When **both** sides are `Border` (an isolated singleton), treat the
left as `L` and right as `G`, matching the ends-meeting case. -/

def δ (c0 c1 c2 : Couleur) : Couleur :=
  match c1 with
  | Border => Border
  | _ =>
    let leftSubst  : Couleur := match c0 with | Border => L | x => x
    let rightSubst : Couleur := match c2 with | Border => G | x => x
    MazoyerDelta leftSubst c1 rightSubst

/-! ### CA construction -/

/-- The CA has alphabet `Bool？` (input symbol or off-array marker) and
    output alphabet `Bool` (cell fired or not). The `general` symbol
    is `true`; quiet cells are `false`. -/
def C : LCellAutomaton Bool where
  Q := Couleur
  δ := δ
  embed
    | none       => Border
    | some true  => G
    | some false => L
  project
    | F => true
    | _ => false

/-! ### Tests for small `n`

Mazoyer / Duprat require `n ≥ 4` (the Coq axiom `2 < N` becomes `n ≥ 4`).
At time `2n - 2`, every cell `i ∈ {0, …, n-1}` should fire.

The tests below run the actual `CellAutomaton.comp` and compare with
the expected firing time. All must reduce to `true` by `native_decide`. -/

/-- Convenience: the comp output (a `Bool`) at time `t`, position `i ∈ ℕ`,
    on the canonical FSSP input of size `n`. -/
def fired (n : ℕ) (t : ℕ) (i : ℕ) : Bool :=
  C.comp ⟬fssp_left_side n⟭ t (i : ℤ)

/-- All real cells fire at time `t`. -/
def all_fire (n : ℕ) (t : ℕ) : Bool :=
  (List.range n).all fun i => fired n t i

/-- No real cell fires at time `t`. -/
def none_fire (n : ℕ) (t : ℕ) : Bool :=
  (List.range n).all fun i => ! fired n t i

/-- Internal-state snapshot: states of cells `-2 .. n+3` at time `t`,
    using the inner `Couleur` alphabet (for debugging). -/
def row (n : ℕ) (t : ℕ) : List Couleur :=
  (List.range (n + 6)).map fun i =>
    C.nextt (⦋⟬fssp_left_side n⟭⦌) t ((i : ℤ) - 2)

-- n = 4: should fire at t = 6.
example : all_fire 4 6 = true := by native_decide
example : none_fire 4 5 = true := by native_decide

-- n = 5: should fire at t = 8.
example : all_fire 5 8 = true := by native_decide
example : none_fire 5 7 = true := by native_decide

-- n = 6: should fire at t = 10.
example : all_fire 6 10 = true := by native_decide
example : none_fire 6 9 = true := by native_decide

-- n = 7: should fire at t = 12.
example : all_fire 7 12 = true := by native_decide
example : none_fire 7 11 = true := by native_decide

-- n = 8: should fire at t = 14.
example : all_fire 8 14 = true := by native_decide
example : none_fire 8 13 = true := by native_decide

-- For #eval debugging:
-- #eval row 4 0
-- #eval row 4 6  -- expect F at indices 2..5 (cells 0..3)

end FsspMazoyerCA
end CellularAutomatas
