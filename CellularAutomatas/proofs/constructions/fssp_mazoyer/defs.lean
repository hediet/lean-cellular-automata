/-
  Mazoyer FSSP -- simulator and small-case `native_decide` tests.

  Re-exports the core definitions from `jean_duprat/autom.lean` and adds
  test infrastructure (`all_fire`, `none_fire`, `row`) plus compile-time
  correctness checks for small `n`.
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.jean_duprat.autom

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

/-! ### Tests for small `n`

Mazoyer / Duprat require `n ≥ 4` (the Coq axiom `2 < N` becomes `n ≥ 4`).
At time `2n - 2`, all cells `0..n-1` should be in state `F`.

We test:
* All cells fire at `t = 2n - 2`.
* No cell has fired before then (specifically: not all cells fire at
  `t = 2n - 3`).
-/

/-- Check that every cell `i ∈ {0, …, n-1}` is in state `F` at time `t`. -/
def all_fire (n : ℕ) (t : ℕ) : Bool :=
  (List.range n).all fun i => decide (Etat n t (i : ℤ) = F)

/-- Check that every cell `i ∈ {0, …, n-1}` is **not** in state `F` at time `t`. -/
def none_fire (n : ℕ) (t : ℕ) : Bool :=
  (List.range n).all fun i => decide (Etat n t (i : ℤ) ≠ F)

/-- Pretty-print one row of the simulation: states of cells `-2 .. n+3` at time `t`. -/
def row (n : ℕ) (t : ℕ) : List Couleur :=
  (List.range (n + 6)).map fun i => Etat n t ((i : ℤ) - 2)

-- Small-case tests. Each `example` is a compile-time proof.

/-! #### Degenerate cases (n < 4)

The construction is designed for n ≥ 4. Below that threshold:
* **n = 0**: vacuously true (no cells).
* **n = 1**: cell 0 starts as `G`, becomes `F` at t=1 (not t=0 = 2·1−2).
* **n = 2**: cells never all fire simultaneously (`[A,B]` at t=2, then
  cell 0 stays non-F forever).
* **n = 3**: happens to work — all cells fire at t=4 = 2·3−2.
-/

-- n = 0: vacuously, all_fire is true for any t (no cells to check).
example : all_fire 0 0 = true := by native_decide

-- n = 1: cell 0 is G at t=0, then F from t=1 onward. Does not fire at t=0.
example : all_fire 1 0 = false := by native_decide
example : all_fire 1 1 = true := by native_decide

-- n = 2: never fires simultaneously. Cell 0 is never F.
example : all_fire 2 2 = false := by native_decide
example : all_fire 2 3 = false := by native_decide
example : all_fire 2 4 = false := by native_decide
example : all_fire 2 10 = false := by native_decide

-- n = 3: fires correctly at t = 4 = 2·3−2.
example : all_fire 3 4 = true := by native_decide
example : none_fire 3 3 = true := by native_decide

/-! #### Valid cases (n ≥ 4) -/

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

-- For convenience while iterating, also expose `#eval` snapshots.
-- Uncomment to inspect:
-- #eval row 4 0
-- #eval row 4 1
-- #eval row 4 2
-- #eval row 4 3
-- #eval row 4 4
-- #eval row 4 5
-- #eval row 4 6  -- expect F at cells 0..3

end FsspMazoyer
end CellularAutomatas
