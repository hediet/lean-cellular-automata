/-
  Mazoyer's 6-state minimal-time (2n-2) FSSP CA, ported from
  Jean Duprat's Coq formalization at
    https://github.com/rocq-archive/firing-squad
  (see external/firing-squad/autom.v).

  This file provides only the construction + a simulator + small-case
  tests. The correctness theorem (`SolvesFSSPOptimal`) is left to a
  follow-up file; here we just want a runnable / `#eval`-able CA.

  Setup (matches the Coq source exactly):
  * 6 states: `A`, `B`, `C`, `L` (quiet), `G` (general), `F` (fire).
  * For an array of `n = N+1` cells (n ≥ 4), the initial configuration on
    the integer line `Etat 0 : ℤ → Couleur` is
        cell 0       : G
        cells 1..N   : L
        cell N+1     : G        -- right "ghost general"
        cell N+2     : C        -- right "ghost marker"
        cells > N+2  : L
        cells < 0    : L
  * One step: `Etat (t+1) p = δ (Etat t (p-1)) (Etat t p) (Etat t (p+1))`,
    with the convention that cells `< 0` (and far right) are evaluated by
    the same recursion (they are surrounded by `L`s and stay `L`).
  * Final theorem (target): for all `i ∈ {0,…,N}`, `Etat (2N) i = F`.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Computability.Language

namespace CellularAutomatas
namespace FsspMazoyer

/-! ### Alphabet -/

inductive Couleur
  | A | B | C | L | G | F
deriving DecidableEq, Repr, Inhabited

open Couleur

/-! ### Transition table

Verbatim port of `external/firing-squad/autom.v`.
Each helper mirrors the Coq definition of the same name. -/

def Transition_A_A : Couleur → Couleur
  | A => A | B => B | C => C | L => A | G => B | F => F

def Transition_B_A : Couleur → Couleur
  | A => F | B => G | C => C | L => G | G => C | F => F

def Transition_L_A : Couleur → Couleur
  | A => A | B => L | C => G | L => A | G => F | F => F

def Transition_A_B : Couleur → Couleur
  | A => B | B => B | C => L | L => G | G => F | F => F

def Transition_B_B : Couleur → Couleur
  | A => A | B => B | C => C | L => G | G => B | F => F

def Transition_C_B : Couleur → Couleur
  | A => A | B => F | C => F | L => L | G => L | F => F

def Transition_L_B : Couleur → Couleur
  | A => G | B => B | C => L | L => F | G => B | F => F

def Transition_G_B : Couleur → Couleur
  | A => C | B => F | C => B | L => C | G => G | F => F

def Transition_B_C : Couleur → Couleur
  | A => F | B => F | C => C | L => C | G => G | F => F

def Transition_C_C : Couleur → Couleur
  | A => A | B => B | C => C | L => C | G => B | F => F

def Transition_L_C : Couleur → Couleur
  | A => A | B => G | C => C | L => C | G => G | F => F

def Transition_A_L : Couleur → Couleur
  | A => L | B => L | C => L | L => G | G => C | F => F

def Transition_C_L : Couleur → Couleur
  | A => L | B => L | C => L | L => A | G => G | F => F

def Transition_G_L : Couleur → Couleur
  | A => L | B => L | C => L | L => C | G => A | F => F

/-- In the Coq source this is `Transition__G_L`: the case of the
    middle cell being `G` and the **right** cell being `L`,
    parameterised by the **left** cell `c0`. -/
def Transition_G_L_left : Couleur → Couleur
  | A => B | B => B | C => A | L => A | G => B | F => F

/-- In the Coq source `Transition__G_G`: middle `G`, right `G`,
    parameterised by the left cell `c0`. -/
def Transition_G_G_left : Couleur → Couleur
  | A => F | B => G | C => A | L => F | G => F | F => F

/-- Middle cell is `A`. -/
def Transition_A (c0 c2 : Couleur) : Couleur :=
  match c0 with
  | A => Transition_A_A c2
  | B => Transition_B_A c2
  | C => A
  | L => Transition_L_A c2
  | G => C
  | F => F

/-- Middle cell is `B`. -/
def Transition_B (c0 c2 : Couleur) : Couleur :=
  match c0 with
  | A => Transition_A_B c2
  | B => Transition_B_B c2
  | C => Transition_C_B c2
  | L => Transition_L_B c2
  | G => Transition_G_B c2
  | F => F

/-- Middle cell is `C`. -/
def Transition_C (c0 c2 : Couleur) : Couleur :=
  match c0 with
  | A => B
  | B => Transition_B_C c2
  | C => Transition_C_C c2
  | L => Transition_L_C c2
  | G => B
  | F => F

/-- Middle cell is `L`. Note: in the Coq source the `F` row maps to `L`
    (i.e. `L` cells with an `F` neighbour stay `L`); kept verbatim. -/
def Transition_L (c0 c2 : Couleur) : Couleur :=
  match c0 with
  | A => Transition_A_L c2
  | B => L
  | C => Transition_C_L c2
  | L => L
  | G => Transition_G_L c2
  | F => L

/-- Middle cell is `G`. The case split is on the **right** neighbour first
    (this matches the Coq source). -/
def Transition_G (c0 c2 : Couleur) : Couleur :=
  match c2 with
  | A => G
  | B => G
  | C => G
  | L => Transition_G_L_left c0
  | G => Transition_G_G_left c0
  | F => G

/-- The full local transition rule `δ(c0, c1, c2)`. -/
def δ (c0 c1 c2 : Couleur) : Couleur :=
  match c1 with
  | A => Transition_A c0 c2
  | B => Transition_B c0 c2
  | C => Transition_C c0 c2
  | L => Transition_L c0 c2
  | G => Transition_G c0 c2
  | F => F

/-! ### Initial configuration & one-step law

This mirrors `Etat` from `autom.v`. The line has `n = N + 1` cells.
-/

/-- Initial configuration on an `n = N+1` line: cell 0 is `G`,
    cells `1..N` are `L`, cell `N+1` is `G`, cell `N+2` is `C`,
    everything else is `L` (including cells with negative index). -/
def init (n : ℕ) (p : ℤ) : Couleur :=
  if p = 0 then G
  else if p = (n : ℤ) then G
  else if p = (n : ℤ) + 1 then C
  else L

/-- Configuration at time `t`, position `p`, for an `n = N+1` array. -/
def Etat (n : ℕ) : ℕ → ℤ → Couleur
  | 0,     p => init n p
  | t + 1, p => δ (Etat n t (p - 1)) (Etat n t p) (Etat n t (p + 1))

@[simp] lemma Etat_zero (n : ℕ) (p : ℤ) : Etat n 0 p = init n p := rfl

@[simp] lemma Etat_succ (n : ℕ) (t : ℕ) (p : ℤ) :
    Etat n (t + 1) p = δ (Etat n t (p - 1)) (Etat n t p) (Etat n t (p + 1)) := rfl

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
