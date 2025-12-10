/-
  Configuration for axiom verification.
  Edit this file to specify allowed axioms per module.
-/
import Lean

open Lean

/-- Allowed axioms configuration per module -/
def verifyConfig : List (Name × List Name) :=
  [
    (`CellularAutomatas.results, [
      `Quot.sound,
      `Classical.choice,
      `propext
    ])
  ]
