/-
  Configuration for axiom verification.
  Edit this file to specify allowed axioms per module.
-/
import Lean

namespace CellularAutomatas
open Lean

/-- Allowed axioms configuration per module -/
def verifyConfig : List (Name × List Name) :=
  [
    (`CellularAutomatas.results, [
      `Quot.sound,
      `Classical.choice,
      `propext
    ]),
    (`CellularAutomatas.proofs.constructions.linear_time_speedup, [
      `Quot.sound,
      `Classical.choice,
      `propext
    ]),
    (`CellularAutomatas.proofs.advice_theory.time_advice_combinators, [
      `Quot.sound,
      `Classical.choice,
      `propext
    ]),
    (`CellularAutomatas.proofs.advice_theory.compress_n_is_rt_advice, [
      `Quot.sound,
      `Classical.choice,
      `propext
    ]),
    (`CellularAutomatas.proofs.advice_theory.run_after_n_time_advice, [
      `Quot.sound,
      `Classical.choice,
      `propext
    ]),
    (`CellularAutomatas.proofs.advice_theory.rt_eq_lt_iff_compress2_weak_rt_closed, [
      `Quot.sound,
      `Classical.choice,
      `propext
    ])
  ]
