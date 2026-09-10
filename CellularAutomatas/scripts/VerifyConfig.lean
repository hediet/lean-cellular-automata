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
  ] ++ [
    `CellularAutomatas.proofs.constructions.speedup_one_step_pair,
    `CellularAutomatas.proofs.advice_theory.three_stage,
    `CellularAutomatas.proofs.uniform_local.expressions,
    `CellularAutomatas.proofs.uniform_local.program,
    `CellularAutomatas.proofs.uniform_local.relabel,
    `CellularAutomatas.proofs.uniform_local.correctness,
    `CellularAutomatas.proofs.uniform_local.composition,
    `CellularAutomatas.proofs.uniform_local.examples,
    `CellularAutomatas.proofs.advice_theory.local_horizon.defs,
    `CellularAutomatas.proofs.advice_theory.local_horizon.machine,
    `CellularAutomatas.proofs.advice_theory.local_horizon.prefix_stability,
    `CellularAutomatas.proofs.advice_theory.local_horizon.deadline,
    `CellularAutomatas.proofs.advice_theory.local_horizon.producer,
    `CellularAutomatas.proofs.advice_theory.local_horizon.normalize,
    `CellularAutomatas.proofs.advice_theory.local_horizon.closure,
    `CellularAutomatas.proofs.advice_theory.local_horizon.cart,
    `CellularAutomatas.proofs.advice_theory.local_horizon.dyadic_prefix,
    `CellularAutomatas.proofs.advice_theory.local_horizon.examples,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.normalized,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.initialization,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.packets,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.event_readout,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.readiness,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.retained_events,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.packed_target,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.async_full_line,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.async_driven,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.deadline,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.progress,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.assembly,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.composition,
    `CellularAutomatas.proofs.advice_theory.local_horizon.fusion.examples,
    `CellularAutomatas.proofs.advice_theory.bounded_anticipation.defs,
    `CellularAutomatas.proofs.advice_theory.bounded_anticipation.global_readout,
    `CellularAutomatas.proofs.advice_theory.bounded_anticipation.diary,
    `CellularAutomatas.proofs.advice_theory.bounded_anticipation.diary_decode,
    `CellularAutomatas.proofs.advice_theory.bounded_anticipation.diagonal_readout,
    `CellularAutomatas.proofs.advice_theory.bounded_anticipation.characterization,
    `CellularAutomatas.proofs.advice_theory.bounded_anticipation.examples
  ].map (fun module => (module, [`Quot.sound, `Classical.choice, `propext]))
