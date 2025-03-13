# Cellular Automata in Lean 4

This repository contains a formalization of Cellular Automata using the Lean 4 theorem prover.

## Overview

The project defines various types of cellular automata and their properties, including:

*   **CellAutomaton**: Basic definition of a cellular automaton.
*   **LCellAutomaton**: Cellular automata that can map words to configurations.
*   **FCellAutomaton**: Finite cellular automata that can recognize languages (accept/reject states).
*   **tCellAutomaton**: Time-constrained cellular automata.
*   **OCellAutomaton**: Cellular automata with advice.

## Structure

*   `CellularAutomatas/`: Contains the Lean source files with definitions and proofs.
    *   `defs.lean`: Core definitions of cellular automata types.
    *   `results.lean`: Proven results.
    *   `examples.lean`: Examples of cellular automata.
*   `docs/`: Documentation and related thesis files.

## Dependencies

*   [Lean 4](https://leanprover.github.io/)
*   [Mathlib4](https://github.com/leanprover-community/mathlib4)

## Building

To build the project, make sure you have Lean 4 and Lake installed.

```bash
lake build
```
