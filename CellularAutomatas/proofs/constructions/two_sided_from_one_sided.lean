import CellularAutomatas.proofs.constructions.two_sided_fssp_half_runtime

/-!
# Two-sided half-runtime simulations from a one-sided FSSP

The checked result is `two_sided_half_runtime_of_one_sided`. It provides two
uniform parity-specific automata and proves that their left halves fire at the
optimal two-sided times:

* odd input `2 * k + 1`: time `2 * k`;
* even input `2 * k`: time `2 * k - 1`.

This module intentionally does not claim `SolvesTwoSidedFSSPOptimal`: combining
the parity-specific left-half simulations into one all-cells automaton still
requires mirrored tracks and a parity selector.
-/
