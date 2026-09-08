import CellularAutomatas.proofs.advice_theory.marked_prefix.prefix_transform
import CellularAutomatas.proofs.advice_theory.marked_prefix.prefix_reversal
import CellularAutomatas.proofs.advice_theory.marked_prefix.selector_marker
import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_config
import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_join
import CellularAutomatas.proofs.advice_theory.marked_prefix.marked_initialization
import CellularAutomatas.proofs.advice_theory.marked_prefix.lifted_packets
import CellularAutomatas.proofs.advice_theory.marked_prefix.clock_arithmetic
import CellularAutomatas.proofs.advice_theory.marked_prefix.release_envelope
import CellularAutomatas.proofs.advice_theory.marked_prefix.producer_budget
import CellularAutomatas.proofs.advice_theory.marked_prefix.raw_pack_three
import CellularAutomatas.proofs.advice_theory.marked_prefix.delayed_reflection
import CellularAutomatas.proofs.advice_theory.marked_prefix.reversal_packets
import CellularAutomatas.proofs.advice_theory.marked_prefix.reversal_initialization
import CellularAutomatas.proofs.advice_theory.marked_prefix.periodic_readout
import CellularAutomatas.proofs.advice_theory.marked_prefix.exact_readout
import CellularAutomatas.proofs.advice_theory.marked_prefix.final_readout
import CellularAutomatas.proofs.advice_theory.marked_prefix.eventual_acceptance
import CellularAutomatas.proofs.advice_theory.marked_prefix.consumer_normalization
import CellularAutomatas.proofs.advice_theory.marked_prefix.asynchronous_half_line
import CellularAutomatas.proofs.advice_theory.marked_prefix.async_driven
import CellularAutomatas.proofs.advice_theory.marked_prefix.async_origin
import CellularAutomatas.proofs.advice_theory.marked_prefix.async_catchup
import CellularAutomatas.proofs.advice_theory.marked_prefix.reversal_rt_closed
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt

/-!
# Strongly RT-closed marked-prefix transformations

This entry point collects the prefix algebra, separation from two-stage advice,
packet producers, clock arithmetic, exact readout, and finite-exception repair.
The end-to-end construction proves that dyadic-prefix reversal is strongly
RT-closed, yet is not two-stage advice over an alphabet with at least two
symbols. More generally, every spatially linear-time-computable transformation
of the dyadic prefix gives strongly RT-closed advice. The LT construction
includes concrete online packing, a bounded finite-strip producer, and the
complete consumer pipeline; no auxiliary existence hypotheses remain.
-/
