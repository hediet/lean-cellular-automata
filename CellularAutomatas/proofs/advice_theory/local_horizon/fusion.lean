import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.composition
import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.examples

/-!
# Fusion of domain-relative packet producers

`Advice.IsPacketReadoutOn.compose` constructs one readout for `B (A w)`
whenever the first promised domain maps into the second. It requires neither
global validity nor causality, and does not pass through language RT closure.

Normalization supplies controlled exterior releases. The second producer's
events are retained before packing; a full-integer-line asynchronous simulator
then consumes the first producer's packets. Local readiness is converted to
one-shot output, with the product packet width and a fixed startup constant.

This is whole-word composition, not pointwise equality of the two producers'
event schedules or the causal consumer's complete real-time trace.
-/
