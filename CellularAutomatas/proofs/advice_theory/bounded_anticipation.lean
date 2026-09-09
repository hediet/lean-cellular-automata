import CellularAutomatas.proofs.advice_theory.bounded_anticipation.characterization
import CellularAutomatas.proofs.advice_theory.bounded_anticipation.examples

/-!
# Bounded anticipation characterizes all-input packet readouts

For finite alphabets, `Advice.IsGlobalPacketReadout` is equivalent to bounded
anticipation together with weak RT closure, and also with strong RT closure.

The converse constructs a finite suffix probe, obtains its unadvised prefix
diary by weak closure, and uses bounded local history to decode a fixed-delay
trace. Diagonal compression and fixed event routing yield width-three packets.
No prepared-input promise, full-word oracle, or length-dependent runtime
parameter is used.
-/
