import CellularAutomatas.proofs.uniform_local.expressions
import CellularAutomatas.proofs.uniform_local.program
import CellularAutomatas.proofs.uniform_local.correctness
import CellularAutomatas.proofs.uniform_local.composition
import CellularAutomatas.proofs.uniform_local.examples

/-!
# Uniform opaque-state local simulation

`UniformLocal.Program` is a finite program parameterized by a target CA.
`Program.compile` interprets it as a radius-one CA transformer. Primitive
wrappers have finite control and a fixed number of target-state registers.
Expressions can copy states, embed input symbols, apply the target transition,
and observe target outputs. They cannot enumerate, compare, pattern-match,
or otherwise inspect the target's internal state representation.

Programs admit static composition: an outer wrapper targets the entire inner
compiled CA. This remains a local CA, not a scheduled sequence of computations.
The syntax deliberately permits finite nesting; no flattening theorem into a
single primitive `LocalRule` is claimed.

`CellAutomaton.IsUniformlyLocal f` asserts that one such program implements
`f` for every target. Endpoint correctness is an independent predicate,
`PreservesRtEndpointOn`. Both implementation and correctness compose.

`Advice.IsUniformlyLocallySimulatable` requires one program per alphabet lift
and output alphabet, chosen before the target CA. Its target receives both
input and advice, matching advised recognition. It has no empty-word endpoint
obligation and makes no time-zero or whole-diagram decoding assertion.

Advice-level composition closure and letterwise instances are proved.
Containment/equality with three-stage, finite-stage, and RT-closed advice
is not asserted here; existing constructions still need program witnesses.
-/
