import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.folded_transform
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.rt_closed

/-!
# Strong RT closure of linear-time prefix transformations

`MarkedPrefix.dyadicPrefixTransform_rt_closed` applies to every `IsLtAdvice`
witness, with arbitrary finite input/output alphabets and an arbitrary padding
symbol. It preserves all alphabet lifts required by strong RT closure.

The construction stabilizes the transform's spatial output, folds its
workspace into a finite strip, and runs a packed asynchronous simulation with
two dead endpoints. Online classification supplies the marked prefix without
waiting for a marker signal at the origin. Computed prefix packets and raw
suffix packets then initialize the accelerated real-time consumer.

For coefficient `c`, a fixed power-of-two factor `q >= c+2` exactly packs all
sufficiently long dyadic prefixes. The producer's bound `(q-1+c)*(L/q)` fits
local-horizon deadline. The producer is packaged by
`LocalHorizon.dyadicProducer`, and the generic local-horizon consumer supplies
the exact final readout; finite-exception repair handles short words.
No controller-existence or simulator-correctness premises remain in the public
theorem.
-/
