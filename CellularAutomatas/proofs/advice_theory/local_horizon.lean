import CellularAutomatas.proofs.advice_theory.local_horizon.closure
import CellularAutomatas.proofs.advice_theory.local_horizon.machine
import CellularAutomatas.proofs.advice_theory.local_horizon.prefix_stability
import CellularAutomatas.proofs.advice_theory.local_horizon.cart
import CellularAutomatas.proofs.advice_theory.local_horizon.dyadic_prefix
import CellularAutomatas.proofs.advice_theory.local_horizon.examples
import CellularAutomatas.proofs.advice_theory.local_horizon.fusion

/-!
# Packet-readout machines and domain-explicit contracts

`PacketReadoutMachine` is the finite clock/data implementation.
`PacketReadoutMachine.RTContractOn machine domain` separately specifies its
one-shot schedule and deadline. The domain has no default, including in the
older `RealizableHorizon` interface.

`Advice.IsPacketReadoutOn` states realization on a domain;
`Advice.IsGlobalPacketReadout` is the explicitly named all-input subclass.
Only the latter implies unconditional strong RT closure.

`RealizableHorizon` witnesses local one-shot clock events on nonempty valid
inputs. `LocalHorizon.readout` samples a packet-valued CA at those events,
using physical position `i / q` and packet slot `i % q`.

`LocalHorizon.rt_closed` eliminates every globally valid RT-admissible
readout, including arbitrary alphabet lifts. `Normalize.producer` joins raw
input with sampled advice and certifies exterior packets independently of the
horizon. `PacketProducer.trace_final` is the exact-time consumer interface.

`raw_sample_eq_take` proves bounded prefix dependence for globally valid
horizons: the packet at `p` stabilizes after `q * (p + κ + 1)` input symbols.
The domain-relative early-pulse lemma explicitly requires a valid prefix;
it cannot be applied to arbitrary truncations of prepared inputs.

`cartProducer` and `dyadicPrefixProducer` instantiate the same interface.
The latter operates on the existing marked preparation beyond its finite
packing cutoff; the public dyadic LT closure theorem removes the marker and
repairs short inputs.

`PacketProducer.trace_rt_eq` upgrades final readout to complete trace
composition when the generated word function is causal. `cart_composition`
is this specialization for CART. No causality, trace-composition, or maximality
claim is made for an arbitrary horizon readout.

`Advice.IsPacketReadoutOn.compose` separately proves whole-word producer
fusion on compatible domains, without assuming causality. Its construction
retains the second producer's events before packing and simulates the full
integer line asynchronously from the first producer's packets.
-/
