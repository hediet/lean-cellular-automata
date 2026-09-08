import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.closure
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.prefix_packets

namespace CellularAutomatas.MarkedPrefix

/-- Applying any spatially linear-time-computable transformation to the dyadic
prefix of length at most half the input, and padding the rest with `blank`,
gives strongly RT-closed advice. The controller and every simulation stage
are concrete; no producer, clock, or packet hypotheses remain. -/
noncomputable def dyadicPrefixTransform_rt_closed
    {α Γ : Type} [Alphabet α] [Alphabet Γ]
    (F : Advice α Γ) (hF : F.IsLtAdvice) (blank : Γ) :
    (prefixTransform dyadicSelector F blank).rt_closed := by
  apply LT.rtClosed_of_controllers F hF blank
  intro σ _
  exact LT.PrefixPackets.prefixController (LT.packingFactor hF.c)
    (by
      have hlarge := LT.packingFactor_large hF.c
      omega) σ

end CellularAutomatas.MarkedPrefix
