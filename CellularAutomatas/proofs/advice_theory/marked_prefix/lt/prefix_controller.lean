import CellularAutomatas.proofs.advice_theory.marked_prefix.reversal_packets
import CellularAutomatas.proofs.constructions.speedup_compressed

namespace CellularAutomatas.MarkedPrefix.LT

/-- The two projections of an online prefix packer share the same release
diagonal. Only the initializer drops suffix packets; the raw consumer track
must retain them. The length and endpoint are proof parameters, not CA state. -/
structure PrefixController (q : ℕ) (α : Type) [Alphabet α] where
  offset : ℕ
  offset_pos : 0 < offset
  classified :
    CellAutomaton (Option (α × Bool)) (Option (Bool × (Fin q → Option α)))
  initializer :
    CellAutomaton (Option (α × Bool))
      ((Bool × Bool) × Option (Fin q → Option α))
  classified_spec : ∀ (w : Word α) (M : ℕ), 0 < M → q * M ≤ w.length →
    ∀ t p : ℕ,
      classified.comp (ReversalPackets.markedWord w (q * M - 1)) t p =
        if t = offset + (q - 1) * p then
          some (decide (p < M), SpeedupKx.compress q (word_to_config w) p)
        else none
  packets_spec : ∀ (w : Word α) (M : ℕ), 0 < M → q * M ≤ w.length →
    ∀ t p : ℕ,
      (initializer.comp (ReversalPackets.markedWord w (q * M - 1)) t p).2 =
        if p < M ∧ t = offset + (q - 1) * p then
          some (SpeedupKx.compress q (word_to_config (w.take (q * M))) p)
        else none
  boundaries_spec : ∀ (w : Word α) (M : ℕ), 0 < M → q * M ≤ w.length →
    ∀ t p : ℕ, p < M → offset + (q - 1) * p < t →
      (initializer.comp (ReversalPackets.markedWord w (q * M - 1)) t p).1 =
        (decide (p = 0), decide (p + 1 = M))

end CellularAutomatas.MarkedPrefix.LT
