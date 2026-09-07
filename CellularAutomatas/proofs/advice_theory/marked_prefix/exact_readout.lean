import CellularAutomatas.proofs.advice_theory.marked_prefix.periodic_readout
import CellularAutomatas.proofs.constructions.speedup_k_step

namespace CellularAutomatas.MarkedPrefix

open CellAutomaton

variable {α β : Type} [Alphabet α] [Alphabet β]

/-- Remove the fixed sampling/history delay. The caller proves correctness
only for the packet containing the final real-time observation. -/
def exactReadout (source : CellAutomaton (Option α) (Fin 3 → β))
    (offset : ℕ) : SpeedupKSteps where
  α := α
  β := β
  C_orig := (PeriodicTripleReadout.mk source offset).decompressor.C
  k := offset + 3
  c := offset + 4

theorem exactReadout_spec (source : CellAutomaton (Option α) (Fin 3 → β))
    (offset : ℕ) (hoffset : 0 < offset) (w : Word α)
    (a : ℕ) (r : Fin 3)
    (hindex : w.length - 1 = 3 * a + r)
    (hbound : w.length - 1 + (offset + 3) < (offset + 4) * w.length)
    (packet : Fin 3 → β)
    (hpacket : source.trace (word_to_config w) (3 * (a + 1) + offset) = packet) :
    (exactReadout source offset).C.trace (word_to_config w) (w.length - 1) =
      packet r := by
  let sampler : PeriodicTripleReadout := ⟨source, offset⟩
  calc
    (exactReadout source offset).C.trace (word_to_config w) (w.length - 1)
        = sampler.decompressor.C.trace (word_to_config w)
            (w.length - 1 + (offset + 3)) := by
          show (exactReadout source offset).C.trace (word_to_config w) (w.length - 1) =
            (exactReadout source offset).C_orig.trace (word_to_config w)
              (w.length - 1 + (exactReadout source offset).k)
          exact (exactReadout source offset).spec w (w.length - 1) (by omega) hbound
    _ = sampler.decompressor.C.trace (word_to_config w) (3 * a + r + offset + 3) := by
          congr 1
          omega
    _ = packet r := sampler.decode_packet (word_to_config w) hoffset a r packet hpacket

end CellularAutomatas.MarkedPrefix
