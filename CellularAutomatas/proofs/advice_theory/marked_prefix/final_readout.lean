import CellularAutomatas.proofs.advice_theory.marked_prefix.clock_arithmetic
import CellularAutomatas.proofs.advice_theory.marked_prefix.periodic_readout
import CellularAutomatas.proofs.advice_theory.marked_prefix.exact_readout
import CellularAutomatas.proofs.advice_theory.marked_prefix.consumer_normalization
import CellularAutomatas.proofs.constructions.trace_kx

namespace CellularAutomatas.MarkedPrefix

open CellAutomaton

/-- The macro generation containing the final real-time index `n - 1`. -/
def finalGeneration (n : ℕ) : ℕ :=
  (n - 1) / 3 + 1

/-- The component of the final macro packet corresponding to index `n - 1`. -/
def finalPhase (n : ℕ) : Fin 3 :=
  ⟨(n - 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- Package an automaton with the threefold speedup-and-trace construction. -/
abbrev speedupAndTrace3 {δ β : Type} [Alphabet δ] [Alphabet β]
    (C : CellAutomaton (Option δ) β) : SpeedupAndTraceKx where
  k := 3
  α := Option δ
  β := β
  C_orig := C

variable {α δ β : Type} [Alphabet α] [Alphabet δ] [Alphabet β]

/-- Specialize `exactReadout_spec` to the quotient/remainder decomposition of
the final index. The caller supplies only nonemptiness and the final packet. -/
theorem exactReadout_final_spec
    (source : CellAutomaton (Option α) (Fin 3 → β))
    (offset : ℕ) (hoffset : 0 < offset) (w : Word α)
    (hw : 0 < w.length) (packet : Fin 3 → β)
    (hpacket :
      source.trace (word_to_config w) (3 * finalGeneration w.length + offset) =
        packet) :
    (exactReadout source offset).C.trace (word_to_config w) (w.length - 1) =
      packet (finalPhase w.length) := by
  let a := (w.length - 1) / 3
  let r := finalPhase w.length
  have hdecode :=
    MarkedPrefixClock.exact_decoding_identity 0 (w.length - 1)
  have hindex : w.length - 1 = 3 * a + (r : ℕ) := by
    change w.length - 1 =
      3 * ((w.length - 1) / 3) + (w.length - 1) % 3
    simp only [Nat.zero_add, Nat.add_zero] at hdecode
    omega
  have hbound :
      w.length - 1 + (offset + 3) < (offset + 4) * w.length := by
    have := MarkedPrefixClock.constant_speedup_side_condition
      w.length (offset + 3) hw
    omega
  apply exactReadout_spec source offset hoffset w a r hindex hbound packet
  simpa [a, finalGeneration] using hpacket

/-- If the sampled source agrees with a threefold speedup-and-trace packet at
the final macro generation, exact readout returns the original final trace. -/
theorem exactReadout_speedupAndTrace3_final
    (source : CellAutomaton (Option α) (Fin 3 → β))
    (C : CellAutomaton (Option δ) β)
    (offset : ℕ) (hoffset : 0 < offset)
    (w : Word α) (hw : 0 < w.length) (v : Word δ)
    (hagrees :
      source.trace (word_to_config w) (3 * finalGeneration w.length + offset) =
        (speedupAndTrace3 C).C.trace
          (SpeedupKx.compress 3 (word_to_config v))
          (finalGeneration w.length)) :
    (exactReadout source offset).C.trace (word_to_config w) (w.length - 1) =
      C.trace (word_to_config v) (w.length - 1) := by
  let packet :=
    (speedupAndTrace3 C).C.trace
      (SpeedupKx.compress 3 (word_to_config v))
      (finalGeneration w.length)
  let r := finalPhase w.length
  calc
    (exactReadout source offset).C.trace (word_to_config w) (w.length - 1)
        = packet r := by
          apply exactReadout_final_spec source offset hoffset w hw packet
          exact hagrees
    _ = C.trace (word_to_config v)
          (3 * ((w.length - 1) / 3) + (r : ℕ)) := by
          exact (speedupAndTrace3 C).spec1
            (c := word_to_config v)
            (t1 := (w.length - 1) / 3)
            (t2 := r)
    _ = C.trace (word_to_config v) (w.length - 1) := by
          congr 1
          change 3 * ((w.length - 1) / 3) + (w.length - 1) % 3 =
            w.length - 1
          omega

/-- A half-length marker bound guarantees that the final macro generation is
among the generations on which the source and accelerated trace agree. -/
theorem exactReadout_speedupAndTrace3_final_of_catchup
    (source : CellAutomaton (Option α) (Fin 3 → β))
    (C : CellAutomaton (Option δ) β)
    (offset : ℕ) (hoffset : 0 < offset)
    (w : Word α) (hn : 2 ≤ w.length) (v : Word δ) (L : ℕ)
    (hL : L ≤ w.length / 2)
    (hagrees : ∀ j, L - 1 ≤ 2 * j →
      source.trace (word_to_config w) (3 * j + offset) =
        (speedupAndTrace3 C).C.trace
          (SpeedupKx.compress 3 (word_to_config v)) j) :
    (exactReadout source offset).C.trace (word_to_config w) (w.length - 1) =
      C.trace (word_to_config v) (w.length - 1) := by
  apply exactReadout_speedupAndTrace3_final
    source C offset hoffset w (by omega) v
  apply hagrees
  simpa [finalGeneration] using
    MarkedPrefixClock.final_marker_bound w.length L hn hL

/-- The normalized consumer has a dead left exterior for asynchronous
simulation, while final readout still returns the original consumer's answer. -/
theorem exactReadout_normalized_final_of_catchup
    (source : CellAutomaton (Option α) (Fin 3 → β))
    (C : CellAutomaton (Option δ) β)
    (offset : ℕ) (hoffset : 0 < offset)
    (w : Word α) (hn : 2 ≤ w.length) (v : Word δ)
    (hlen : v.length = w.length) (L : ℕ) (hL : L ≤ w.length / 2)
    (hagrees : ∀ j, L - 1 ≤ 2 * j →
      source.trace (word_to_config w) (3 * j + offset) =
        (normalizedSpeedupAndTrace3 C).C.trace
          (SpeedupKx.compress 3 (word_to_config v)) j) :
    (exactReadout source offset).C.trace (word_to_config w) (w.length - 1) =
      C.trace (word_to_config v) (w.length - 1) := by
  calc
    (exactReadout source offset).C.trace (word_to_config w) (w.length - 1) =
        (normalizedConsumer C).C.trace (word_to_config v) (w.length - 1) :=
      exactReadout_speedupAndTrace3_final_of_catchup source
        (normalizedConsumer C).C offset hoffset w hn v L hL hagrees
    _ = C.trace (word_to_config v) (w.length - 1) := by
      have hfinal := normalizedConsumer_trace_final C v (by omega)
      simpa only [hlen] using hfinal

end CellularAutomatas.MarkedPrefix
