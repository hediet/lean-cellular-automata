import CellularAutomatas.proofs.advice_theory.marked_prefix.async_catchup
import CellularAutomatas.proofs.advice_theory.marked_prefix.eventual_acceptance
import CellularAutomatas.proofs.advice_theory.marked_prefix.final_readout
import CellularAutomatas.proofs.advice_theory.marked_prefix.reversal_initialization
import CellularAutomatas.proofs.advice_theory.middle_exp_two_stage
import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage

namespace CellularAutomatas.MarkedPrefix

namespace ReversalClosure

open ReversalInitialization

variable {α σ β : Type} [Alphabet α] [Alphabet σ] [Alphabet β]

/-- The concrete reversed-prefix initialization drives the accelerated
consumer, retaining the full lifted input alphabet. -/
def source (π : σ → α)
    (consumer : CellAutomaton (Option (σ × Option α)) β) :
    CellAutomaton (Option (σ × Bool)) (Fin 3 → β) :=
  AsyncCatchup.source (rawPackets σ) (advicePackets π) consumer

theorem source_spec (π : σ → α)
    (consumer : CellAutomaton (Option (σ × Option α)) β)
    (w : Word σ) (hn : 2 ≤ w.length) (j : ℕ)
    (hcatch : dyadicSelector w.length - 1 ≤ 2 * j) :
    (source π consumer).trace
        (word_to_config (controllerWord w)) (3 + 3 * j) =
      (normalizedSpeedupAndTrace3 consumer).C.trace
        (SpeedupKx.compress 3
          (word_to_config (((dyadicPrefixReversal α).lift π).annotate w))) j := by
  have hcontroller : 0 < (controllerWord w).length := by
    simpa [controllerWord, Advice.annotate] using (show 0 < w.length by omega)
  apply AsyncCatchup.trace_eq_normalized_of_catchup
    (rawPackets σ) (advicePackets π) consumer
    (controllerWord w) hcontroller
    w ((dyadicPrefixReversal α).lift π) none
    3 (dyadicSelector w.length - 1) j
  · intro t p
    exact rawPackets_spec w hn t p
  · intro t p
    exact advicePackets_spec π w hn t p
  · exact hcatch

/-- Decode the total asynchronous output and remove its fixed six-tick delay. -/
def simulator (π : σ → α) (consumer : CA_rt (σ × Option α)) :
    CA_rt (σ × Bool) :=
  toRtCa (exactReadout (source π consumer.toCellAutomaton) 3).C

theorem simulator_accepts_eq (π : σ → α)
    (consumer : CA_rt (σ × Option α)) (w : Word σ)
    (hn : 2 ≤ w.length) :
    (simulator π consumer).accepts ((Advice.middle_exp σ).annotate w) =
      consumer.accepts (((dyadicPrefixReversal α).lift π).annotate w) := by
  have hcontrollerLength : (controllerWord w).length = w.length := by
    simp [controllerWord, Advice.annotate]
  have hadvisedLength :
      (((dyadicPrefixReversal α).lift π).annotate w).length = w.length := by
    simp [Advice.annotate]
  have hfinal := exactReadout_normalized_final_of_catchup
    (source π consumer.toCellAutomaton) consumer.toCellAutomaton
    3 (by decide) (controllerWord w) (by omega)
    (((dyadicPrefixReversal α).lift π).annotate w) (by omega)
    (dyadicSelector w.length)
    (by
      rw [hcontrollerLength]
      exact dyadicSelector_le_half w.length)
    (by
      intro j hj
      simpa only [Nat.add_comm 3 (3 * j)] using
        source_spec π consumer.toCellAutomaton w hn j hj)
  change
    (exactReadout (source π consumer.toCellAutomaton) 3).C.trace
        (word_to_config (controllerWord w)) ((controllerWord w).length - 1) =
      consumer.toCellAutomaton.trace
        (word_to_config (((dyadicPrefixReversal α).lift π).annotate w))
        ((((dyadicPrefixReversal α).lift π).annotate w).length - 1)
  simpa only [hcontrollerLength, hadvisedLength] using hfinal

end ReversalClosure

/-- Dyadic-prefix reversal is strongly RT-closed. The construction works with
every alphabet lift; finite-exception repair handles lengths zero and one. -/
noncomputable def dyadicPrefixReversal_rt_closed
    (α : Type) [Alphabet α] :
    (dyadicPrefixReversal α).rt_closed := by
  have hmarker : (Advice.middle_exp α).rt_closed := by
    let witness := middle_exp_two_stage_advice (α := α)
    rw [← witness.spec]
    exact two_stage_is_rt_closed witness.witness
  refine rtClosed_of_eventual_marked_simulators
    (dyadicPrefixReversal α) (Advice.middle_exp α) hmarker 2
    (fun σ _ π => ReversalClosure.simulator π) ?_
  intro σ _ π consumer w hn
  rw [middle_exp_lift_eq π]
  rw [ReversalClosure.simulator_accepts_eq π consumer w hn]

/-- Strong RT closure does not imply that advice is two-stage. -/
theorem exists_rt_closed_not_two_stage :
    ∃ adv : Advice Bool (Option Bool),
      Nonempty adv.rt_closed ∧ IsEmpty adv.is_two_stage_advice := by
  refine ⟨dyadicPrefixReversal Bool,
    ⟨dyadicPrefixReversal_rt_closed Bool⟩, ?_⟩
  exact dyadicPrefixReversal_not_two_stage_advice (by decide)

/-- Strong RT closure does not imply uniformly bounded future variation. -/
theorem exists_rt_closed_not_finite_future_variation :
    ∃ adv : Advice Bool (Option Bool),
      Nonempty adv.rt_closed ∧ ¬adv.finite_future_variation := by
  refine ⟨dyadicPrefixReversal Bool,
    ⟨dyadicPrefixReversal_rt_closed Bool⟩, ?_⟩
  exact dyadicPrefixReversal_not_finite_future_variation (by decide)

end CellularAutomatas.MarkedPrefix
