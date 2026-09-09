import CellularAutomatas.proofs.advice_theory.marked_prefix.eventual_acceptance
import CellularAutomatas.proofs.advice_theory.marked_prefix.lifted_packets
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.lift
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.packing_budget
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.producer
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.readout
import CellularAutomatas.proofs.advice_theory.middle_exp_two_stage
import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage
import CellularAutomatas.proofs.advice_theory.local_horizon.dyadic_prefix

namespace CellularAutomatas.MarkedPrefix.LT

namespace Closure

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- The actual online finite-strip producer, asynchronous half-line consumer,
packet serializer, and constant-delay removal form one real-time simulator. -/
def simulator
    {F : Advice α Γ} (hF : F.IsLtAdvice) (blank : Γ)
    (controller : PrefixController (packingFactor hF.c) α)
    (consumer : CA_rt (α × Γ)) :
    CA_rt (α × Bool) :=
  let q := packingFactor hF.c
  letI : NeZero q := ⟨by
    have hlarge := packingFactor_large hF.c
    omega⟩
  toRtCa
    (consumerCA q (Producer.C q hF blank controller)
      consumer.toCellAutomaton controller.offset)

/-- On every input beyond the finite cutoff, the actual producer satisfies
the conditional consumer endpoint and hence preserves final acceptance. -/
theorem simulator_accepts_eq
    {F : Advice α Γ} (hF : F.IsLtAdvice) (blank : Γ)
    (controller : PrefixController (packingFactor hF.c) α)
    (consumer : CA_rt (α × Γ)) (w : Word α)
    (hn : 2 * packingFactor hF.c ≤ w.length) :
    (simulator hF blank controller consumer).accepts
        ((Advice.middle_exp α).annotate w) =
      consumer.accepts ((prefixTransform dyadicSelector F blank).annotate w) := by
  let q := packingFactor hF.c
  letI : NeZero q := ⟨by
    have hlarge := packingFactor_large hF.c
    dsimp only [q]
    omega⟩
  let prepared := (Advice.middle_exp α).annotate w
  have hlength : prepared.length = w.length := by
    simp only [prepared, Advice.annotate, List.length_zip, advice_len, min_self]
  have hinput : prepared.map Prod.fst = w :=
    List.map_fst_zip (by simp)
  have hvalid : LocalHorizon.dyadicValid q prepared := by
    refine ⟨?_, ?_⟩
    · show prepared = (Advice.middle_exp α).annotate (prepared.map Prod.fst)
      rw [hinput]
    · show 2 * q ≤ prepared.length
      simpa only [hlength] using hn
  have hnonempty : prepared ≠ [] := by
    apply List.ne_nil_of_length_pos
    have hpositive := NeZero.pos q
    omega
  -- All asynchronous timing now belongs to the local-horizon interface.
  have hfinal := (LocalHorizon.dyadicProducer hF blank controller).trace_final
    consumer.toCellAutomaton prepared hvalid hnonempty
  change
    (consumerCA q (Producer.C q hF blank controller)
      consumer.toCellAutomaton controller.offset).trace prepared
        (prepared.length - 1) =
      consumer.toCellAutomaton.trace
        ((prefixTransform dyadicSelector F blank).annotate w)
        (((prefixTransform dyadicSelector F blank).annotate w).length - 1)
  simpa only [LocalHorizon.PacketProducer.consumer, LocalHorizon.dyadicProducer,
    LocalHorizon.PacketProducer.of_exists, LocalHorizon.dyadicOutput,
    hinput, hlength, Advice.annotate, List.length_zip, advice_len, min_self] using hfinal

end Closure

/-- Conditional strong closure theorem. The only remaining premise is a
uniform family of actual online prefix controllers; all producer, consumer,
timing, lifting, and finite-exception obligations are discharged here. -/
noncomputable def rtClosed_of_controllers
    {α Γ : Type} [Alphabet α] [Alphabet Γ]
    (F : Advice α Γ) (hF : F.IsLtAdvice) (blank : Γ)
    (controllers : ∀ (σ : Type) [Alphabet σ],
      PrefixController (packingFactor hF.c) σ) :
    (prefixTransform dyadicSelector F blank).rt_closed := by
  have hmarker : (Advice.middle_exp α).rt_closed := by
    let witness := middle_exp_two_stage_advice (α := α)
    rw [← witness.spec]
    exact two_stage_is_rt_closed witness.witness
  refine rtClosed_of_eventual_marked_simulators
    (prefixTransform dyadicSelector F blank)
    (Advice.middle_exp α) hmarker
    (2 * packingFactor hF.c)
    (fun σ _ π consumer =>
      Closure.simulator (hF.lift π) blank (controllers σ) consumer) ?_
  intro σ _ π consumer w hn
  rw [middle_exp_lift_eq π, prefixTransform_lift]
  rw [Closure.simulator_accepts_eq (hF.lift π)
    blank (controllers σ) consumer w hn]

end CellularAutomatas.MarkedPrefix.LT
