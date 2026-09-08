import CellularAutomatas.proofs.advice_theory.marked_prefix.eventual_acceptance
import CellularAutomatas.proofs.advice_theory.marked_prefix.lifted_packets
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.lift
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.packing_budget
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.producer
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.readout
import CellularAutomatas.proofs.advice_theory.middle_exp_two_stage
import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage

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
  let L := dyadicSelector w.length
  let M := L / q
  letI : NeZero q := ⟨by
    have hlarge := packingFactor_large hF.c
    dsimp only [q]
    omega⟩

  have hq_large : hF.c + 2 ≤ q := by
    dsimp only [q]
    exact packingFactor_large hF.c
  have hq : 2 ≤ q := by omega
  have hn_two : 2 ≤ w.length := by
    have hq_pos : 0 < q := NeZero.pos q
    omega
  have hL_pos : 0 < L := by
    dsimp only [L]
    exact dyadicSelector_pos hn_two
  have hdiv : q ∣ L := by
    dsimp only [q, L]
    exact packingFactor_dvd hn
  have hlength : L = q * M := by
    dsimp only [M]
    exact (Nat.mul_div_cancel' hdiv).symm
  have hM : 0 < M := by
    dsimp only [M]
    apply Nat.div_pos
    · exact Nat.le_of_dvd hL_pos hdiv
    · exact NeZero.pos q

  obtain ⟨R, henvelope, hpackets⟩ :=
    Producer.exists_packets q hF blank controller
      dyadicSelector w M hM (by simpa only [L] using hlength)

  let controllerWord :=
    ReversalPackets.markedWord w (q * M - 1)
  let advisedWord :=
    (prefixTransform dyadicSelector F blank).annotate w
  have hcontroller_length : controllerWord.length = w.length := by
    simp only [controllerWord, ReversalPackets.markedWord_length]
  have hadvised_length : advisedWord.length = w.length := by
    simp only [advisedWord, Advice.annotate, List.length_zip,
      advice_len, min_self]
  have hcontroller_pos : 0 < controllerWord.length := by omega
  have hcatch :
      (q - 1 + hF.c) * M ≤
        (q - 1) * ((controllerWord.length - 1) / q + 1) := by
    have hbudget := packed_cost_le_catchup hF.c w.length hn
    simpa only [hcontroller_length] using hbudget

  have hfinal := consumerCA_trace_final q
    (Producer.C q hF blank controller) consumer.toCellAutomaton
    controllerWord advisedWord R controller.offset
    ((q - 1 + hF.c) * M)
    hq controller.offset_pos
    (by omega) (by omega)
    (by
      intro t p
      dsimp only [controllerWord, advisedWord]
      exact hpackets t p)
    henvelope hcatch

  have hmarked :
      (Advice.middle_exp α).annotate w = controllerWord := by
    rw [middle_exp_annotate_eq_mapIdx w hn_two]
    dsimp only [controllerWord, ReversalPackets.markedWord]
    rw [← hlength]

  change
    (consumerCA q (Producer.C q hF blank controller)
      consumer.toCellAutomaton controller.offset).trace
        (word_to_config ((Advice.middle_exp α).annotate w))
        (((Advice.middle_exp α).annotate w).length - 1) =
      consumer.toCellAutomaton.trace
        (word_to_config advisedWord) (advisedWord.length - 1)
  rw [hmarked]
  simpa only [hcontroller_length, hadvised_length] using hfinal

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
