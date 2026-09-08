import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.async_transform
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.prefix_controller
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.producer_handoff

namespace CellularAutomatas.MarkedPrefix.LT.Producer

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- The complete producer runs the LT transformation on the asynchronously
initialized finite strip and supplies annotated packets over the full half-line. -/
def C (q : ℕ) [NeZero q] {F : Advice α Γ} (hF : F.IsLtAdvice)
    (blank : Γ) (controller : PrefixController q α) :
    CellAutomaton (Option (α × Bool)) (Option (Fin q → Option (α × Γ))) :=
  ProducerHandoff.C controller.classified
    (AsyncTransform.events q hF controller.initializer) blank

theorem controller_spec (q : ℕ) [NeZero q] {F : Advice α Γ}
    (hF : F.IsLtAdvice) (controller : PrefixController q α)
    (w : Word α) (M : ℕ) (hM : 0 < M) (hbound : q * M ≤ w.length) :
    (AsyncTransform.driven q hF controller.initializer).ControllerSpec M
      (word_to_config (ReversalPackets.markedWord w (q * M - 1)))
      (fun p => controller.offset + (q - 1) * p)
      (fun p => SpeedupKx.compress q (word_to_config (w.take (q * M))) p) := by
  constructor
  · intro t p hp
    change (controller.initializer.comp
      (ReversalPackets.markedWord w (q * M - 1)) t p).2 = _
    rw [controller.packets_spec w M hM hbound]
    simp only [hp, true_and, AsyncHalfLine.packet]
  · intro t p hp ht
    exact controller.boundaries_spec w M hM hbound t p hp ht

/-- Actual finite-state prefix events have the required linear physical
budget. The first-event times are witnesses in the proof, not runtime oracles. -/
theorem exists_prefix_events (q : ℕ) [NeZero q] {F : Advice α Γ}
    (hF : F.IsLtAdvice) (blank : Γ) (controller : PrefixController q α)
    (selector : BoundedSelector) (w : Word α) (M : ℕ) (hM : 0 < M)
    (hlength : selector w.length = q * M) :
    ∃ τ : ℕ → ℕ,
      (∀ p, p < M → τ p ≤ controller.offset + (q - 1 + hF.c) * M) ∧
      ∀ t p : ℕ,
        (AsyncTransform.events q hF controller.initializer).comp
            (ReversalPackets.markedWord w (q * M - 1)) t p =
          if p < M ∧ t = τ p then
            some (ProducerHandoff.prefixBlock selector F blank w p)
          else none := by
  classical
  have hbound : q * M ≤ w.length := by
    rw [← hlength]
    exact selector.bound w.length
  have hprefix : (w.take (q * M)).length = q * M := by
    simp only [List.length_take, Nat.min_eq_left hbound]
  have hrelease : ∀ p, p < M →
      controller.offset + (q - 1) * p ≤ controller.offset + (q - 1) * M := by
    intro p hp
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hp.le) _
  have hdeadline : controller.offset + (q - 1) * M + hF.c * M =
      controller.offset + (q - 1 + hF.c) * M := by ring
  have hinside : ∀ p, p < M → ∃ τ,
      τ ≤ controller.offset + (q - 1 + hF.c) * M ∧
        ∀ t, (AsyncTransform.events q hF controller.initializer).comp
            (ReversalPackets.markedWord w (q * M - 1)) t p =
          if t = τ then
            some (ProducerHandoff.prefixBlock selector F blank w p)
          else none := by
    intro p hp
    obtain ⟨τ, _, hupper, hevent⟩ :=
      AsyncTransform.exists_event_at q hF blank controller.initializer
        (word_to_config (ReversalPackets.markedWord w (q * M - 1)))
        (w.take (q * M)) M hM hprefix
        (fun p => controller.offset + (q - 1) * p)
        (controller.offset + (q - 1) * M)
        (controller_spec q hF controller w M hM hbound) hrelease p hp
    refine ⟨τ, by simpa only [hdeadline] using hupper, ?_⟩
    intro t
    have hblock : PackedTransform.block q F blank (w.take (q * M)) p =
        ProducerHandoff.prefixBlock selector F blank w p := by
      funext i
      change (word_to_config (F (w.take (q * M)))
        ((p : ℤ) * q + (i : ℤ))).getD blank =
          (word_to_config (F (w.take (selector w.length)))
            ((p : ℤ) * q + (i : ℤ))).getD blank
      rw [hlength]
    simpa only [hblock] using hevent t
  let τ : ℕ → ℕ := fun p =>
    if hp : p < M then Classical.choose (hinside p hp) else 0
  refine ⟨τ, ?_, ?_⟩
  · intro p hp
    simpa only [τ, dif_pos hp] using (Classical.choose_spec (hinside p hp)).1
  · intro t p
    by_cases hp : p < M
    · simpa only [hp, true_and, τ, dif_pos hp] using
        (Classical.choose_spec (hinside p hp)).2 t
    · have hnone : ∀ s,
          (controller.initializer.comp
            (ReversalPackets.markedWord w (q * M - 1)) s p).2 = none := by
        intro s
        rw [controller.packets_spec w M hM hbound]
        simp only [hp, false_and, if_false]
      have houtput :
          (AsyncTransform.driven q hF controller.initializer).C.comp
            (ReversalPackets.markedWord w (q * M - 1)) t p = none := by
        exact (AsyncTransform.driven q hF controller.initializer).comp_of_no_packets
          (word_to_config (ReversalPackets.markedWord w (q * M - 1))) p hnone t
      have hevent := FirstOutput.comp_none
        (AsyncTransform.driven q hF controller.initializer).C
        (word_to_config (ReversalPackets.markedWord w (q * M - 1))) t p houtput
      simpa only [AsyncTransform.events, hp, false_and, if_false] using hevent

/-- The full producer now satisfies both the consumer's exact packet contents
and its affine release envelope. Only the online controller remains a parameter. -/
theorem exists_packets (q : ℕ) [NeZero q] {F : Advice α Γ}
    (hF : F.IsLtAdvice) (blank : Γ) (controller : PrefixController q α)
    (selector : BoundedSelector) (w : Word α) (M : ℕ) (hM : 0 < M)
    (hlength : selector w.length = q * M) :
    ∃ R : ℕ → ℕ,
      (∀ p, controller.offset + (q - 1) * p ≤ R p ∧
        R p ≤ controller.offset + max ((q - 1) * p) ((q - 1 + hF.c) * M)) ∧
      ∀ t p : ℕ,
        (C q hF blank controller).comp
            (ReversalPackets.markedWord w (q * M - 1)) t p =
          if t = R p then
            some (SpeedupKx.compress q
              (word_to_config ((prefixTransform selector F blank).annotate w)) p)
          else none := by
  obtain ⟨τ, htime, hevents⟩ :=
    exists_prefix_events q hF blank controller selector w M hM hlength
  refine ⟨ProducerHandoff.release controller.offset q M τ, ?_, ?_⟩
  · exact ProducerHandoff.release_bounds controller.offset q M
      ((q - 1 + hF.c) * M) τ htime
  · intro t p
    apply ProducerHandoff.comp_prefix_spec controller.classified
      (AsyncTransform.events q hF controller.initializer) blank
      (word_to_config (ReversalPackets.markedWord w (q * M - 1)))
      selector F w controller.offset M τ hlength
    · intro s r
      exact controller.classified_spec w M hM
        (by rw [← hlength]; exact selector.bound w.length) s r
    · exact hevents

end CellularAutomatas.MarkedPrefix.LT.Producer
