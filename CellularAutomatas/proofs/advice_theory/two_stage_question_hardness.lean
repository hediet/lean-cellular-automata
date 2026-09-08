import CellularAutomatas.proofs.advice_theory.middle_not_two_stage
import CellularAutomatas.proofs.advice_theory.middle_iff_compress2_weak_rt_closed
import CellularAutomatas.proofs.advice_theory.rt_eq_lt_iff_compress2_weak_rt_closed
import CellularAutomatas.proofs.advice_theory.marker_future_variation

/-!
# The two-stage question is at least as hard as `CA_rt ≠ CA_lt`

`open_question_1` asks whether every weakly RT-closed advice is two-stage, and
`open_question_1a` asks for the weaker conclusion that it merely has finite future
variation. This file shows that **even the weaker question `1a` cannot be answered
positively without separating real time from linear time.**

The argument composes three results that already live in the repository:

* `middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary` and
  `ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed` together say that over a unary
  input alphabet the middle marker is weakly RT-closed **iff** `ℒ(CA_rt) = ℒ(CA_lt)`.
* `Advice.middle_not_finite_future_variation` (from `marker_future_variation`) says that
  the middle marker has unbounded future variation.

So under `ℒ(CA_rt) = ℒ(CA_lt)` the middle marker is a *counterexample* to both
questions. Contrapositively, a positive answer forces `ℒ(CA_rt) ≠ ℒ(CA_lt)`.

This makes the status of the open question precise: it is not an oversight that
it is unproved, and any attempted proof must implicitly contain a real-time
lower bound. Conversely, only a *refutation* (an explicit weakly RT-closed advice
with unbounded future variation) is plausibly within reach unconditionally.
-/

namespace CellularAutomatas

open Classical

variable {α : Type} [Alphabet α]

/-! ## Conditional hardness of the open questions -/

/-- **A positive answer to `open_question_1a` separates real time from linear time.**

If every weakly RT-closed advice had finite future variation, then over the unary alphabet
`ℒ(CA_rt) = ℒ(CA_lt)` would be contradictory: that equality makes the middle marker
weakly RT-closed, yet the middle marker has unbounded future variation. -/
theorem ca_rt_ne_ca_lt_of_weak_rt_closed_imp_finite_future_variation
    (H : ∀ adv : Advice Unit Bool, adv.weak_rt_closed → adv.finite_future_variation) :
    ℒ (CA_rt Unit) ≠ ℒ (CA_lt Unit) := by
  intro heq
  -- `rt = lt` removes the width-two compression advice ...
  have hcompress : Nonempty (Advice.compress2 Unit).weak_rt_closed :=
    ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed.1 heq
  -- ... and hence, over a unary alphabet, the middle marker as well.
  have hmiddle : Nonempty (Advice.middle Unit).weak_rt_closed :=
    middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary.2 hcompress
  exact Advice.middle_not_finite_future_variation (H _ hmiddle.some)

/-- **A positive answer to `open_question_1` separates real time from linear time.**

Two-stage advice has finite RT disclosure, hence finite free disclosure, hence
finite future variation, so this reduces to the previous theorem. -/
theorem ca_rt_ne_ca_lt_of_weak_rt_closed_imp_two_stage
    (H : ∀ adv : Advice Unit Bool, adv.weak_rt_closed → adv.is_two_stage_advice) :
    ℒ (CA_rt Unit) ≠ ℒ (CA_lt Unit) :=
  ca_rt_ne_ca_lt_of_weak_rt_closed_imp_finite_future_variation fun adv hadv =>
    Advice.finite_future_variation_of_finite_free_disclosure
      (H adv hadv).finite_rt_disclosure.finite_free_disclosure

/-- Restated as a dichotomy: either real time is strictly weaker than linear time,
or the middle marker over a unary alphabet already refutes `open_question_1a`. -/
theorem ca_rt_ne_ca_lt_or_weak_rt_closed_without_finite_future_variation :
    ℒ (CA_rt Unit) ≠ ℒ (CA_lt Unit) ∨
      ∃ adv : Advice Unit Bool, Nonempty adv.weak_rt_closed ∧ ¬ adv.finite_future_variation := by
  by_cases heq : ℒ (CA_rt Unit) = ℒ (CA_lt Unit)
  · refine Or.inr ⟨Advice.middle Unit, ?_, Advice.middle_not_finite_future_variation⟩
    exact middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary.2
      (ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed.1 heq)
  · exact Or.inl heq

end CellularAutomatas
