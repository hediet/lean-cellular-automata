import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs
import CellularAutomatas.proofs.advice_theory.finite_future_variation_iff_free_disclosure
import CellularAutomatas.proofs.advice_theory.natural_weak_rt_closed

namespace CellularAutomatas
variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]

-- open question: is every weak_rt_closed advice a two-stage advice?
def open_question_1 (adv: Advice α Γ) (h: adv.weak_rt_closed): adv.is_two_stage_advice := by
    sorry

/-!
## `open_question_1`, factored

The repository proves `weak_rt_closed + finite_rt_disclosure → two_stage`, and
`result_finite_future_variation_iff_finite_free_disclosure` proves
`finite_free_disclosure ↔ finite_future_variation`. So `open_question_1` is exactly the
conjunction of the two questions below, and nothing else remains:

1. does RT closure bound the future variation at all, and
2. can the resulting *free* probe be replaced by a real-time observable one?

Attacking these separately is strictly easier, because each is independently checkable.

**Known hardness.** `ca_rt_ne_ca_lt_of_weak_rt_closed_imp_finite_future_variation` shows that
even a positive answer to question 1 below implies `ℒ(CA_rt Unit) ≠ ℒ(CA_lt Unit)`.
So neither question can be settled affirmatively without separating real time from
linear time; only a refutation is plausibly unconditional.
-/

-- open question (combinatorial half): does weak RT closure bound the future variation?
-- Equivalently, by the characterization above: does it imply finite free disclosure?
def open_question_1a_weak_rt_closed_implies_finite_future_variation
    (adv: Advice α Γ) (_h: adv.weak_rt_closed): adv.finite_future_variation := by
    sorry

-- open question (observability half): can a free probe be upgraded to an RT probe?
-- The probe built by `finite_free_disclosure_of_finite_future_variation` discloses a
-- *counterfactual* table (which advice symbol a prefix would carry under other
-- continuations), which an advised real-time recognizer cannot observe. Whether some
-- *other* probe works is open.
def open_question_1b_upgrade_free_probe_to_rt
    (adv: Advice α Γ) (_h₁: adv.weak_rt_closed) (_h₂: adv.finite_future_variation):
    adv.finite_rt_disclosure := by
    sorry

/-!
## `open_question_1`, split along uniformity

A second, orthogonal factorization. `Advice.WeakRtClosed` is data, and every explicit
witness in this repository builds the eliminating automaton on top of `C`'s state space by
a recipe fixed in advance; only `Advice.WeakRtClosed.of_language_eq` — the choice-based
witness used for the `rt = lt` direction — does not. `Advice.NaturalWeakRtClosed` makes
that distinction precise, splitting `open_question_1` into `conjecture_U` below plus
"every weak RT closure witness can be made uniform", which is where the difficulty moves.

See `natural_weak_rt_closed.lean` for why the *naive* uniformity condition (naturality
with respect to CA homomorphisms alone) is vacuous, and why a state-space constraint is
needed.
-/

-- open question (uniform half): is every *uniformly* weakly RT-closed advice two-stage?
def conjecture_U_natural_weak_rt_closed_implies_two_stage
    (adv: Advice α Γ) (_h: adv.NaturalWeakRtClosed): adv.is_two_stage_advice := by
    sorry

-- open question (uniformization half): can every elimination construction be replaced by
-- one that is uniform in the state space?
def open_question_1_uniformize
    (adv: Advice α Γ) (_h: adv.weak_rt_closed): adv.NaturalWeakRtClosed := by
    sorry

theorem lt_eq_rt: CA_rt α = CA_lt α := by
    sorry

-- open question: is every rt-closed advice an lt-advice?
-- (Spatially, an rt-closed advice can be eliminated from any CA_rt; whether it
--  can additionally be *spatially* computed in linear time is open.)
def open_question_rt_closed_implies_lt_advice
    (adv: Advice α Γ) (_h: adv.rt_closed): adv.IsLtAdvice := by
    sorry

-- open question: rt-closed + lt-advice ⟹ two-stage?
-- (Showing rt-closed ⟹ two-stage is hard; the spatial-computability hypothesis
--  of `IsLtAdvice` may be enough to bridge the gap.)
def open_question_rt_closed_and_lt_advice_implies_two_stage
    (adv: Advice α Γ) (_h₁: adv.rt_closed) (_h₂: adv.IsLtAdvice):
    adv.is_two_stage_advice := by
    sorry
