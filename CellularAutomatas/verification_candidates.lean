import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs

namespace CellularAutomatas.verification_candidates

variable {α} [Alphabet α]
variable {Γ} [Alphabet Γ]



section advice_theorems
  -- peeking into the future! Speed up theorem for two-stage advices.
  def advice_shift_left_rt (extension: Word α) (adv: Advice α Γ) (h: adv.is_two_stage_advice):
      (adv.shift_left_advice extension).is_two_stage_advice := by
    sorry



/-
  theorem CartTraceAdvice_classification (adv: Advice α Γ) :
    adv.is_CartTraceAdvice ↔ adv.weak_rt_closed ∧ adv.causal :=
    by sorry
-/



  -- this is wrong!
  theorem CartTraceFstAdvice_classification (adv: Advice α Γ) :
    Nonempty adv.is_two_stage_advice ↔
      Nonempty adv.weak_rt_closed ∧
      ∃ as: List { a: Advice α Γ // Nonempty a.weak_rt_closed ∧ a.causal },
        ∀ w, adv w ∈ { a.val w | a ∈ as } :=
    by

    sorry

end advice_theorems

-- If the middle_exp advice is weak-LT-closed over the unary alphabet,
-- then CA_lt and CA_rt recognize the same unary languages.
--
-- Proof sketch: weak-LT-closure of middle_exp (marking the largest power-of-2
-- position ≤ n/2) allows simulating 2n-time CAs in linear time on unary input.
-- Combined with ℒ(CA_lt) ⊆ ℒ(CA_2n) ⊆ ℒ(CA_rt) (for unary), we get equality.
-- TODO: rewrite for schema-parameterized types (Advice.weak_lt_closed is currently commented out in defs.lean)
-- theorem middle_exp_weak_lt_closed_unary_implies_ca_lt_eq_ca_rt
--     (h : (Advice.middle_exp Unit).weak_lt_closed) :
--     ℒ (CA_lt Unit) = ℒ (CA_rt Unit) := by
--   sorry


/-

L is a CA LT language.
a1(w)_i = if i = 2^2j then w_i ∈ L else 0

advice a(w)_i :=
  if w.length is 2^(2n+1)
  then a1(w)_i
  else 0

Then a is probably weak_rt_closed?

-/
