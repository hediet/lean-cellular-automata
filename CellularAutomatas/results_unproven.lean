import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs

namespace CellularAutomatas.results_unproven

variable {α} [Alphabet α]
variable {Γ} [Alphabet Γ]



-- TODO: Define tCellAutomaton.similar
-- theorem linear_time_dead_border (C: CA_lt α): ∃ C': tCellAutomaton α, C'.dead C'.border ∧ C'.similar C := by
--   sorry

theorem const_speed_up: ℒ ({ C ∈ CA α | ∃ k, ∀ n, C.t n = n + k - 1 }) = ℒ (CA_rt α) := by
  sorry

-- Moved to CellularAutomatas/proofs/rt_rev_implies_lt_eq_rt.lean
-- theorem ca_linear_time_eq_2n: ℒ (CA_lt α) = ℒ (CA_2n α)

theorem oca_linear_time_eq_2n: ℒ (OCA_lt α) = ℒ (OCA_2n α) := by
  sorry

theorem ocar_lt_eq_ca_rt: ℒ (OCAr_lt α) = ℒ (CA_rt α) := by
  sorry

theorem ca_rt_equals_lt_of_closure_under_reversal: ℒ (CA α) = ℒ (CAr α) → ℒ (CA α) = ℒ (CA_lt α) := by
  sorry


section advice_theorems

  theorem exp_middle_two_stage_advice: (Advice.exp_middle α).is_two_stage_advice := by
    sorry


  -- peeking into the future! Speed up theorem for two-stage advices.
  theorem advice_shift_left_rt (extension: Word α) (adv: Advice α Γ) (h: adv.is_two_stage_advice):
      (adv.shift_left_advice extension).is_two_stage_advice := by
    sorry



/-
  theorem CartTraceAdvice_classification (adv: Advice α Γ) :
    adv.is_CartTraceAdvice ↔ adv.weak_rt_closed ∧ adv.causal :=
    by sorry
-/

  instance : CoeFun (Advice α Γ) (fun _ => Word α → Word Γ) where
    coe a := a.f


  theorem CartTraceFstAdvice_classification (adv: Advice α Γ) :
    adv.is_two_stage_advice ↔
      adv.weak_rt_closed ∧
      ∃ as: List { a: Advice α Γ // a.weak_rt_closed ∧ a.causal },
        ∀ w, adv w ∈ { a.val w | a ∈ as } :=
    by

    sorry

end advice_theorems

/-

L is a CA LT language.
a1(w)_i = if i = 2^2j then w_i ∈ L else 0

advice a(w)_i :=
  if w.length is 2^(2n+1)
  then a1(w)_i
  else 0

Then a is probably weak_rt_closed?

-/
