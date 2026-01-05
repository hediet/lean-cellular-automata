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


theorem exp_word_length_rt: ∃ C: CA_rt Unit, C.val.L = { w | ∃ n, w.length = 2 ^ n } := by
  sorry



theorem linear_time_dead_border (C: CA_lt α): ∃ C': tCellAutomaton α, C'.dead C'.border ∧ C'.similar C := by
  sorry

theorem const_speed_up: ℒ ({ C ∈ CA α | ∃ k, ∀ n, C.t n = n + k - 1 }) = ℒ (CA_rt α) := by
  sorry

theorem ca_linear_time_eq_2n: ℒ (CA_lt α) = ℒ (CA_2n α) := by
  sorry

theorem oca_linear_time_eq_2n: ℒ (OCA_lt α) = ℒ (OCA_2n α) := by
  sorry

theorem ocar_lt_eq_ca_rt: ℒ (OCAr_lt α) = ℒ (CA_rt α) := by
  sorry

theorem ca_rt_equals_lt_of_closure_under_reversal: ℒ (CA α) = ℒ (CAr α) → ℒ (CA α) = ℒ (CA_lt α) := by
  sorry


section advice_theorems

  theorem advice_two_stage_closed_under_composition {O'} [Alphabet O'] (a1: TwoStageAdvice α O') (a2: TwoStageAdvice O' Γ):
      ∃ a: TwoStageAdvice α Γ, a.advice.f = a2.advice.f ∘ a1.advice.f := by
    sorry




  theorem advice_prefix_mem_rt_closed (C: CA_rt α):
      (Advice.prefix_mem C.val.L).rt_closed := by
    sorry

  theorem advice_exp_middle_rt_closed: (Advice.exp_middle α).rt_closed := by
    sorry

  -- For some c ∈ Γ, consider L_c = { w | adv(w)_|w| = c }. Since adv is rt_closed, we have L_c ∈ L(RT)!
  -- w[0..i+1] ∈ L_c <-> adv(w)_i = c (because adv is prefix-stable).
  -- Because advice_prefix_mem is rt_closed, we have adv = advice_prefix_mem(L_c1) + advice_prefix_mem(L_c2) + ...

  theorem prefix_stable_of_rt_closed (adv: Advice α Γ) (h1: adv.rt_closed) (h2: adv.prefix_stable) :
      adv.is_two_stage_advice := by
    sorry

  theorem exp_middle_two_stage_advice: (Advice.exp_middle α).is_two_stage_advice := by
    sorry


  -- peeking into the future! Speed up theorem for two-stage advices.
  theorem advice_shift_left_rt (extension: Word α) (adv: Advice α Γ) (h: adv.is_two_stage_advice):
      (adv.shift_left_advice extension).is_two_stage_advice := by
    sorry

end advice_theorems
