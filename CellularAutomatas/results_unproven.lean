import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs

variable {A: Alphabet}


theorem exp_word_length_rt: ∃ C: @CA_rt 𝒰, C.val.L = { w | ∃ n, w.length = 2 ^ n } := by
    sorry

theorem linear_time_dead_border (C: CA_lt):
        ∃ C': tCellAutomaton, C'.dead C'.border ∧ C'.similar C := by
    sorry

theorem const_speed_up:
        ℒ ({ C ∈ CA | ∃ k, ∀ n, C.t n = n + k - 1 }) = ℒ (CA_rt) := by
    sorry

theorem ca_linear_time_eq_2n:
        ℒ CA_lt = ℒ CA_2n := by
    sorry

theorem oca_linear_time_eq_2n:
        ℒ OCA_lt = ℒ OCA_2n := by
    sorry

theorem ocar_lt_eq_ca_rt:
        ℒ OCAr_lt = ℒ CA_rt := by
    sorry

theorem ca_rt_equals_lt_of_closure_under_reversal:
        ℒ CA = ℒ CAr → ℒ CA = ℒ CA_lt := by
    sorry


section advice_theorems

    theorem advice_two_stage_rt_closed {A O: Alphabet} (a: TwoStageAdvice A O):
            rt_closed a.advice := by
        sorry

    theorem advice_two_stage_closed_under_composition {A O' O: Alphabet} (a1: TwoStageAdvice A O') (a2: TwoStageAdvice O' O):
            ∃ a: TwoStageAdvice A O, a.advice.f = a2.advice.f ∘ a1.advice.f := by
        sorry

    theorem advice_prefixes_in_L_rt_closed [A: Alphabet] (C: CA_rt):
            rt_closed (advice_prefixes_in_L C.val.L) := by
        sorry

end advice_theorems
