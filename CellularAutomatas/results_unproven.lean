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
            a.advice.rt_closed := by
        sorry

    theorem advice_two_stage_closed_under_composition {A O' O: Alphabet} (a1: TwoStageAdvice A O') (a2: TwoStageAdvice O' O):
            ∃ a: TwoStageAdvice A O, a.advice.f = a2.advice.f ∘ a1.advice.f := by
        sorry





    theorem advice_prefixes_in_L_rt_closed [A: Alphabet] (C: CA_rt):
            (Advice.prefixes_in_L C.val.L).rt_closed := by
        sorry

    theorem advice_exp_middle_rt_closed [A: Alphabet]:
            (@Advice.exp_middle A).rt_closed := by
        sorry

    -- For some c ∈ Γ, consider L_c = { w | adv(w)_|w| = c }. Since adv is rt_closed, we have L_c ∈ L(RT)!
    -- w[0..i+1] ∈ L_c <-> adv(w)_i = c (because adv is prefix-stable).
    -- Because advice_prefixes_in_L is rt_closed, we have adv = advice_prefixes_in_L(L_c1) + advice_prefixes_in_L(L_c2) + ...

    theorem prefix_stable_of_rt_closed {A Γ: Alphabet} (adv: Advice A Γ) (h1: adv.rt_closed) (h2: adv.prefix_stable) :
            adv.is_two_stage_advice := by
        sorry

    theorem exp_middle_two_stage_advice :
            (@Advice.exp_middle 𝒰).is_two_stage_advice := by
        sorry


    -- peeking into the future! Speed up theorem for two-stage advices.
    theorem advice_shift_left_rt {A: Alphabet} (extension: Word) (adv: Advice A Γ) (h: adv.is_two_stage_advice):
            (Advice.shift_left extension adv).is_two_stage_advice := by
        sorry



    /-
        marking the middle is not a two stage advice.
        a two stage advice
        w := any word
        v := adv(w)

        w1 ~R w2 <=>

        wwww www
        vvvv vvv

    -/

end advice_theorems
