import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs
import CellularAutomatas.proofs.scan_lemmas

variable {α: Type u} [Alphabet α]
variable {Γ: Type u} [Alphabet Γ]


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
  theorem advice_two_stage_rt_closed (a: TwoStageAdvice α Γ):
      a.advice.rt_closed := by
    sorry

  theorem advice_two_stage_closed_under_composition {O': Type u} [Alphabet O'] (a1: TwoStageAdvice α O') (a2: TwoStageAdvice O' Γ):
      ∃ a: TwoStageAdvice α Γ, a.advice.f = a2.advice.f ∘ a1.advice.f := by
    sorry




  theorem advice_prefixes_in_L_rt_closed (C: CA_rt α):
      (Advice.prefixes_in_L C.val.L).rt_closed := by
    sorry

  theorem advice_exp_middle_rt_closed: (Advice.exp_middle α).rt_closed := by
    sorry

  -- For some c ∈ Γ, consider L_c = { w | adv(w)_|w| = c }. Since adv is rt_closed, we have L_c ∈ L(RT)!
  -- w[0..i+1] ∈ L_c <-> adv(w)_i = c (because adv is prefix-stable).
  -- Because advice_prefixes_in_L is rt_closed, we have adv = advice_prefixes_in_L(L_c1) + advice_prefixes_in_L(L_c2) + ...

  theorem prefix_stable_of_rt_closed (adv: Advice α Γ) (h1: adv.rt_closed) (h2: adv.prefix_stable) :
      adv.is_two_stage_advice := by
    sorry

  theorem exp_middle_two_stage_advice: (Advice.exp_middle α).is_two_stage_advice := by
    sorry


  -- peeking into the future! Speed up theorem for two-stage advices.
  theorem advice_shift_left_rt (extension: Word α) (adv: Advice α Γ) (h: adv.is_two_stage_advice):
      (Advice.shift_left extension adv).is_two_stage_advice := by
    sorry



  def rel_repr (adv: Advice α Γ) (p s: Word α) := (adv.f (p.append s))⟦0..p.length⟧


  lemma two_stage_rel_repr_eq (adv: TwoStageAdvice α Γ) (p s: Word α):
    rel_repr adv.advice p s =
      (adv.M.scanr_q
        (adv.C.scan_temporal p)
        (adv.M.scanr_reduce
          (adv.C.scan_temporal (p.append s))⟦p.length..*⟧
        )
      ).map adv.t
        := by
    dsimp [rel_repr, TwoStageAdvice.advice]
    rw [← List.map_take]
    congr 1
    let W := adv.C.scan_temporal (List.append p s)
    change (adv.M.scanr W).take p.length = _
    have h_split : W = W⟦0..p.length⟧ ++ W⟦p.length..*⟧ := (List.take_append_drop p.length W).symm
    conv in (adv.M.scanr W) => rw [h_split]
    have h_indep : W⟦0..p.length⟧ = adv.C.scan_temporal p := by
      simp [W]
      change (adv.C.scan_temporal (List.append p s)).take p.length = _
      erw [scan_temporal_independence (p := p) (s := s)]
    rw [h_indep]
    have h_len_p : (adv.C.scan_temporal p).length = p.length := by simp [LCellAutomaton.scan_temporal]
    conv => lhs; arg 1; rw [← h_len_p]
    erw [@scanr_append_take _ _ adv.M (adv.C.scan_temporal p) (W⟦p.length..*⟧)]
    simp [W]



  theorem middle_not_two_stage_advice : ¬ (Advice.middle α).is_two_stage_advice := by
    sorry


end advice_theorems
