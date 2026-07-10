import CellularAutomatas.proofs.constructions.even_two_sided_beta_boundary

/-!
# Half-runtime FSSP simulations on two-sided inputs

The moving-beta-boundary constructions provide two uniform automata:

* odd inputs `2 * k + 1` simulate a one-sided input of length `k + 1`;
* even inputs `2 * k` simulate a one-sided input of length `k`, delayed by one step.

This file combines those simulation invariants with one-sided FSSP correctness.
It deliberately states only the left-half result. A full two-sided solver still
needs mirrored tracks and a parity selector before their outputs can be combined.
-/

namespace CellularAutomatas

open CellAutomaton

/-- On an odd two-sided input, the corrected odd simulation fires throughout
    the left half exactly at time `2 * k = (2 * k + 1) - 1`. -/
theorem odd_two_sided_left_half_fires_iff
    (C : CellAutomaton Bool？ Bool) (hC : SolvesFSSPOptimal C)
    (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ)
    (hp_nn : 0 ≤ p) (hp_half : p < (k + 1 : ℤ)) :
    (OddTwoSidedBetaBoundary.ca C).comp
        ⟬fssp_both_sides (2 * k + 1)⟭ t p = true ↔
      t ≥ 2 * k := by
  by_cases hp_cone : p ≤ (t : ℤ)
  · rw [OddTwoSidedBetaBoundary.spec_comp C hC.quiescent_set k hk t p hp_cone]
    have h_fire := hC.fire_iff (k + 1) (by omega) t p (by
      rw [fssp_left_side_length]
      exact ⟨hp_nn, hp_half⟩)
    calc
      C.comp ⟬fssp_left_side (k + 1)⟭ t p = true ↔
          t ≥ 2 * (k + 1) - 2 := h_fire
      _ ↔ t ≥ 2 * k := by omega
  · rw [CellAutomaton.comp_apply]
    show C.project
        ((OddTwoSidedBetaBoundary.ca C).nextt
          ⟬fssp_both_sides (2 * k + 1)⟭ t p).2 = true ↔ t ≥ 2 * k
    rw [OddTwoSidedBetaBoundary.ca_nextt_eq C k hk t p]
    rw [OddTwoSidedBetaBoundary.q_inv C hC.quiescent_set k hk t p]
    unfold OddTwoSidedBetaBoundary.qShape
    rw [if_neg hp_cone]
    have hp_not_beta : ¬ (2 * (k : ℤ) - (t : ℤ) ≤ p) := by omega
    rw [if_neg hp_not_beta, hC.inner_false_projects_false]
    simp
    omega

/-- On an even two-sided input, the corrected delayed simulation fires
    throughout the left half exactly at time `2 * k - 1`. -/
theorem even_two_sided_left_half_fires_iff
    (C : CellAutomaton Bool？ Bool) (hC : SolvesFSSPOptimal C)
    (k : ℕ) (hk : k ≥ 2) (τ : ℕ) (p : ℤ)
    (hp_nn : 0 ≤ p) (hp_half : p < (k : ℤ)) :
    (EvenTwoSidedBetaBoundary.ca C).comp
        ⟬fssp_both_sides (2 * k)⟭ τ p = true ↔
      τ ≥ 2 * k - 1 := by
  rcases τ with _ | t
  · rw [CellAutomaton.comp_apply]
    show C.project
        ((EvenTwoSidedBetaBoundary.ca C).nextt
          ⟬fssp_both_sides (2 * k)⟭ 0 p).2 = true ↔ 0 ≥ 2 * k - 1
    rw [EvenTwoSidedBetaBoundary.ca_nextt_eq C k hk 0 p]
    rw [EvenTwoSidedBetaBoundary.q_inv C hC.quiescent_set k hk 0 p]
    rw [EvenTwoSidedBetaBoundary.qShape_zero_eq C k hk p]
    have hp_in : 0 ≤ p ∧ p < 2 * (k : ℤ) := by omega
    have hp_not_last : p ≠ 2 * (k : ℤ) - 1 := by omega
    rw [if_neg (by push_neg; exact ⟨hp_not_last, hp_in⟩)]
    rw [hC.inner_false_projects_false]
    simp
    omega
  · by_cases hp_cone : p ≤ (t : ℤ)
    · rw [EvenTwoSidedBetaBoundary.spec_comp C hC.quiescent_set k hk (t + 1) p
          (by omega) hp_nn (by omega) (by simpa using hp_cone)]
      have h_fire := hC.fire_iff k hk t p (by
        rw [fssp_left_side_length]
        exact ⟨hp_nn, hp_half⟩)
      calc
        C.comp ⟬fssp_left_side k⟭ t p = true ↔ t ≥ 2 * k - 2 := h_fire
        _ ↔ t + 1 ≥ 2 * k - 1 := by omega
    · rw [CellAutomaton.comp_apply]
      show C.project
          ((EvenTwoSidedBetaBoundary.ca C).nextt
            ⟬fssp_both_sides (2 * k)⟭ (t + 1) p).2 = true ↔
        t + 1 ≥ 2 * k - 1
      rw [EvenTwoSidedBetaBoundary.ca_nextt_eq C k hk (t + 1) p]
      rw [EvenTwoSidedBetaBoundary.q_inv C hC.quiescent_set k hk (t + 1) p]
      change C.project
          (if p ≤ (t : ℤ) then EvenTwoSidedBetaBoundary.originalQ C k t p
           else if 2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ p then C.border
           else C.inner false) = true ↔ t + 1 ≥ 2 * k - 1
      rw [if_neg hp_cone]
      have hp_not_beta : ¬ (2 * (k : ℤ) - 1 - ((t + 1 : ℕ) : ℤ) ≤ p) := by
        push_cast
        omega
      rw [if_neg hp_not_beta, hC.inner_false_projects_false]
      simp
      omega

/-- The checked core of the one-sided-to-two-sided speedup: two fixed
    parity-specific automata have the expected half-runtime behavior. -/
theorem two_sided_half_runtime_of_one_sided
    (C : CellAutomaton Bool？ Bool) (hC : SolvesFSSPOptimal C) :
    (OddTwoSidedBetaBoundary.ca C).quiescent_set
        { (OddTwoSidedBetaBoundary.ca C).border,
          (OddTwoSidedBetaBoundary.ca C).inner (false, false) } ∧
    (EvenTwoSidedBetaBoundary.ca C).quiescent_set
        { (EvenTwoSidedBetaBoundary.ca C).border,
          (EvenTwoSidedBetaBoundary.ca C).inner (false, false) } ∧
    (∀ (k : ℕ), k ≥ 1 → ∀ t p, 0 ≤ p → p < (k + 1 : ℤ) →
      ((OddTwoSidedBetaBoundary.ca C).comp
        ⟬fssp_both_sides (2 * k + 1)⟭ t p = true ↔ t ≥ 2 * k)) ∧
    (∀ (k : ℕ), k ≥ 2 → ∀ t p, 0 ≤ p → p < (k : ℤ) →
      ((EvenTwoSidedBetaBoundary.ca C).comp
        ⟬fssp_both_sides (2 * k)⟭ t p = true ↔ t ≥ 2 * k - 1)) := by
  refine ⟨OddTwoSidedBetaBoundary.spec_quiescent_set C hC.quiescent_set,
    EvenTwoSidedBetaBoundary.spec_quiescent_set C hC.quiescent_set, ?_, ?_⟩
  · intro k hk t p hp_nn hp_half
    exact odd_two_sided_left_half_fires_iff C hC k hk t p hp_nn hp_half
  · intro k hk t p hp_nn hp_half
    exact even_two_sided_left_half_fires_iff C hC k hk t p hp_nn hp_half

end CellularAutomatas