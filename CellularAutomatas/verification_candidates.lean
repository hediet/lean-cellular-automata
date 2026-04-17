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



-- TODO: Define tCellAutomaton.similar
-- theorem linear_time_dead_border (C: CA_lt α): ∃ C': tCellAutomaton α, C'.dead C'.border ∧ C'.similar C := by
--   sorry

-- TODO: rewrite for schema-parameterized types (CA α no longer exists as a set)
-- theorem const_speed_up: ℒ ({ C ∈ CA α | ∃ k, ∀ n, C.t n = n + k - 1 }) = ℒ (CA_rt α) := by
--   sorry

-- Moved to CellularAutomatas/proofs/rt_rev_implies_lt_eq_rt.lean
-- theorem ca_linear_time_eq_2n: ℒ (CA_lt α) = ℒ (CA_2n α)

theorem oca_linear_time_eq_2n: ℒ (OCA_lt α) = ℒ (OCA_2n α) := by
  sorry

theorem ocar_lt_eq_ca_rt: ℒ (OCAr_lt α) = ℒ (CA_rt α) := by
  sorry

-- TODO: rewrite for schema-parameterized types (CA α and CAr α no longer exist)
-- theorem ca_rt_equals_lt_of_closure_under_reversal: ℒ (CA α) = ℒ (CAr α) → ℒ (CA α) = ℒ (CA_lt α) := by
--   sorry


section advice_theorems

  def middle_exp_two_stage_advice: (Advice.middle_exp α).is_two_stage_advice := by
    sorry


  -- peeking into the future! Speed up theorem for two-stage advices.
  def advice_shift_left_rt (extension: Word α) (adv: Advice α Γ) (h: adv.is_two_stage_advice):
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
    Nonempty adv.is_two_stage_advice ↔
      Nonempty adv.weak_rt_closed ∧
      ∃ as: List { a: Advice α Γ // Nonempty a.weak_rt_closed ∧ a.causal },
        ∀ w, adv w ∈ { a.val w | a ∈ as } :=
    by

    sorry

end advice_theorems

/-!
## Language Class Equalities

These theorems relate the languages of various CA/OCA classes.
-/

/-- CA_2n and CA_lt recognize the same languages (linear-time speedup). -/
theorem ca_2n_eq_ca_lt : ℒ (CA_2n α) = ℒ (CA_lt α) := by
  sorry

/-- The CA_rt class equals the reverses of OCA_lt, OCA_2n, and the neg-2n OCA class.

    Proof sketch:
    - ℒ_rev(OCA_2n) = ℒ(CA_rt): mirroring an OCA_2n (left-independent, p=0, t=2(n-1))
      gives a right-independent CA reading from position n-1 at time 2(n-1),
      which by standard OCA-2n speedup equals CA_rt.
    - ℒ_rev(OCA_lt) = ℒ_rev(OCA_2n): follows from oca_linear_time_eq_2n.
    - ℒ(OCA_2n_neg2n) = ℒ_rev(OCA_2n): OCA_2n_neg2n natively reads from the
      left boundary (position -(n-1)) at time 2*(n-1); the computation cone
      covers -(n-1) to n-1, seeing the full word. This is equivalent to running
      OCA_2n on the reversed word. -/
theorem ca_rt_eq_rev_oca :
    ℒ (CA_rt α) = ℒ_rev (OCA_2n α) ∧
    ℒ_rev (OCA_2n α) = ℒ_rev (OCA_lt α) ∧
    ℒ_rev (OCA_lt α) = ℒ (OCA_2n_neg2n α) := by
  sorry

/-- The exp language { w | |w| = 2^n } lies in ℒ(CA_rt Unit) but not in ℒ(OCA_rt Unit).
    Hence ℒ(OCA_rt Unit) is a proper subset of ℒ(CA_rt Unit). -/
theorem oca_rt_proper_subset_ca_rt : ℒ (OCA_rt Unit) ⊂ ℒ (CA_rt Unit) := by
  sorry

/-!
## Unary Alphabet Results
-/

/-- Every language recognized by OCA_rt over the unary alphabet is regular.

    Proof idea: Over Unit, all words of the same length are identical, so any
    OCA_rt language is a set of lengths. A left-independent CA running for n-1
    steps on a width-1 input traces a finite automaton on the border symbol only.
    The resulting set of lengths is ultimately periodic, hence regular. -/
theorem oca_rt_unary_regular : ∀ L ∈ ℒ (OCA_rt Unit), L.IsRegular := by
  sorry

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
