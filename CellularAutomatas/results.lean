import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs
import CellularAutomatas.proofs.advice_theory.middle_not_two_stage
import CellularAutomatas.proofs.advice_theory.rt_closed.of_prefix_mem
import CellularAutomatas.proofs.advice_theory.is_two_stage_of_rt_closed_and_causal
import CellularAutomatas.proofs.constructions.left_indep_to_regular
import CellularAutomatas.proofs.constructions.left_indep_from_regular
import CellularAutomatas.proofs.constructions.speedup_left_independent
import CellularAutomatas.proofs.constructions.border_quiescent_left_independent
import CellularAutomatas.proofs.constructions.border_dead
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_cart
import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_two_stage
import CellularAutomatas.proofs.advice_theory.rt_closed.of_compose
import CellularAutomatas.proofs.constructions.basic_exp_word
import CellularAutomatas.proofs.rt_eq_2n_iff_rt_eq_rt_rev.rt_eq_2n_iff_rt_eq_rt_rev
import CellularAutomatas.proofs.language.dfa_to_left_indep_ca
import CellularAutomatas.proofs.language.oca_rt_proper_subset_ca_rt
import CellularAutomatas.proofs.language.oca_rt_unary_regular
import CellularAutomatas.proofs.constructions.linear_time_speedup
import CellularAutomatas.proofs.constructions.speedup_right_border_oca
import CellularAutomatas.proofs.language.oca_reversal_equivalences
import CellularAutomatas.proofs.advice_theory.middle_exp_two_stage
import CellularAutomatas.proofs.advice_theory.middle_iff_compress2_weak_rt_closed
import CellularAutomatas.proofs.advice_theory.rt_eq_lt_iff_compress2_weak_rt_closed

open CellularAutomatas

namespace CellularAutomatas.results

variable {α} [Alphabet α]
variable {Γ} [Alphabet Γ]

/-!
## Part I: Base Cellular Automata Results

These results establish equivalences and constructions for cellular automata
with various properties (left-independence, borders, speedups).
-/

section BaseResults

/-!
### Result 1: Left-Independent ↔ Regular CA Simulation

Given a left-independent CA C, there exists C' such that:
  Δ^t_{C'}(c)_i = Δ^{2t}_C(c)_{i-t}

And conversely, given any CA C, there exists a left-independent C' such that:
  Δ^{2t}_{C'}(c)_i = Δ^t_C(c)_{i+t}
-/

theorem result_left_indep_to_regular
    {β : Type} [Alphabet β] (C : CellAutomaton α β) (h_left_indep : C.left_independent)
    (c : Config α) (t : ℕ) (i : ℤ) :
    let e := LeftIndepToRegular.mk C h_left_indep
    e.C.comp c t i = C.comp c (2 * t) (i - t) := by
  intro e
  exact LeftIndepToRegular.spec e c t i
#print axioms result_left_indep_to_regular

theorem result_regular_to_left_indep
    {β : Type} [Alphabet β] (C : CellAutomaton α β)
    (c : Config α) (t : ℕ) (i : ℤ) :
    let e := RegularToLeftIndep.mk C
    e.C.comp c (2*t) i = .single (C.comp c t (i + t)) := by
  intro e
  exact RegularToLeftIndep.spec_even e c t i
#print axioms result_regular_to_left_indep

theorem result_regular_to_left_indep_is_left_indep
    {β : Type} [Alphabet β] (C : CellAutomaton α β) :
    (RegularToLeftIndep.mk C).C.left_independent :=
  RegularToLeftIndep.C_left_independent _
#print axioms result_regular_to_left_indep_is_left_indep

/-!
### Result 2: k-Step Left-Independent Speedup

Given a left-independent CA C and k ≥ 2, there exists a left-independent C' that
compresses k consecutive diagonal cells into one tuple.
-/

theorem result_left_indep_speedup
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (k : ℕ) (hk : k ≥ 2)
    (h_left_indep : C.left_independent)
    (w : Word α) (hw : w.length > 0) (t : ℕ) (i : ℤ)
    (hi2 : -(t : ℤ) ≤ i) (hi : i < 0) (j : Fin k) :
    let e := LeftIndepSpeedup.mk C k hk h_left_indep
    (e.C.comp w t i) j =
    C.comp w (t - ((k - 1) * i) - j).toNat (k * i + j) := by
  intro e
  exact LeftIndepSpeedup.spec e w hw t i hi2 hi j
#print axioms result_left_indep_speedup

/-!
### Result 3: Quiescent Border for Left-Independent CAs

Given a left-independent CA C, there exists C' whose border is quiescent
(δ(#, #, #) = #), while preserving the computation inside the left-independent
light cone.
-/

theorem result_quiescent_border_spec
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (h_left_indep : C.left_independent):
    let C' := (QuiescentBorderLeftIndep.mk C h_left_indep).C
    C'.quiescent C'.border
    ∧ C'.left_independent
    ∧ ∀ (w : Word α) (_hw : w.length > 0) (t : ℕ) (i : ℤ),
      C'.comp w t i =
        if i ∈ WordConeLeftIndep w t
        then C.comp w t i
        else C.project C.border :=
  ⟨QuiescentBorderLeftIndep.C_border_quiescent _,
   QuiescentBorderLeftIndep.C_left_indep _,
   fun w hw t i => QuiescentBorderLeftIndep.spec (QuiescentBorderLeftIndep.mk C h_left_indep) w hw t i⟩
#print axioms result_quiescent_border_spec

/-!
### Result 4: Dead Border Construction

Given any CA C, there exists C' whose border state is dead (absorbing),
while preserving the trace for all t < c * |w| for some constant c.
-/

theorem result_dead_border_spec
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (c_const : ℕ) :
    let C' := (DeadBorder.mk ⟨ c_const ⟩ C).C
    C'.dead C'.border
    ∧ ∀ (w : Word α) (t : ℕ) (_h : t < c_const * w.length),
      C'.trace w t = C.trace w t :=
  ⟨@DeadBorder.spec_left_border_dead { c := c_const, C_orig := C },
   fun _w _t h => @DeadBorder.spec_comp_trace { c := c_const, C_orig := C } _ _ h⟩
#print axioms result_dead_border_spec



theorem exp_word_length_rt: ∃ C: CA_rt Unit, C.L = { w | ∃ n, w.length = 2 ^ n } :=
  CellularAutomatas.exp_word_length_rt
#print axioms exp_word_length_rt

/-- **Strict separation: ℒ(OCA_rt α) ⊊ ℒ(CA_rt α).**

    For every alphabet `α`, one-way real-time CAs recognize strictly fewer
    languages than general real-time CAs.

    Witness: the powers-of-2-length language `{ w | ∃ k, |w| = 2^k }`, which
    lies in `ℒ(CA_rt α)` (lift of `exp_word_ca`) but not in `ℒ(OCA_rt α)`
    (its unary slice would have to be regular, yet `{2^k}` is not). -/
theorem oca_rt_proper_subset_ca_rt {α : Type} [Alphabet α] :
    ℒ (OCA_rt α) ⊂ ℒ (CA_rt α) :=
  CellularAutomatas.oca_rt_proper_subset_ca_rt
#print axioms oca_rt_proper_subset_ca_rt

/-!
### Result: ℒ(DFA) ⊆ ℒ(OCA_rt)

Every language recognized by a DFA is also recognized by a one-way (left-independent)
cellular automaton in real time.
-/

theorem result_dfa_subset_OCA_rt {σ : Type} [Fintype σ] [DecidableEq σ] [Inhabited σ]:
    ℒ (DFA α σ) ⊆ ℒ (OCA_rt α) :=
  dfa_subset_OCA_rt
#print axioms result_dfa_subset_OCA_rt

end BaseResults

/-!
## Part II: Advice Theory Results

These results develop a structural theory of advice for cellular automata,
establishing closure properties and characterizations.
-/

section AdviceResults

/-!
### Result 5: RT Transducers are Closed Under Composition

Given CA transducers C₁ : Σ → Γ₁ and C₂ : Γ₁ → Γ₂, there exists a CA C
such that trace_rt_C = trace_rt_{C₂} ∘ trace_rt_{C₁}.
-/

theorem result_rt_transducers_closed_under_composition
    {β γ : Type} [Alphabet β] [Alphabet γ]
    (C1 : CellAutomaton α？ β) (C2 : CellAutomaton β？ γ) :
    (C2.compose_trace_rt C1).trace_rt = C2.trace_rt ∘ C1.trace_rt :=
  CellAutomaton.compose_trace_rt_spec C2 C1
#print axioms result_rt_transducers_closed_under_composition

/-!
### Result 6: Two-Stage Advice is RT-Closed (Strong)

If f is two-stage, then for any Σ, ℒ(CA_rt((α×Σ) × Γ) / f^Σ) = ℒ(CA_rt(α×Σ)).
-/

def result_two_stage_is_rt_closed
    (adv : TwoStageAdvice α Γ) :
    adv.advice.rt_closed :=
  two_stage_is_rt_closed adv
#print axioms result_two_stage_is_rt_closed

/-!
### Result 7: Prefix-Membership Advice is Two-Stage (hence RT-Closed)

For any L ∈ ℒ(CA_rt), the advice f_L defined by f_L(w)_i = [w_{[0..i+1)} ∈ L]
is itself an RT transducer.
-/

def result_advice_prefix_mem_is_two_stage_advice:
    ∀ C : CA_rt α, Advice.is_two_stage_advice (Advice.prefix_mem C.L) := by
  exact advice_prefix_mem_is_two_stage_advice
#print axioms result_advice_prefix_mem_is_two_stage_advice

/-- The largest-power-of-two marker advice is computable in two stages. -/
def middle_exp_two_stage_advice :
    (Advice.middle_exp α).is_two_stage_advice :=
  CellularAutomatas.middle_exp_two_stage_advice
#print axioms middle_exp_two_stage_advice

/-!
### Result 8: Weak-RT-Closed ∧ Causal ⟹ CArt Advice (hence Two-Stage, hence RT-Closed)

If an advice f is both weak-RT-closed and causal, then f is a CArt advice,
i.e. computable by a single CA RT transducer. This implies two-stage.
-/

def result_is_cart_advice_of_rt_closed_and_causal:
    ∀ adv: Advice α Γ, adv.weak_rt_closed → adv.causal → adv.is_cart_advice := by
  exact is_cart_advice_of_rt_closed_and_causal
#print axioms result_is_cart_advice_of_rt_closed_and_causal


/-!
### Result 9: Two-Stage Advice is Closed Under Composition

Given two-stage advices f₁ : Σ* → Γ₁* and f₂ : Γ₁* → Γ₂*,
the composition f₂ ∘ f₁ is again two-stage.
-/

theorem result_two_stage_closed_under_composition
    {Γ' : Type} [Alphabet Γ']
    (a1 : TwoStageAdvice α Γ') (a2 : TwoStageAdvice Γ' Γ) :
    (compose_two_stage a2 a1: TwoStageAdvice α Γ).advice = a2.advice ∘ a1.advice :=
  compose_two_stage_spec a1 a2
#print axioms result_two_stage_closed_under_composition

/-!
### Result 10: Middle Advice is NOT Two-Stage

The advice f_mid that marks position ⌊n/2⌋ cannot be expressed as a two-stage advice.
-/

theorem result_middle_not_two_stage_advice:
    IsEmpty (Advice.middle α).is_two_stage_advice := by
  exact middle_not_two_stage_advice
#print axioms result_middle_not_two_stage_advice

/-!
### Result 11: RT-Closed Advices are Closed Under Composition

Given f₁ : Advice α Γ₁ (rt_closed) and f₂ : Advice Γ₁ Γ₂ (rt_closed),
the composition f₁.compose f₂ is rt_closed.
-/

noncomputable def result_rt_closed_compose_rt_closed
    {Γ' : Type} [Alphabet Γ']
    (f₁: Advice α Γ') (f₂: Advice Γ' Γ)
    (h₁: f₁.rt_closed) (h₂: f₂.rt_closed):
    (f₁.compose f₂).rt_closed :=
  Advice.rt_closed_compose_rt_closed f₁ f₂ h₁ h₂

/-- Over a unary alphabet, the middle and width-two compression advices have
    equivalent weak real-time closure behavior. -/
theorem middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary :
    Nonempty (Advice.middle Unit).weak_rt_closed ↔
    Nonempty (Advice.compress2 Unit).weak_rt_closed :=
  CellularAutomatas.middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary
#print axioms middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary

/-- Real time equals linear time exactly when width-two compression advice can
    be eliminated from real-time recognizers. -/
theorem ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed :
    ℒ (CA_rt α) = ℒ (CA_lt α) ↔
    Nonempty (Advice.compress2 α).weak_rt_closed :=
  CellularAutomatas.ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed
#print axioms ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed

/-- Unary specialization through the middle-marking advice. -/
theorem ca_rt_eq_ca_lt_unary_iff_middle_weak_rt_closed :
    ℒ (CA_rt Unit) = ℒ (CA_lt Unit) ↔
    Nonempty (Advice.middle Unit).weak_rt_closed := by
  calc
    ℒ (CA_rt Unit) = ℒ (CA_lt Unit)
        ↔ Nonempty (Advice.compress2 Unit).weak_rt_closed :=
          ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed
    _ ↔ Nonempty (Advice.middle Unit).weak_rt_closed :=
      middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary.symm
#print axioms ca_rt_eq_ca_lt_unary_iff_middle_weak_rt_closed

end AdviceResults

/-!
## Part III: Reproductions of Prior Results

Mechanized reproductions of previously published results about real-time
cellular automata.
-/

section RTEquivalence

/-- Linear-time speedup: two-way CAs need no more than `2(n-1)` time. -/
theorem ca_2n_eq_ca_lt : ℒ (CA_2n α) = ℒ (CA_lt α) :=
  CellularAutomatas.ca_2n_eq_ca_lt
#print axioms ca_2n_eq_ca_lt

/-- Linear-time speedup for one-way CAs: every linear-time OCA language is
    recognized by an OCA in time `2(n-1)`. -/
theorem oca_linear_time_eq_2n : ℒ (OCA_lt α) = ℒ (OCA_2n α) :=
  (CellularAutomatas.OCA_2n_eq_OCA_lt α).symm
#print axioms oca_linear_time_eq_2n

/-- A `2(n-1)`-time OCA is equivalent to a right-reading real-time CA. -/
theorem oca_2n_eq_car_rt : ℒ (OCA_2n α) = ℒ (CAr_rt α) :=
  CellularAutomatas.oca_2n_eq_car_rt
#print axioms oca_2n_eq_car_rt

/-- A `2(n-1)`-time OCA observed at `-(n-1)` is equivalent to a real-time CA. -/
theorem oca_2n_left_neg_np1_eq_ca_rt :
    ℒ (OCA_2n_left_neg_np1 α) = ℒ (CA_rt α) :=
  CellularAutomatas.oca_2n_left_neg_np1_eq_ca_rt
#print axioms oca_2n_left_neg_np1_eq_ca_rt

/-- Reversing linear-time OCA languages gives exactly the languages of
    right-reading linear-time right-independent CAs. -/
theorem oca_lt_rev_eq_ocar_lt : ℒ_rev (OCA_lt α) = ℒ (OCAr_lt α) :=
  CellularAutomatas.oca_lt_rev_eq_ocar_lt
#print axioms oca_lt_rev_eq_ocar_lt

/-- Right-reading right-independent linear-time CAs recognize exactly the
    real-time CA languages. -/
theorem ocar_lt_eq_ca_rt : ℒ (OCAr_lt α) = ℒ (CA_rt α) :=
  CellularAutomatas.ocar_lt_eq_ca_rt
#print axioms ocar_lt_eq_ca_rt

/-- Real-time CA languages are equivalently reversed `2(n-1)`-time or
  linear-time OCA languages, or `2(n-1)`-time OCA languages observed at
  `-(n-1)`. -/
theorem ca_rt_eq_rev_oca :
    ℒ (CA_rt α) = ℒ_rev (OCA_2n α) ∧
    ℒ_rev (OCA_2n α) = ℒ_rev (OCA_lt α) ∧
  ℒ_rev (OCA_lt α) = ℒ (OCA_2n_left_neg_np1 α) :=
  CellularAutomatas.ca_rt_eq_rev_oca
#print axioms ca_rt_eq_rev_oca

/-- Every unary real-time one-way CA language is regular. -/
theorem oca_rt_unary_regular : ∀ L ∈ ℒ (OCA_rt Unit), L.IsRegular :=
  CellularAutomatas.oca_rt_unary_regular
#print axioms oca_rt_unary_regular

/-!
### Result 12 (Ibarra & Jiang 1988): ℒ(CA_rt) = ℒ(CA_lt) ⟺ ℒ(CA_rt) = ℒᴿ(CA_rt)

Two open questions about real-time cellular automata are equivalent:
- (A) Real-time = linear-time for all alphabets
- (B) Real-time languages are closed under reversal for all alphabets

Note: The (⇐) direction requires reversal closure over all alphabets (including
Option β) because the proof lifts words to Option β for padding.
-/

theorem result_rt_eq_lt_iff_rt_eq_rt_rev :
    (∀ (β : Type) [Alphabet β], ℒ (CA_rt β) = ℒ (CA_lt β)) ↔
    (∀ (γ : Type) [Alphabet γ], ℒ (CA_rt γ) = ℒ_rev (CA_rt γ)) := by
  simp [← ca_2n_eq_ca_lt, rt_eq_2n_iff_rt_eq_rt_rev]
#print axioms result_rt_eq_lt_iff_rt_eq_rt_rev

end RTEquivalence
