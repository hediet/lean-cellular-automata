import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs
import CellularAutomatas.proofs.middle_not_two_stage
import CellularAutomatas.proofs.advice_prefix_mem_rt_closed
import CellularAutomatas.proofs.is_two_stage_of_rt_closed_and_causal
import CellularAutomatas.proofs.left_indep_to_regular
import CellularAutomatas.proofs.regular_to_left_indep
import CellularAutomatas.proofs.left_indep_speedup
import CellularAutomatas.proofs.passive_border
import CellularAutomatas.proofs.dead_border
import CellularAutomatas.proofs.composition
import CellularAutomatas.proofs.two_stage_is_rt_closed
import CellularAutomatas.proofs.advice_two_stage_closed_under_composition

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

theorem result_regular_to_left_indep
    {β : Type} [Alphabet β] (C : CellAutomaton α β)
    (c : Config α) (t : ℕ) (i : ℤ) :
    let e := RegularToLeftIndep.mk C
    e.C.comp c (2*t) i = .single (C.comp c t (i + t)) := by
  intro e
  exact RegularToLeftIndep.spec_even e c t i

theorem result_regular_to_left_indep_is_left_indep
    {β : Type} [Alphabet β] (C : CellAutomaton α β) :
    (RegularToLeftIndep.mk C).C.left_independent :=
  RegularToLeftIndep.C_left_independent _

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
    (e.C.comp (CellAutomaton.embed_word w) t i) j =
    C.comp (CellAutomaton.embed_word w) (t - ((k - 1) * i) - j).toNat (k * i + j) := by
  intro e
  exact LeftIndepSpeedup.spec e w hw t i hi2 hi j

/-!
### Result 3: Passive Border for Left-Independent CAs

Given a left-independent CA C, there exists C' whose border is quiescent
(δ(#, #, #) = #), while preserving the computation inside the left-independent
light cone.
-/

theorem result_passive_border_left_indep
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (h_left_indep : C.left_independent)
    (w : Word α) (hw : w.length > 0) (t : ℕ) (i : ℤ) :
    let e := PassiveBorderLeftIndep.mk C h_left_indep
    e.C.comp w t i =
      if i ∈ WordConeLeftIndep w t
      then C.comp w t i
      else C.project C.border := by
  intro e
  exact PassiveBorderLeftIndep.spec e w hw t i

theorem result_passive_border_left_indep_is_quiescent
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (h_left_indep : C.left_independent) :
    let e := PassiveBorderLeftIndep.mk C h_left_indep
    e.C.quiescent e.C.border :=
  PassiveBorderLeftIndep.C_border_passive _

theorem result_passive_border_left_indep_preserves_left_indep
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (h_left_indep : C.left_independent) :
    (PassiveBorderLeftIndep.mk C h_left_indep).C.left_independent :=
  PassiveBorderLeftIndep.C_left_indep _

/-!
### Result 4: Dead Border Construction

Given any CA C, there exists C' whose border state is dead (absorbing),
while preserving the trace for all t < c * |w| for some constant c.
-/

theorem result_dead_border
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (c_const : ℕ)
    (w : Word α) (t : ℕ) (h : t < c_const * w.length) :
    let e : DeadBorder := { c := c_const, C_orig := C }
    e.C.trace w t = C.trace w t := by
  intro e
  exact @DeadBorder.spec_comp_trace e w t h

theorem result_dead_border_is_dead
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (c_const : ℕ) :
    let e : DeadBorder := { c := c_const, C_orig := C }
    e.C.dead e.C.border := by
  intro e
  exact @DeadBorder.spec_left_border_dead e

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
    (C1 : CArtTransducer α β) (C2 : CArtTransducer β γ) :
    (C2.compose C1).trace_rt = C2.trace_rt ∘ C1.trace_rt :=
  CArtTransducer.compose_spec C2 C1

/-!
### Result 6: Two-Stage Advice is RT-Closed

If f is two-stage, then ℒ(CA_rt(Σ × Γ) / f) = ℒ(CA_rt(Σ)).
-/

theorem result_two_stage_is_rt_closed
    (adv : TwoStageAdvice α Γ) :
    adv.advice.rt_closed :=
  two_stage_rt_closed adv

/-!
### Result 7: Prefix-Membership Advice is Two-Stage (hence RT-Closed)

For any L ∈ ℒ(CA_rt), the advice f_L defined by f_L(w)_i = [w_{[0..i+1)} ∈ L]
is itself an RT transducer.
-/

theorem result_advice_prefix_mem_is_two_stage_advice:
    ∀ C ∈ CA_rt α, Advice.is_two_stage_advice (Advice.prefix_mem C.L) := by
  intro C h
  exact advice_prefix_mem_is_two_stage_advice ⟨ C, h ⟩

/-!
### Result 8: RT-Closed ∧ Prefix-Stable ⟹ Two-Stage (hence RT Transducer)

If an advice f is both RT-closed and prefix-stable, then f is two-stage.
-/

theorem result_is_two_stage_of_rt_closed_and_causal:
    ∀ adv: Advice α Γ, adv.rt_closed ∧ adv.causal → adv.is_two_stage_advice := by
  intro adv h
  exact is_two_stage_of_rt_closed_and_causal adv h.1 h.2

/-!
### Result 9: Two-Stage Advice is Closed Under Composition

Given two-stage advices f₁ : Σ* → Γ₁* and f₂ : Γ₁* → Γ₂*,
the composition f₂ ∘ f₁ is again two-stage.
-/

theorem result_two_stage_closed_under_composition
    {Γ' : Type} [Alphabet Γ']
    (a1 : TwoStageAdvice α Γ') (a2 : TwoStageAdvice Γ' Γ) :
    (compose_two_stage a2 a1).advice.f = a2.advice.f ∘ a1.advice.f :=
  advice_two_stage_closed_under_composition a1 a2

/-!
### Result 10: Middle Advice is NOT Two-Stage

The advice f_mid that marks position ⌊n/2⌋ cannot be expressed as a two-stage advice.
-/

theorem result_middle_not_two_stage_advice:
    ¬ Advice.is_two_stage_advice (Advice.middle α) := by
  exact middle_not_two_stage_advice

end AdviceResults
