/-
  # rt-advice / lt-advice: spatial CA-computed advice

  Builds on `Advice.IsRtAdvice` / `Advice.IsLtAdvice` defined in `defs.lean`.

  Main statements:

  * `cart_with_rt_advice_subset_ca_2n_minus_1` (sorry): the genuine
      combinatorial content. Uses FSSP + the marker advice
      `Advice.fssp_input` to fire every interior cell at `t = n` (one step
      over rt because the marker advice needs a 1-step initial broadcast),
      then runs the cart for `n − 1` more steps.

  * `cart_with_rt_advice_subset_ca_2n` (proved):
      Composes the above with the constant 1-step speedup
      `ca_2n_minus_1_subset_ca_2n` (`SpBDk 3 1`).

  * `ca_2n_subset_cart_with_compress2` (proved):
      `ℒ(CA_2n) ⊆ ℒ(CA_rt + compress2)` — fully proved using the existing
      `Compress2Sim` simulator.

  * `compress2_is_rt_advice` (sorry): `Advice.compress2 α` is an rt-advice.

  * `rt_advice_ne_lt_advice_of_cart_ne_calt` (sorry):
      If `ℒ(CA_rt α) ≠ ℒ(CA_lt α)`, then there is an lt-advice that is not
      an rt-advice.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.ca_rt_utils
import CellularAutomatas.proofs.fssp
import CellularAutomatas.proofs.constructions.speedup_k_step
import CellularAutomatas.proofs.advice_theory.rt_eq_lt_iff_compress2_weak_rt_closed

namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

open CellAutomaton

/-! ## Auxiliary CA class: `CA_(2n − 1)` -/

/-- Acceptance schema reading at time `2n − 1` (with `ℕ`-saturating subtraction
    for `n = 0`), centre position. -/
def time_2n_minus_1_schema : AcceptanceSchema :=
  ⟨fun n => 2 * n - 1, fun _ => 0⟩

/-- CA class reading at time `2n − 1`, centre position. -/
abbrev CA_2n_minus_1 (α : Type) [Alphabet α] := tCellAutomaton time_2n_minus_1_schema α

/-! ## `ℒ(CA_(2n−1)) ⊆ ℒ(CA_2n)` via 1-step constant speedup

    For `n ≥ 1`, `SpBDk 3 1` makes the trace at time `2(n − 1)` coincide with
    the original trace at time `2(n − 1) + 1 = 2n − 1`. For `n = 0` both
    schemas read at time `0` and the proof reduces to definitional unfolding
    of `SpBDk` on the all-border configuration. -/
lemma ca_2n_minus_1_subset_ca_2n : ℒ (CA_2n_minus_1 α) ⊆ ℒ (CA_2n α) := by
  intro L ⟨C, hC_L⟩
  -- Witness: the original CA wrapped through `SpBDk 3 1`.
  let C' : CA_2n α := { toCellAutomaton := SpBDk 3 1 C.toCellAutomaton }
  refine ⟨C', ?_⟩
  subst hC_L; ext w
  show w ∈ tCellAutomaton.L C ↔ w ∈ tCellAutomaton.L C'
  rw [tCellAutomaton.elem_L_iff (C := C), tCellAutomaton.elem_L_iff (C := C')]
  show C.toCellAutomaton.comp ⦋⟬w⟭⦌ (2 * w.length - 1) 0 = true ↔
    (SpBDk 3 1 C.toCellAutomaton).comp ⦋⟬w⟭⦌ (2 * (w.length - 1)) 0 = true
  by_cases hn : w.length ≥ 1
  · -- n ≥ 1: SpBDk 3 1 gives the +1 speedup directly.
    have h_speed := SpBDk_trace_eq 3 1 C.toCellAutomaton w (2 * (w.length - 1))
                      (by omega) (by omega)
    -- `SpBDk_trace_eq` is stated about `trace`; unfold to `comp`.
    simp only [CellAutomaton.trace] at h_speed
    have h_time : 2 * (w.length - 1) + 1 = 2 * w.length - 1 := by omega
    rw [h_time] at h_speed
    rw [h_speed]
  · -- n = 0: empty word, both schemas read at time 0.
    push_neg at hn
    have hw0 : w.length = 0 := by omega
    have hw : w = [] := List.eq_nil_of_length_eq_zero hw0
    subst hw
    -- After substitution both sides read at time 0, position 0 on the
    -- all-border configuration. Same idea as `ca_2n_proper_subset_ca_2n`.
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_sub]
    simp only [CellAutomaton.comp_apply, CellAutomaton.nextt_zero, CellAutomaton.embed_config]
    simp only [SpBDk, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
               SpBD, SpB, CellAutomaton.map_project, withDeadBorder, DeadBorder.C,
               Sp, CellAutomaton.border]
    rfl

/-! ## Theorem A (inner): `ℒ(CA_rt + rt-advice) ⊆ ℒ(CA_(2n−1))`

    The "real" theorem — contains the FSSP + advice + cart construction.
    Proof idea (state space `A.Q × M.Q × F.Q × Option C.Q`, 4 layered
    inductions, see project documentation for the full plan).

    * Phase 1 (`t ∈ [0, n]`, synchronisation):
      - `A.Q` runs the rt-advice CA and produces `(adv w)[i]` at every cell
        at time `n − 1`;
      - `M.Q` runs the marker CA (`fssp_input_is_const_time_1`), latching
        `is_first_or_last(i)` at every cell from `t = 1` onward;
      - `F.Q` runs the FSSP solver, seeded from `M.Q` at `t = 1`. Two-sided
        FSSP then fires every interior cell at `t = 1 + (n − 1) = n`.

    * Phase 2 (`t ∈ [n, 2n − 1]`, cart simulation): at the firing tick
      `t = n`, every interior cell reseeds its `Option C.Q` slot to
      `some (C.embed (some (w[i], (adv w)[i])))`. Then `C.δ` runs for `n − 1`
      more steps. Output read at `t = 2n − 1`, position `0`. -/
def cart_with_rt_advice_subset_ca_2n_minus_1
    (adv : Advice α Γ) (h : adv.IsRtAdvice) :
    ℒ (CA_rt (α × Γ) + adv) ⊆ ℒ (CA_2n_minus_1 α) := by
  -- Once available, the exposed `cart_with_rt_advice_subset_ca_2n` below
  -- becomes sorry-free.
  sorry

/-! ## Theorem A: `ℒ(CA_rt + rt-advice) ⊆ ℒ(CA_2n)` (composition) -/

theorem cart_with_rt_advice_subset_ca_2n
    (adv : Advice α Γ) (h : adv.IsRtAdvice) :
    ℒ (CA_rt (α × Γ) + adv) ⊆ ℒ (CA_2n α) :=
  fun _L hL =>
    ca_2n_minus_1_subset_ca_2n
      (cart_with_rt_advice_subset_ca_2n_minus_1 adv h hL)


/-! ## Theorem B: `ℒ(CA_2n α) ⊆ ℒ(CA_rt + compress2)`

    Concrete instance of `ℒ(CA_kn) ⊆ ℒ(cart + compressk-advice)` for `k = 2`.
    The simulator `Compress2Sim.simRtCA` already exists; this theorem simply
    packages its correctness into a language-class inclusion. -/
theorem ca_2n_subset_cart_with_compress2 :
    ℒ (CA_2n α) ⊆ ℒ (CA_rt (α × (Option α × Option α)) + Advice.compress2 α) := by
  intro L hL
  obtain ⟨C₀, hL⟩ := hL
  let C₂ : CA_rt (α × (Option α × Option α)) := Compress2Sim.simRtCA C₀
  have h_eq : { w | C₂.accepts ((Advice.compress2 α).annotate w) } = C₀.L := by
    ext w
    show C₂.accepts ((Advice.compress2 α).annotate w) = true ↔ _
    rw [Compress2Sim.simRtCA_accepts_iff]
    rfl
  show L ∈ ℒ (CA_rt (α × (Option α × Option α)) + Advice.compress2 α)
  rw [hL]
  exact ⟨⟨C₂⟩, h_eq.symm⟩


/-! ## Theorem C: `Advice.compress2 α` is an rt-advice -/

def compress2_is_rt_advice :
    (Advice.compress2 α).IsRtAdvice := by
  sorry


/-! ## Combined: `ℒ(CA_2n α) ⊆ ℒ(cart + rt-advice)` -/

theorem ca_2n_subset_some_cart_with_rt_advice :
    ∃ Γ : Type, ∃ _ : Alphabet Γ, ∃ adv : Advice α Γ,
      Nonempty adv.IsRtAdvice ∧
        ℒ (CA_2n α) ⊆ ℒ (CA_rt (α × Γ) + adv) :=
  ⟨_, _, Advice.compress2 α, ⟨compress2_is_rt_advice⟩, ca_2n_subset_cart_with_compress2⟩


/-! ## Theorem D: `ℒ(CArt) ≠ ℒ(CAlt) ⟹ rt-advice ≠ lt-advice` -/

theorem rt_advice_ne_lt_advice_of_cart_ne_calt
    (h : ℒ (CA_rt α) ≠ ℒ (CA_lt α)) :
    ∃ adv : Advice α Bool, Nonempty adv.IsLtAdvice ∧ IsEmpty adv.IsRtAdvice := by
  sorry


/-! ## Trivial direction: `rt-advice ⟹ lt-advice` -/

def rt_advice_implies_lt_advice
    {adv : Advice α Γ} (h : adv.IsRtAdvice) : adv.IsLtAdvice :=
  h.toLtAdvice

end CellularAutomatas
