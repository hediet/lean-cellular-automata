/-
  # DFA to Left-Independent Cellular Automaton

  This file proves that every DFA language is recognized by a left-independent
  real-time cellular automaton.

  Main result:
  - `dfa_language_in_OCA_rt`: For any DFA M, M.accepts ∈ ℒ(OCA_rt α)

  ## Construction Overview

  Given a DFA M with states σ, transition `step`, initial state `start`, and accepting `accept`:

  We construct a left-independent CA where:
  - State Q = Option (σ × α) where:
    - `none` = quiescent/border state
    - `some (q, a)` = accumulated DFA state q with original symbol a
  - embed(none) = none (border)
  - embed(some a) = some (step start a, a)  -- immediately apply first transition
  - δ(_, center, right) = transition that propagates DFA computation left-to-right:
    - δ(_, none, _) = none  -- border stays quiescent
    - δ(_, some (q, a), none) = some (q, a)  -- preserve at right border
    - δ(_, some (q_c, a_c), some (q_r, a_r)) = some (step q_c a_r, a_r)
      -- take center's DFA state, step on right's symbol, propagate right's symbol

  Key insight: In a left-independent CA, cell 0 at time t depends on cells 0..t at time 0.
  After n-1 steps for input of length n, cell 0 has accumulated the full DFA computation.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [DecidableEq α] [Alphabet α]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ## Construction of CA from DFA -/

/-- The state space for our CA: Option (DFA state × original symbol).
    - none = border/quiescent
    - some (q, a) = accumulated DFA state q with symbol a preserved -/
abbrev DFAtoCA.Q (σ α : Type) := Option (σ × α)

/-- Transition function: left-independent by construction (ignores first argument).
    Propagates DFA computation from left to right. -/
def DFAtoCA.δ (M : DFA α σ) : DFAtoCA.Q σ α → DFAtoCA.Q σ α → DFAtoCA.Q σ α → DFAtoCA.Q σ α :=
  fun _ center right =>
    match center, right with
    | none, _ => none  -- border stays quiescent
    | some (q, a), none => some (q, a)  -- preserve at right border
    | some (q_c, _), some (_, a_r) => some (M.step q_c a_r, a_r)  -- propagate DFA computation

/-- Embed input: none ↦ none, some a ↦ some (step start a, a) -/
def DFAtoCA.embed (M : DFA α σ) : Option α → DFAtoCA.Q σ α :=
  fun input =>
    match input with
    | none => none
    | some a => some (M.step M.start a, a)

/-- Project to Bool: accept iff in accepting state.
    For `none` (border/empty word), check if start state is accepting. -/
def DFAtoCA.project (M : DFA α σ) [DecidablePred (· ∈ M.accept)] : DFAtoCA.Q σ α → Bool :=
  fun q =>
    match q with
    | none => M.start ∈ M.accept
    | some (s, _) => s ∈ M.accept

/-- The cellular automaton constructed from a DFA -/
def DFAtoCA (M : DFA α σ) [DecidablePred (· ∈ M.accept)] [Fintype α] [Inhabited σ] [Inhabited α] :
    CellAutomaton (Option α) Bool where
  Q := DFAtoCA.Q σ α
  δ := DFAtoCA.δ M
  embed := DFAtoCA.embed M
  project := DFAtoCA.project M

/-! ## Left-Independence Proof -/

omit [DecidableEq α] [Alphabet α] [Fintype σ] [DecidableEq σ] in
/-- The transition function is left-independent: it ignores the left argument. -/
theorem DFAtoCA.δ_left_independent (M : DFA α σ) :
    ∀ q1 q2 q3 q1', DFAtoCA.δ M q1 q2 q3 = DFAtoCA.δ M q1' q2 q3 := by
  intros q1 q2 q3 q1'
  unfold DFAtoCA.δ
  -- The definition doesn't use q1 or q1', so they're definitionally equal
  rfl

omit [Alphabet α] in
/-- The CA is left-independent. -/
theorem DFAtoCA_left_independent (M : DFA α σ) [DecidablePred (· ∈ M.accept)] [Fintype α]
    [Inhabited σ] [Inhabited α] :
    (DFAtoCA M).left_independent := by
  unfold CellAutomaton.left_independent
  exact DFAtoCA.δ_left_independent M

/-! ## Correctness: nextt computes DFA evaluation -/

omit [Alphabet α] in
/-- General specification: Position p at time t holds state for w[p..p+t]. -/
theorem DFAtoCA.nextt_spec_general (M : DFA α σ) (w : List α) (t : ℕ) (p : ℤ)
    (hp : p ≥ 0) (hpt : p.toNat + t < w.length)
    [DecidablePred (· ∈ M.accept)] [Fintype α] [Inhabited σ] [Inhabited α] :
    (DFAtoCA M).nextt ⦋⟬w⟭⦌ t p =
      some (M.evalFrom M.start (w.drop p.toNat |>.take (t + 1)), w[p.toNat + t]) := by
  induction t generalizing p with
  | zero =>
    -- Base case: nextt at time 0 = embed_config = embed(w[p])
    simp only [CellAutomaton.nextt_zero, Nat.add_zero]
    simp only [CellAutomaton.embed_config, word_to_config]
    have hp_range : (0 ≤ p ∧ p < w.length) := ⟨hp, by omega⟩
    simp only [hp_range, and_self, ↓reduceDIte, DFAtoCA, DFAtoCA.embed]
    -- evalFrom start (w.drop p |>.take 1) = evalFrom start [w[p]] = step start w[p]
    have h_take1 : (w.drop p.toNat).take 1 = [w[p.toNat]] := by
      rw [List.take_one]
      simp only [List.drop_eq_getElem_cons (by omega : p.toNat < w.length), List.head?_cons,
        Option.toList_some]
    rw [h_take1]
    simp only [DFA.evalFrom, List.foldl_cons, List.foldl_nil]
  | succ t ih =>
    -- Inductive case: nextt (t+1) p = δ(nextt t (p-1), nextt t p, nextt t (p+1))
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    have hp_lt : p.toNat + t < w.length := by omega
    have ih_p := ih p hp hp_lt
    have hp1 : (p + 1) ≥ 0 := by omega
    have hp1_nat : (p + 1).toNat = p.toNat + 1 := Int.toNat_add_nat hp 1
    have hp1_lt : (p + 1).toNat + t < w.length := by rw [hp1_nat]; omega
    have ih_p1 := ih (p + 1) hp1 hp1_lt
    -- Rewrite ih_p1 with the nat conversion
    have h_bound1 : p.toNat + 1 + t < w.length := by omega
    have ih_p1' : (DFAtoCA M).nextt ⦋⟬w⟭⦌ t (p + 1) =
        some (M.evalFrom M.start (w.drop (p.toNat + 1) |>.take (t + 1)),
              w[p.toNat + 1 + t]'h_bound1) := by
      simp only [hp1_nat] at ih_p1
      convert ih_p1 using 3
    rw [ih_p, ih_p1']
    simp only [DFAtoCA, DFAtoCA.δ]
    -- Goal: (step (evalFrom ... take(t+1)) w[p+1+t], w[p+1+t]) =
    --       some (evalFrom ... take(t+2), w[p+(t+1)])
    have h_bound2 : p.toNat + t + 1 < w.length := by omega
    have h_idx1 : p.toNat + 1 + t = p.toNat + t + 1 := by omega
    have h_idx2 : p.toNat + (t + 1) = p.toNat + t + 1 := by omega
    have h_take : (w.drop p.toNat).take (t + 2) =
                  (w.drop p.toNat).take (t + 1) ++ [w[p.toNat + t + 1]'h_bound2] := by
      rw [List.take_add_one]
      have h_len : t + 1 < (w.drop p.toNat).length := by simp; omega
      simp only [List.getElem?_eq_getElem h_len, Option.toList_some, List.getElem_drop, h_idx2]
    simp only [h_take, DFA.evalFrom_append_singleton, h_idx1, h_idx2]

omit [Alphabet α] in
/-- At time n-1, position 0 has the full DFA evaluation. -/
theorem DFAtoCA.nextt_full (M : DFA α σ) (w : List α) (hw : w.length > 0)
    [DecidablePred (· ∈ M.accept)] [Fintype α] [Inhabited σ] [Inhabited α] :
    (DFAtoCA M).nextt ⦋⟬w⟭⦌ (w.length - 1) 0 = some (M.eval w, w[w.length - 1]) := by
  have := DFAtoCA.nextt_spec_general M w (w.length - 1) 0 (by omega) (by simp; omega)
  simp only [Int.toNat_zero, List.drop_zero, Nat.zero_add, Nat.sub_add_cancel hw,
    List.take_length] at this
  exact this

/-- The CA accepts w iff the DFA accepts w. -/
theorem DFAtoCA.accepts_iff (M : DFA α σ) (w : List α)
    [DecidablePred (· ∈ M.accept)] [Fintype α] [Inhabited σ] [Inhabited α] :
    (toRtCa (DFAtoCA M)).accepts w ↔ w ∈ M.accepts := by
  by_cases hw : w.length > 0
  · -- Non-empty word: cell 0 at time n-1 has full DFA evaluation
    simp only [tCellAutomaton.accepts, toRtCa, AcceptanceSchema.rt_left,
      CellAutomaton.comp_apply, CellAutomaton.project_config_apply,
      Function.comp_apply]
    rw [DFAtoCA.nextt_full M w hw]
    simp only [DFAtoCA, DFAtoCA.project, decide_eq_true_eq, DFA.mem_accepts]
  · -- Empty word: both sides reduce to M.start ∈ M.accept
    simp only [Nat.not_lt, Nat.le_zero] at hw
    have hw_nil : w = [] := List.eq_nil_of_length_eq_zero hw
    subst hw_nil
    simp only [tCellAutomaton.accepts, toRtCa, AcceptanceSchema.rt_left,
      List.length_nil, Nat.zero_sub,
      CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply,
      CellAutomaton.nextt_zero, CellAutomaton.embed_config, word_to_config,
      le_refl, DFAtoCA, DFAtoCA.embed, DFAtoCA.project,
      and_false, Int.ofNat_zero, lt_self_iff_false, ↓reduceDIte,
      decide_eq_true_eq, DFA.mem_accepts, DFA.eval_nil]

/-! ## DefinesLanguage instance for DFA -/

instance : DefinesLanguage (DFA α σ) α where
  L := DFA.accepts

/-! ## Main Result -/

/-- Every DFA language is in ℒ(OCA_rt α). -/
lemma dfa_language_in_OCA_rt (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] [Fintype α] [Inhabited σ] [Inhabited α] :
    M.accepts ∈ ℒ (OCA_rt α) := by
  unfold ℒ
  -- OCA_rt α = { C : CA_rt α // C.left_independent }
  refine ⟨⟨toRtCa (DFAtoCA M), DFAtoCA_left_independent M⟩, ?_⟩
  ext w
  simp only [DefinesLanguage.L, tCellAutomaton.L]
  exact (DFAtoCA.accepts_iff M w).symm

/-- ℒ(DFA) ⊆ ℒ(OCA_rt): every DFA language is recognized by an OCA in real time. -/
theorem dfa_subset_OCA_rt [Fintype α] [Inhabited α] [Inhabited σ] :
    ℒ (DFA α σ) ⊆ ℒ (OCA_rt α) := by
  intro L ⟨M, hM⟩
  classical
  rw [hM]
  exact dfa_language_in_OCA_rt M

end CellularAutomatas
