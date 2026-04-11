/-
  QuiescentBorderLeftIndep: Converting a left-independent CA to one with quiescent border

  Given a left-independent CA C, we construct C' where:
  - The border is quiescent (δ(border, border, border) = border)
  - Left-independence is preserved
  - The computation inside the word cone matches the original

  Key insight from thesis (Satz "Wahl eines quiescentn und initialen Randes"):
  For left-independent CAs, we only look at the tracked border from the MIDDLE
  and RIGHT neighbors (not left). This preserves left-independence.

  Reference: docs/bachelor-thesis/chapters/2.Grundlagen.tex, lines 403-471
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.border

namespace CellularAutomatas

open CellAutomaton

/-! ## Iterated border transition

  When the border is not quiescent, it evolves over time as δ(#, #, #).
  We define δδt to track this evolution.
-/

/-- Iterate the border transition t times: δδt q t = δ(q, q, q) applied t times -/
def δδt {α β : Type} (C : CellAutomaton α β) (q : C.Q) : ℕ → C.Q
  | 0 => q
  | t + 1 => C.δ (δδt C q t) (δδt C q t) (δδt C q t)

@[simp]
lemma δδt_zero {α β : Type} (C : CellAutomaton α β) (q : C.Q) : δδt C q 0 = q := rfl

@[simp]
lemma δδt_succ {α β : Type} (C : CellAutomaton α β) (q : C.Q) (t : ℕ) :
    δδt C q (t + 1) = C.δ (δδt C q t) (δδt C q t) (δδt C q t) := rfl

/-- If q is quiescent, then δδt q t = q for all t -/
lemma δδt_quiescent {α β : Type} (C : CellAutomaton α β) (q : C.Q) (h : C.quiescent q) (t : ℕ) :
    δδt C q t = q := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [δδt_succ, ih]
    exact h ⟨q, rfl⟩ ⟨q, rfl⟩ ⟨q, rfl⟩

/-! ## Word cone for left-independent CAs

  For left-independent CAs, information only flows leftward (cell i depends on cells i and i+1).
  So the cone expands to the LEFT (negative direction). The right boundary stays fixed at w.length.

  At t=0: positions 0..w.length-1
  At t=1: positions -1..w.length-1 (can also include -1 due to border info)
  etc.
-/

/-- The word cone at time t for left-independent CAs.
    At t=0, this is positions 0..w.length-1. The cone expands only leftward. -/
def WordConeLeftIndep {α : Type} (w : Word α) (t : ℕ) : Set ℤ :=
  { i : ℤ | (-t : ℤ) ≤ i ∧ i < w.length }

instance {α : Type} (w : Word α) (t : ℕ) (i : ℤ) : Decidable (i ∈ WordConeLeftIndep w t) := by
  unfold WordConeLeftIndep
  infer_instance

@[simp]
lemma WordConeLeftIndep_zero {α : Type} (w : Word α) : WordConeLeftIndep w 0 = w.range := by
  ext i
  simp only [WordConeLeftIndep, Word.range, ge_iff_le, Set.mem_setOf_eq,
    Nat.cast_zero, neg_zero]

/-- Position i is in cone at t iff -t ≤ i < w.length -/
lemma WordConeLeftIndep_mem {α : Type} (w : Word α) (t : ℕ) (i : ℤ) :
    i ∈ WordConeLeftIndep w t ↔ (-t : ℤ) ≤ i ∧ i < w.length := by
  simp only [WordConeLeftIndep, Set.mem_setOf_eq]

/-! ## QuiescentBorderLeftIndep construction

  Given a left-independent CA C, we construct C' with:
  - Q' = border | state(s, tracked_border)
  - δ'(_, border, border) = border  (quiescent!)
  - δ' ignores the left neighbor's tracked border (preserving left-independence)

  The tracked border evolves as δδt C.border t.
-/

structure QuiescentBorderLeftIndep where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β
  h_left_indep : C_orig.left_independent

attribute [instance] QuiescentBorderLeftIndep._inst_α
attribute [instance] QuiescentBorderLeftIndep._inst_β

namespace QuiescentBorderLeftIndep

variable (e : QuiescentBorderLeftIndep)

/-- State space for C': either the quiescent border, or a state paired with the tracked border value -/
inductive Q'
  | border : Q'
  | state (s : e.C_orig.Q) (tracked_border : e.C_orig.Q) : Q'
  deriving DecidableEq

instance : Inhabited (Q' e) := ⟨Q'.border⟩

instance : Fintype (Q' e) :=
  Fintype.ofEquiv (Unit ⊕ (e.C_orig.Q × e.C_orig.Q))
    { toFun := fun
        | .inl () => Q'.border
        | .inr (s, br) => Q'.state s br
      invFun := fun
        | Q'.border => .inl ()
        | Q'.state s br => .inr (s, br)
      left_inv := fun x => by cases x with | inl u => cases u; rfl | inr p => rfl
      right_inv := fun x => by cases x <;> rfl }

/-- Unwrap a Q' to get the underlying state, using the tracked border if it's the border state -/
def unwrap : Q' e → e.C_orig.Q → e.C_orig.Q
  | .border, fallback => fallback
  | .state s _, _ => s

/-- Extract the tracked border from a Q' state -/
def get_tracked_border : Q' e → Option e.C_orig.Q
  | .border => none
  | .state _ br => some br

/-- Transition function for C'.
    The border is quiescent.

    Key insight from thesis: to preserve left-independence, we only look at the
    tracked border from the MIDDLE and RIGHT neighbors (not left).

    The rule is: if {b_br, c_br} \ {⊥} = {x} for exactly one x, use x.
    Otherwise, return border.
-/
def δ' : Q' e → Q' e → Q' e → Q' e
  | a, .state b br, .state c br' =>
      -- Both middle and right have tracked border - they must agree
      if br = br' then
        let a' := e.unwrap a br
        .state (e.C_orig.δ a' b c) (e.C_orig.δ br br br)
      else
        .border  -- Conflict - shouldn't happen in valid computation
  | a, .state b br, .border =>
      -- Only middle has tracked border, use it
      let a' := e.unwrap a br
      .state (e.C_orig.δ a' b br) (e.C_orig.δ br br br)
  | a, .border, .state c br =>
      -- Only right has tracked border, use it
      let a' := e.unwrap a br
      .state (e.C_orig.δ a' br c) (e.C_orig.δ br br br)
  | _, .border, .border =>
      -- Neither middle nor right has tracked border → quiescent border
      .border

/-- Project Q' to the original output type -/
def project' : Q' e → e.β
  | .border => e.C_orig.project e.C_orig.border
  | .state s _ => e.C_orig.project s

/-- The CA with quiescent border -/
def C : CellAutomaton e.α？ e.β := {
  Q := Q' e
  δ := e.δ'
  embed := fun a => match a with
    | some a' => .state (e.C_orig.embed (some a')) e.C_orig.border
    | none => .border
  project := e.project'
}

/-- The border of C is quiescent -/
lemma C_border_quiescent : e.C.quiescent e.C.border := by
  unfold CellAutomaton.quiescent CellAutomaton.quiescent_set CellAutomaton.border C
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  simp only [Set.mem_singleton_iff] at ha hb hc
  subst ha hb hc
  rfl

/-- The border of C is the border constructor -/
@[simp]
lemma C_border_eq : e.C.border = Q'.border := rfl

/-- C is left-independent -/
lemma C_left_indep : e.C.left_independent := by
  intro q1 q2 q3 q1'
  unfold C δ'
  -- The transition function doesn't depend on q1's tracked border
  cases q2 <;> cases q3
  · -- border, border → border (doesn't depend on q1)
    rfl
  · -- border, state c br → uses br, unwrap q1 br
    rename_i c br
    cases q1 <;> cases q1'
    · rfl
    · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
    · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
    · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
  · -- state b br, border → uses br, unwrap q1 br
    rename_i b br
    cases q1 <;> cases q1'
    · rfl
    · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
    · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
    · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
  · -- state b br, state c br' → uses br/br', unwrap q1 br
    rename_i b br c br'
    simp only
    split_ifs with h
    · cases q1 <;> cases q1'
      · rfl
      · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
      · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
      · simp only [unwrap]; congr 1; exact e.h_left_indep _ _ _ _
    · rfl

/-! ## δ' step lemmas

  These lemmas reduce the case explosion in spec_internal by capturing the
  common pattern: after applying the IH, each neighbor is either
  Q'.state s (δδt t) or Q'.border, and δ' produces the correct result.
-/

/-- When middle is .state b br, δ' produces the correct one-step transition
    regardless of whether left/right are .state or .border.
    The original left value a_orig is arbitrary (by left-independence). -/
private lemma δ'_mid_state (a_val : Q' e) (a_orig b : e.C_orig.Q) (br : e.C_orig.Q)
    (c_val : Q' e) (c_orig : e.C_orig.Q)
    (hc : c_val = Q'.state c_orig br ∨ (c_val = Q'.border ∧ c_orig = br)) :
    e.δ' a_val (.state b br) c_val =
    Q'.state (e.C_orig.δ a_orig b c_orig) (e.C_orig.δ br br br) := by
  rcases hc with rfl | ⟨rfl, rfl⟩
  · simp only [δ', ↓reduceIte, unwrap]
    congr 1; exact e.h_left_indep _ _ _ _
  · simp only [δ', unwrap]
    congr 1; exact e.h_left_indep _ _ _ _

/-- When middle and left are .border but right is .state c br,
    δ' produces .state (orig.δ br br c) (orig.δ br br br).
    Used at the left edge of the cone. -/
private lemma δ'_left_edge (c : e.C_orig.Q) (br : e.C_orig.Q) (a_orig : e.C_orig.Q) :
    e.δ' Q'.border Q'.border (.state c br) =
    Q'.state (e.C_orig.δ a_orig br c) (e.C_orig.δ br br br) := by
  simp only [δ', unwrap]
  congr 1; exact e.h_left_indep _ _ _ _

/-! ## Main specification

  The main theorem: C.comp gives the same result as C_orig.comp inside the cone,
  and border outside the cone.
-/

/-- Helper: embed_word matches for positions in the word range -/
private lemma embed_config_in_range (w : Word e.α) (i : ℤ) (hi : i ∈ w.range) :
    CellAutomaton.embed_config (C := e.C) (word_to_config w) i =
    Q'.state (CellAutomaton.embed_config (C := e.C_orig) (word_to_config w) i) e.C_orig.border := by
  simp only [Word.range, ge_iff_le, Set.mem_setOf_eq] at hi
  simp only [CellAutomaton.embed_config, word_to_config, C, hi]
  rfl

/-- Helper: embed_config is border outside the word range -/
private lemma embed_config_out_range (w : Word e.α) (i : ℤ) (hi : i ∉ w.range) :
    CellAutomaton.embed_config (C := e.C) (word_to_config w) i = Q'.border := by
  simp only [Word.range, ge_iff_le, Set.mem_setOf_eq, not_and, not_lt] at hi
  simp only [CellAutomaton.embed_config, word_to_config, C]
  split_ifs with h
  · exfalso; exact (hi h.1).not_gt h.2
  · rfl

/-- Helper: border stays for positions ≥ w.length using left-independence -/
lemma border_stays_right (w : Word e.α) (i : ℤ) (hi : i ≥ w.length) (t : ℕ) :
    e.C.nextt w t i = Q'.border := by
  exact CellAutomaton.border_stays_right e.C e.C_left_indep e.C_border_quiescent w i hi t

/-- For positions left of the cone, the original CA computes as δδt of the border -/
private lemma orig_left_of_cone (w : Word e.α) (t : ℕ) (i : ℤ) (hi : i < -(t : ℤ)) :
    e.C_orig.nextt w t i =
    δδt e.C_orig e.C_orig.border t := by
  induction t generalizing i with
  | zero =>
    simp only [Nat.cast_zero, neg_zero] at hi
    simp only [nextt_zero, δδt_zero, CellAutomaton.embed_config, word_to_config,
      CellAutomaton.border]
    split_ifs with h
    · exfalso; omega
    · rfl
  | succ t iht =>
    simp only [nextt_succ, CellAutomaton.next, δδt_succ]
    have hl : i - 1 < -(t : ℤ) := by omega
    have hc : i < -(t : ℤ) := by omega
    have hr : i + 1 < -(t : ℤ) := by omega
    rw [iht (i - 1) hl, iht i hc, iht (i + 1) hr]

/-- For positions right of the word (>= w.length), the original CA computes as δδt of the border -/
private lemma orig_right_of_word (w : Word e.α) (t : ℕ) (i : ℤ) (hi : i ≥ w.length) :
    e.C_orig.nextt w t i =
    δδt e.C_orig e.C_orig.border t := by
  induction t generalizing i with
  | zero =>
    simp only [nextt_zero, δδt_zero, CellAutomaton.embed_config, word_to_config,
      CellAutomaton.border]
    split_ifs with h
    · omega
    · rfl
  | succ t iht =>
    simp only [nextt_succ, CellAutomaton.next, δδt_succ]
    -- All three neighbors: i-1, i, i+1
    -- We know i >= w.length, so i+1 >= w.length and i >= w.length
    -- For i-1, either i-1 >= w.length (use iht) or i-1 < w.length but might be < -t
    have hr : i + 1 ≥ w.length := by omega
    have hc : i ≥ w.length := hi
    by_cases hl : i - 1 ≥ w.length
    · rw [iht (i - 1) hl, iht i hc, iht (i + 1) hr]
    · -- i - 1 < w.length, but since i >= w.length, we have i = w.length, so i - 1 = w.length - 1
      -- This position might be in the cone or to the left of it
      by_cases hl' : i - 1 < -(t : ℤ)
      · rw [orig_left_of_cone e w t (i - 1) hl', iht i hc, iht (i + 1) hr]
      · -- i - 1 is in the range [-t, w.length), so it's in the cone
        -- But we need the original value, not δδt. This is a problem!
        -- Actually, wait - in this case we should use left-independence
        -- The key is that for left-independent CAs, the result at position i only depends on
        -- positions i and i+1, not i-1. So we can use any value for i-1.
        rw [iht i hc, iht (i + 1) hr]
        exact e.h_left_indep _ _ _ _

/-- Main specification: inside the cone we get the original computation,
    outside we get border -/
private theorem spec_internal (w : Word e.α) (hw : w.length > 0) (t : ℕ) (i : ℤ) :
    e.C.nextt w t i =
      if i ∈ WordConeLeftIndep w t
      then Q'.state (e.C_orig.nextt w t i)
           (δδt e.C_orig e.C_orig.border t)
      else Q'.border := by
  induction t generalizing i with
  | zero =>
    simp only [nextt_zero, δδt_zero, WordConeLeftIndep_zero]
    split_ifs with hi
    · exact embed_config_in_range e w i hi
    · exact embed_config_out_range e w i hi
  | succ t ih =>
    by_cases hi_succ : i ∈ WordConeLeftIndep w (t + 1)
    · -- i is in cone at t+1
      rw [if_pos hi_succ]
      rw [WordConeLeftIndep_mem] at hi_succ
      obtain ⟨hi_low, hi_high⟩ := hi_succ
      simp only [nextt_succ, CellAutomaton.next, δδt_succ]
      by_cases hm_in : i ∈ WordConeLeftIndep w t
      · -- Middle is in cone
        rw [ih i, if_pos hm_in]
        -- Determine right neighbor: in cone → .state, else → .border (with orig = δδt)
        by_cases hr_in : i + 1 ∈ WordConeLeftIndep w t
        · rw [ih (i + 1), if_pos hr_in]
          exact δ'_mid_state e _ _ _ _ _ _ (Or.inl rfl)
        · rw [ih (i + 1), if_neg hr_in]
          rw [WordConeLeftIndep_mem] at hr_in; push_neg at hr_in
          have := orig_right_of_word e w t (i + 1) (hr_in (by omega))
          exact δ'_mid_state e _ _ _ _ _ _ (Or.inr ⟨rfl, this⟩)
      · -- Middle is NOT in cone (left edge: i < -t)
        rw [ih i, if_neg hm_in]
        rw [WordConeLeftIndep_mem] at hm_in; push_neg at hm_in
        have hi_left : i < -(t : ℤ) := by
          by_contra h; push_neg at h; have := hm_in h; omega
        have hr_in : i + 1 ∈ WordConeLeftIndep w t := by
          rw [WordConeLeftIndep_mem]; omega
        have hl_out : i - 1 ∉ WordConeLeftIndep w t := by
          rw [WordConeLeftIndep_mem]; omega
        rw [ih (i + 1), if_pos hr_in, ih (i - 1), if_neg hl_out]
        -- Original values at i and i-1 equal δδt t (both left of cone)
        rw [orig_left_of_cone e w t i hi_left,
            orig_left_of_cone e w t (i - 1) (by omega)]
        exact δ'_left_edge e _ _ _
    · -- i is NOT in cone at t+1
      rw [if_neg hi_succ]
      simp only [nextt_succ, CellAutomaton.next]
      rw [WordConeLeftIndep_mem] at hi_succ; push_neg at hi_succ
      -- Both middle and right are outside cone at time t
      have hm_out : i ∉ WordConeLeftIndep w t := by
        rw [WordConeLeftIndep_mem]; intro h; omega
      have hr_out : i + 1 ∉ WordConeLeftIndep w t := by
        rw [WordConeLeftIndep_mem]; intro h; omega
      rw [ih i, ih (i + 1), if_neg hm_out, if_neg hr_out]
      rfl

/-- Corollary: the projected computation matches the original -/
private theorem spec_unwrap (w : Word e.α) (hw : w.length > 0) (t : ℕ) (i : ℤ)
    (hi : i ∈ WordConeLeftIndep w t) :
    e.unwrap (e.C.nextt w t i)
             (δδt e.C_orig e.C_orig.border t) =
    e.C_orig.nextt w t i := by
  rw [spec_internal e w hw t i]
  simp only [hi, ↓reduceIte, unwrap]

/-- If the original border was already quiescent, the tracked border stays constant -/
private theorem spec_quiescent_orig (w : Word e.α) (hw : w.length > 0)
    (h_quiescent : e.C_orig.quiescent e.C_orig.border) (t : ℕ) (i : ℤ)
    (hi : i ∈ WordConeLeftIndep w t) :
    e.C.nextt w t i =
    Q'.state (e.C_orig.nextt w t i)
             e.C_orig.border := by
  rw [spec_internal e w hw t i, δδt_quiescent e.C_orig e.C_orig.border h_quiescent t]
  simp only [hi, ↓reduceIte]

/-- Main specification using comp: the projected computation matches the original -/
theorem spec (w : Word e.α) (hw : w.length > 0) (t : ℕ) (i : ℤ) :
    e.C.comp w t i =
      if i ∈ WordConeLeftIndep w t
      then e.C_orig.comp w t i
      else e.C_orig.project e.C_orig.border := by
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold, Function.comp_apply]
  rw [spec_internal e w hw t i]
  split_ifs with hi <;> rfl

end QuiescentBorderLeftIndep

end CellularAutomatas
