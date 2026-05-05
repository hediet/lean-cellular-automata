/-
  QuiescentBorder: Converting an arbitrary CA to one with quiescent border

  Given any CA C, we construct C' where:
  - The border is quiescent (δ(border, border, border) = border)
  - The computation inside the (symmetric) word cone matches the original

  Note: Unlike `QuiescentBorderLeftIndep`, this construction does not assume
  (and does not preserve) left-independence. The cone expands in BOTH
  directions: at time t, positions in `[-t, w.length + t)`.

  For a left-independence-preserving variant, see
  `border_quiescent_left_independent.lean`. Both files share the helper
  `δδt` and the iterated-border lemmas.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.border
import CellularAutomatas.proofs.constructions.border_quiescent_left_independent

namespace CellularAutomatas

open CellAutomaton

/-! ## Symmetric word cone for general CAs

  At time t, information has propagated by t cells in each direction.
  Cone at t = [-t, w.length + t).
-/

def WordCone {α : Type} (w : Word α) (t : ℕ) : Set ℤ :=
  { i : ℤ | (-t : ℤ) ≤ i ∧ i < w.length + t }

instance {α : Type} (w : Word α) (t : ℕ) (i : ℤ) : Decidable (i ∈ WordCone w t) := by
  unfold WordCone
  infer_instance

@[simp]
lemma WordCone_zero {α : Type} (w : Word α) : WordCone w 0 = w.range := by
  ext i
  simp only [WordCone, Word.range, ge_iff_le, Set.mem_setOf_eq,
    Nat.cast_zero, neg_zero, add_zero]

lemma WordCone_mem {α : Type} (w : Word α) (t : ℕ) (i : ℤ) :
    i ∈ WordCone w t ↔ (-t : ℤ) ≤ i ∧ i < w.length + t := by
  simp only [WordCone, Set.mem_setOf_eq]

/-! ## QuiescentBorder construction

  Given any CA C, we construct C' with:
  - Q' = border | state(s, tracked_border)
  - δ'(_, border, border) = border  (quiescent!)
  - When some neighbour is a state, the tracked border tells us what value
    the original CA has at every cell that was outside the cone, allowing
    us to fill in the missing positions and apply the original δ.
-/

structure QuiescentBorder where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β

attribute [instance] QuiescentBorder._inst_α
attribute [instance] QuiescentBorder._inst_β

namespace QuiescentBorder

variable (e : QuiescentBorder)

/-- State space for C': either the quiescent border, or a state paired with
    the tracked border value `δδt C.border t`. -/
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

/-- Transition function for C'.

    The all-border case is quiescent. Whenever some neighbour is a state we
    use its tracked border to fill any border neighbour, then apply the
    original `δ`. Inconsistent tracked borders never arise in valid evolution
    (all in-cone cells track the same `δδt C.border t`); the `if`s default
    to `border` defensively. -/
def δ' : Q' e → Q' e → Q' e → Q' e
  -- middle is a state: at least one neighbour is the middle itself
  | .state a ar, .state b br, .state c cr =>
      if ar = br ∧ br = cr then
        .state (e.C_orig.δ a b c) (e.C_orig.δ br br br)
      else .border
  | .state a ar, .state b br, .border =>
      if ar = br then
        .state (e.C_orig.δ a b br) (e.C_orig.δ br br br)
      else .border
  | .border, .state b br, .state c cr =>
      if br = cr then
        .state (e.C_orig.δ br b c) (e.C_orig.δ br br br)
      else .border
  | .border, .state b br, .border =>
      .state (e.C_orig.δ br b br) (e.C_orig.δ br br br)
  -- middle is border, but at least one of left/right is a state ("entering" the cone)
  | .state a ar, .border, .border =>
      .state (e.C_orig.δ a ar ar) (e.C_orig.δ ar ar ar)
  | .border, .border, .state c cr =>
      .state (e.C_orig.δ cr cr c) (e.C_orig.δ cr cr cr)
  | .state a ar, .border, .state c cr =>
      -- Doesn't arise in valid evolution (cone is contiguous), but specified for totality.
      if ar = cr then
        .state (e.C_orig.δ a ar c) (e.C_orig.δ ar ar ar)
      else .border
  -- all three border → border (quiescent)
  | .border, .border, .border => .border

/-- Project Q' to the original output type. -/
def project' : Q' e → e.β
  | .border => e.C_orig.project e.C_orig.border
  | .state s _ => e.C_orig.project s

/-- The CA with quiescent border. -/
def C : CellAutomaton e.α？ e.β := {
  Q := Q' e
  δ := e.δ'
  embed := fun a => match a with
    | some a' => .state (e.C_orig.embed (some a')) e.C_orig.border
    | none => .border
  project := e.project'
}

/-- The border of C is quiescent. -/
lemma C_border_quiescent : e.C.quiescent e.C.border := by
  unfold CellAutomaton.quiescent CellAutomaton.quiescent_set CellAutomaton.border C
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  simp only [Set.mem_singleton_iff] at ha hb hc
  subst ha hb hc
  rfl

/-- The border of C is the border constructor. -/
@[simp]
lemma C_border_eq : e.C.border = Q'.border := rfl

/-- Trivial helper: `e.C.δ` is `e.δ'`. Useful to expose the explicit `δ'`
    pattern-match for `simp` / case enumeration. -/
private lemma C_δ_apply (a b c : Q' e) : e.C.δ a b c = e.δ' a b c := rfl

/-! ## Embed-config helpers (positions inside / outside the input range) -/

private lemma embed_config_in_range (w : Word e.α) (i : ℤ) (hi : i ∈ w.range) :
    CellAutomaton.embed_config (C := e.C) (word_to_config w) i =
    Q'.state (CellAutomaton.embed_config (C := e.C_orig) (word_to_config w) i)
             e.C_orig.border := by
  simp only [Word.range, ge_iff_le, Set.mem_setOf_eq] at hi
  simp only [CellAutomaton.embed_config, word_to_config, C, hi]
  rfl

private lemma embed_config_out_range (w : Word e.α) (i : ℤ) (hi : i ∉ w.range) :
    CellAutomaton.embed_config (C := e.C) (word_to_config w) i = Q'.border := by
  simp only [Word.range, ge_iff_le, Set.mem_setOf_eq, not_and, not_lt] at hi
  simp only [CellAutomaton.embed_config, word_to_config, C]
  split_ifs with h
  · exfalso; exact (hi h.1).not_gt h.2
  · rfl

/-! ## Out-of-cone behaviour of the *original* CA

  Outside the cone the original CA's value coincides with the iterated border:
  any position farther than `t` from the input range has only ever seen
  border neighbours.
-/

/-- For positions left of the cone, the original CA equals `δδt C.border t`. -/
private lemma orig_left_of_cone (w : Word e.α) (t : ℕ) (i : ℤ) (hi : i < -(t : ℤ)) :
    e.C_orig.nextt w t i = δδt e.C_orig e.C_orig.border t := by
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
    have hl : i - 1 < -(t : ℤ) := by push_cast at hi; omega
    have hc : i < -(t : ℤ) := by push_cast at hi; omega
    have hr : i + 1 < -(t : ℤ) := by push_cast at hi; omega
    rw [iht (i - 1) hl, iht i hc, iht (i + 1) hr]

/-- For positions right of the cone, the original CA equals `δδt C.border t`. -/
private lemma orig_right_of_cone (w : Word e.α) (t : ℕ) (i : ℤ)
    (hi : (w.length : ℤ) + t ≤ i) :
    e.C_orig.nextt w t i = δδt e.C_orig e.C_orig.border t := by
  induction t generalizing i with
  | zero =>
    simp only [Nat.cast_zero, add_zero] at hi
    simp only [nextt_zero, δδt_zero, CellAutomaton.embed_config, word_to_config,
      CellAutomaton.border]
    split_ifs with h
    · exfalso; omega
    · rfl
  | succ t iht =>
    simp only [nextt_succ, CellAutomaton.next, δδt_succ]
    have hl : (w.length : ℤ) + t ≤ i - 1 := by push_cast at hi; omega
    have hc : (w.length : ℤ) + t ≤ i := by push_cast at hi; omega
    have hr : (w.length : ℤ) + t ≤ i + 1 := by push_cast at hi; omega
    rw [iht (i - 1) hl, iht i hc, iht (i + 1) hr]

/-! ## Combiner: pasting an in-cone state from neighbour values

  After the IH and case-splitting, each successor case reduces to "the
  neighbour values are these `e.C_orig.nextt`, the tracked border is `δδt t`,
  so the result is `state (orig.nextt (t+1) i) (δδt (t+1))`".

  The RHS uses `orig.δ`-form (rather than `orig.nextt (t+1) i`) because
  `simp only [nextt_succ, CellAutomaton.next]` is also applied to the
  original CA's `nextt` on the goal's RHS during the inductive step. -/

private lemma combine_state {a b c br : e.C_orig.Q} (w : Word e.α) (t : ℕ) (i : ℤ)
    (ha : a = e.C_orig.nextt w t (i - 1))
    (hb : b = e.C_orig.nextt w t i)
    (hc : c = e.C_orig.nextt w t (i + 1))
    (hbr : br = δδt e.C_orig e.C_orig.border t) :
    Q'.state (e.C_orig.δ a b c) (e.C_orig.δ br br br) =
    Q'.state
      (e.C_orig.δ (e.C_orig.nextt w t (i - 1))
                  (e.C_orig.nextt w t i)
                  (e.C_orig.nextt w t (i + 1)))
      (δδt e.C_orig e.C_orig.border (t + 1)) := by
  subst ha hb hc hbr
  rfl

/-! ## Main specification

  Inside the cone we get the original computation paired with the tracked
  border; outside we get `border`. -/

/-- Convert "in cone" / "out of cone" hypotheses to a single arithmetic disjunction.
    Useful before omega in subcase reasoning. -/
private lemma not_in_cone_iff {α : Type} (w : Word α) (t : ℕ) (i : ℤ) :
    i ∉ WordCone w t ↔ i < -(t : ℤ) ∨ (w.length : ℤ) + t ≤ i := by
  simp only [WordCone_mem, not_and_or, not_le, not_lt]

private theorem spec_internal (w : Word e.α) (hw : w.length > 0) (t : ℕ) (i : ℤ) :
    e.C.nextt w t i =
      if i ∈ WordCone w t
      then Q'.state (e.C_orig.nextt w t i) (δδt e.C_orig e.C_orig.border t)
      else Q'.border := by
  induction t generalizing i with
  | zero =>
    simp only [nextt_zero, δδt_zero, WordCone_zero]
    split_ifs with hi
    · exact embed_config_in_range e w i hi
    · exact embed_config_out_range e w i hi
  | succ t ih =>
    by_cases hi_succ : i ∈ WordCone w (t + 1)
    · -- i in cone at t+1: the result is a `state`.
      rw [if_pos hi_succ]
      rw [WordCone_mem] at hi_succ
      obtain ⟨hi_low, hi_high⟩ := hi_succ
      push_cast at hi_low hi_high
      simp only [nextt_succ, CellAutomaton.next]
      rw [ih (i - 1), ih i, ih (i + 1), C_δ_apply]
      -- Case-split on whether each neighbour is in cone at t.
      by_cases hl_in : (i - 1) ∈ WordCone w t
      all_goals by_cases hm_in : i ∈ WordCone w t
      all_goals by_cases hr_in : (i + 1) ∈ WordCone w t
      -- 8 subcases; 2 are impossible.
      · -- (T, T, T): generic interior
        rw [if_pos hl_in, if_pos hm_in, if_pos hr_in]
        simp only [δ', and_self, ↓reduceIte]
        exact combine_state e w t i rfl rfl rfl rfl
      · -- (T, T, F): right edge new (i = w.length + t - 1)
        rw [if_pos hl_in, if_pos hm_in, if_neg hr_in]
        rw [WordCone_mem] at hm_in
        rw [not_in_cone_iff] at hr_in
        have h_orig_r : e.C_orig.nextt w t (i + 1) =
            δδt e.C_orig e.C_orig.border t := by
          apply orig_right_of_cone e w t (i + 1)
          rcases hr_in with h | h
          · omega
          · exact h
        simp only [δ', ↓reduceIte]
        exact combine_state e w t i rfl rfl h_orig_r.symm rfl
      · -- (T, F, T): impossible (cone is contiguous)
        exfalso
        rw [WordCone_mem] at hl_in hr_in
        rw [not_in_cone_iff] at hm_in
        rcases hm_in with h | h <;> omega
      · -- (T, F, F): far right edge new (i = w.length + t)
        rw [if_pos hl_in, if_neg hm_in, if_neg hr_in]
        rw [WordCone_mem] at hl_in
        rw [not_in_cone_iff] at hm_in hr_in
        have hi_eq : (w.length : ℤ) + t ≤ i := by
          rcases hm_in with h | h
          · omega
          · exact h
        have h_orig_m : e.C_orig.nextt w t i = δδt e.C_orig e.C_orig.border t :=
          orig_right_of_cone e w t i hi_eq
        have h_orig_r : e.C_orig.nextt w t (i + 1) = δδt e.C_orig e.C_orig.border t :=
          orig_right_of_cone e w t (i + 1) (by omega)
        simp only [δ']
        exact combine_state e w t i rfl h_orig_m.symm h_orig_r.symm rfl
      · -- (F, T, T): left edge new (i = -t)
        rw [if_neg hl_in, if_pos hm_in, if_pos hr_in]
        rw [not_in_cone_iff] at hl_in
        rw [WordCone_mem] at hm_in
        have h_orig_l : e.C_orig.nextt w t (i - 1) =
            δδt e.C_orig e.C_orig.border t := by
          apply orig_left_of_cone e w t (i - 1)
          rcases hl_in with h | h
          · exact h
          · omega
        simp only [δ', ↓reduceIte]
        exact combine_state e w t i h_orig_l.symm rfl rfl rfl
      · -- (F, T, F): isolated middle (small word, t = 0, w.length = 1)
        rw [if_neg hl_in, if_pos hm_in, if_neg hr_in]
        rw [not_in_cone_iff] at hl_in hr_in
        rw [WordCone_mem] at hm_in
        have h_orig_l : e.C_orig.nextt w t (i - 1) =
            δδt e.C_orig e.C_orig.border t := by
          apply orig_left_of_cone e w t (i - 1)
          rcases hl_in with h | h
          · exact h
          · omega
        have h_orig_r : e.C_orig.nextt w t (i + 1) =
            δδt e.C_orig e.C_orig.border t := by
          apply orig_right_of_cone e w t (i + 1)
          rcases hr_in with h | h
          · omega
          · exact h
        simp only [δ']
        exact combine_state e w t i h_orig_l.symm rfl h_orig_r.symm rfl
      · -- (F, F, T): far left edge new (i = -t-1)
        rw [if_neg hl_in, if_neg hm_in, if_pos hr_in]
        rw [not_in_cone_iff] at hl_in hm_in
        rw [WordCone_mem] at hr_in
        have hi_lt : i < -((t : ℤ)) := by
          rcases hm_in with h | h
          · exact h
          · omega
        have h_orig_l : e.C_orig.nextt w t (i - 1) =
            δδt e.C_orig e.C_orig.border t :=
          orig_left_of_cone e w t (i - 1) (by omega)
        have h_orig_m : e.C_orig.nextt w t i = δδt e.C_orig e.C_orig.border t :=
          orig_left_of_cone e w t i hi_lt
        simp only [δ']
        exact combine_state e w t i h_orig_l.symm h_orig_m.symm rfl rfl
      · -- (F, F, F): impossible when i in cone at t+1 and w.length > 0.
        exfalso
        rw [not_in_cone_iff] at hl_in hm_in hr_in
        rcases hl_in with hl | hl <;> rcases hm_in with hm | hm <;>
            rcases hr_in with hr | hr <;> omega
    · -- i not in cone at t+1: result is border.
      rw [if_neg hi_succ]
      simp only [nextt_succ, CellAutomaton.next]
      rw [not_in_cone_iff] at hi_succ
      have h1 : i - 1 ∉ WordCone w t := by
        rw [not_in_cone_iff]
        rcases hi_succ with h | h
        · left; omega
        · right; push_cast at h ⊢; omega
      have h2 : i ∉ WordCone w t := by
        rw [not_in_cone_iff]
        rcases hi_succ with h | h
        · left; omega
        · right; push_cast at h ⊢; omega
      have h3 : i + 1 ∉ WordCone w t := by
        rw [not_in_cone_iff]
        rcases hi_succ with h | h
        · left; omega
        · right; push_cast at h ⊢; omega
      rw [ih (i - 1), ih i, ih (i + 1), if_neg h1, if_neg h2, if_neg h3]
      rfl

/-- Main specification using `comp`: inside the cone we recover the original
    computation; outside we get `C_orig.project C_orig.border`. -/
theorem spec (w : Word e.α) (hw : w.length > 0) (t : ℕ) (i : ℤ) :
    e.C.comp w t i =
      if i ∈ WordCone w t
      then e.C_orig.comp w t i
      else e.C_orig.project e.C_orig.border := by
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold]
  rw [spec_internal e w hw t i]
  split_ifs with hi <;> rfl

end QuiescentBorder

end CellularAutomatas
