import CellularAutomatas.defs

namespace CellularAutomatas

section FSSP

def fssp_left_side (n : ℕ) : Word Bool :=
  if n = 0 then [] else [true] ++ List.replicate (n - 1) false

@[simp]
lemma fssp_left_side_length (n : ℕ) : (fssp_left_side n).length = n := by
  unfold fssp_left_side
  rcases n with _ | n <;> simp

structure SolvesFSSP (C : CellAutomaton Bool？ Bool)
    (input : ℕ → Word Bool) (time : ℕ → ℕ) : Prop where
  quiescent_set : C.quiescent_set { C.border, C.inner false }
  fire_iff : ∀ n : ℕ, n ≥ 2 →
    let w := input n
    ∀ t : ℕ, ∀ p : ℤ, 0 ≤ p ∧ p < w.length →
        (C.comp ⟬w⟭ t p = true ↔ t >= time n)

def SolvesFSSPOptimal (C : CellAutomaton Bool？ Bool) := SolvesFSSP C fssp_left_side (fun n => 2 * n - 2)

/-- Untouched soldiers do not project to the firing output. This follows from
    the length-two instance at time zero. -/
lemma SolvesFSSPOptimal.inner_false_projects_false
    {C : CellAutomaton Bool？ Bool} (hC : SolvesFSSPOptimal C) :
    C.project (C.inner false) = false := by
  have h := hC.fire_iff 2 (by omega) 0 1 (by simp)
  simpa [CellAutomaton.comp_apply, fssp_left_side, word_to_config] using h

/-- Two-sided FSSP input over `Bool × Bool`.

    The two components carry independent flags:
    * first component = "I am the leftmost cell";
    * second component = "I am the rightmost cell".

    For `n ≥ 2` the leftmost and rightmost cells are distinct (one bit each set);
    for `n = 1` the single cell is *both* (both bits set), distinguishing the
    `n = 1` case from any prefix of larger inputs. -/
def fssp_both_sides (n : ℕ) : Word (Bool × Bool) :=
  if n = 0 then []
  else if n = 1 then [(true, true)]
  else [(true, false)] ++ List.replicate (n - 2) (false, false) ++ [(false, true)]

/-- The two-sided FSSP, optimal version. Fires every interior cell at time
    `n − 1`. -/
structure SolvesTwoSidedFSSPOptimal (C : CellAutomaton (Bool × Bool)？ Bool) : Prop where
  /-- Border state is quiescent (a border cell with two border neighbours stays
      a border). -/
  quiescent_border : C.quiescent C.border
  /-- The border state projects to `false` (no firing at border cells). -/
  border_projects_false : C.project C.border = false
  /-- Firing spec: at every interior cell `0 ≤ p < n` (with `n ≥ 1`),
      the projection is `true` iff `t ≥ n − 1`. -/
  fire_iff : ∀ n : ℕ, n ≥ 1 →
    ∀ t : ℕ, ∀ p : ℤ, 0 ≤ p → p < (n : ℤ) →
      (C.comp ⟬fssp_both_sides n⟭ t p = true ↔ t ≥ n - 1)

/-! ### `fssp_both_sides` length and the corresponding "first-or-last" advice -/

@[simp]
lemma fssp_both_sides_length (n : ℕ) : (fssp_both_sides n).length = n := by
  unfold fssp_both_sides
  rcases n with _ | _ | n <;> simp

/-- The `Advice` form of `fssp_both_sides`: maps a word `w` to the
    `Bool × Bool` word of length `|w|` that flags the leftmost and rightmost
    cells via independent bits.

    Concretely matches the input alphabet expected by a two-sided FSSP solver,
    and is itself computable in 1 CA step (see `fssp_input_is_const_time_1`). -/
def Advice.fssp_input (α : Type) [Alphabet α] : Advice α (Bool × Bool) where
  f := fun w => fssp_both_sides w.length
  len := by intro w; simp

/-- `Advice.fssp_input` is a constant-time (1-step) CA-advice.

    Witness CA: state `Bool × Bool`, `δ l _ r = (l.1 ∧ l.2, r.1 ∧ r.2)`,
    `embed none = (true, true)` (so borders carry both bits set), and
    `embed (some _) = (false, false)` (interior cells carry both bits clear).
    After one step:
    * the first component is `true` iff the *left* neighbour was a border, i.e.
      iff the cell sits at position `0`;
    * the second component is `true` iff the *right* neighbour was a border,
      i.e. iff the cell sits at position `n − 1`.

    This matches `fssp_both_sides n` exactly, including `n = 1` where the
    single cell has both neighbours as borders and fires both bits. -/
private def fssp_input_ca (α : Type) [Alphabet α] : CellAutomaton α？ (Bool × Bool) := {
  Q := Bool × Bool
  δ := fun l _ r => (l.1 && l.2, r.1 && r.2)
  embed
    | none => (true, true)
    | some _ => (false, false)
  project := id
}

section FsspInputCa
variable {α : Type} [Alphabet α]

/-- The embed of `fssp_input_ca` on the word configuration: `(true, true)`
    outside `[0, |w|)`, `(false, false)` inside. -/
private lemma fssp_input_ca_embed_eq (w : Word α) (p : ℤ) :
    @CellAutomaton.embed_config _ _ (fssp_input_ca α) (word_to_config w) p =
      (if (0 ≤ p ∧ p < (w.length : ℤ)) then ((false, false) : Bool × Bool)
       else (true, true)) := by
  show (fssp_input_ca α).embed (word_to_config w p) = _
  unfold word_to_config
  by_cases h : (0 ≤ p ∧ p < (w.length : ℤ))
  · simp [h, fssp_input_ca]
  · simp [h, fssp_input_ca]

/-- For an in-range position `i` (so `0 ≤ i < n`), the value of
    `fssp_input_ca` after one step is `(decide (i = 0), decide (i = n − 1))`. -/
private lemma fssp_input_ca_comp_one_in_range (w : Word α) (i : ℤ)
    (h0 : 0 ≤ i) (hn : i < (w.length : ℤ)) :
    (fssp_input_ca α).comp ⟬w⟭ 1 i =
      (decide (i = 0), decide (i = (w.length : ℤ) - 1)) := by
  -- Unfold one step: project = id; δ takes (l.1 && l.2, r.1 && r.2).
  show (fssp_input_ca α).project ((fssp_input_ca α).next ⦋⟬w⟭⦌ i) = _
  rw [CellAutomaton.next_apply]
  show (fssp_input_ca α).δ
        (@CellAutomaton.embed_config _ _ (fssp_input_ca α) ⟬w⟭ (i - 1))
        (@CellAutomaton.embed_config _ _ (fssp_input_ca α) ⟬w⟭ i)
        (@CellAutomaton.embed_config _ _ (fssp_input_ca α) ⟬w⟭ (i + 1)) = _
  rw [fssp_input_ca_embed_eq, fssp_input_ca_embed_eq, fssp_input_ca_embed_eq]
  -- After rewrites, both neighbours' values depend only on whether each
  -- position is in range. Decompose into two scalar equations.
  -- First component: (l.1 && l.2) = decide (i = 0).
  -- Second component: (r.1 && r.2) = decide (i = (w.length : ℤ) - 1).
  apply Prod.ext
  · -- First component, indexed by left neighbour at `i - 1`.
    by_cases hi0 : i = 0
    · subst hi0
      have hL : ¬ (0 ≤ (0 : ℤ) - 1 ∧ (0 : ℤ) - 1 < (w.length : ℤ)) := by
        intro ⟨ha, _⟩; omega
      rw [if_neg hL]
      show (true && true) = decide ((0 : ℤ) = 0)
      rw [decide_eq_true (rfl : (0 : ℤ) = 0)]; rfl
    · have hL : (0 ≤ i - 1 ∧ i - 1 < (w.length : ℤ)) := by
        refine ⟨?_, by omega⟩; omega
      rw [if_pos hL]
      show (false && false) = decide (i = 0)
      rw [decide_eq_false hi0]; rfl
  · -- Second component, indexed by right neighbour at `i + 1`.
    by_cases hin1 : i = (w.length : ℤ) - 1
    · have hR_neg : ¬ (0 ≤ i + 1 ∧ i + 1 < (w.length : ℤ)) := by
        intro ⟨_, hb⟩; omega
      rw [if_neg hR_neg]
      show (true && true) = decide (i = (w.length : ℤ) - 1)
      rw [decide_eq_true hin1]; rfl
    · have hR : (0 ≤ i + 1 ∧ i + 1 < (w.length : ℤ)) := by
        refine ⟨by omega, ?_⟩; omega
      rw [if_pos hR]
      show (false && false) = decide (i = (w.length : ℤ) - 1)
      rw [decide_eq_false hin1]; rfl

/-- The `i`-th symbol of `fssp_both_sides n` (for `i < n`) is
    `(decide (i = 0), decide (i = n − 1))`. -/
lemma fssp_both_sides_getElem_eq (n : ℕ) (i : ℕ) (hi : i < n) :
    (fssp_both_sides n)[i]'(by simpa) =
      (decide (i = 0), decide (i = n - 1)) := by
  rcases n with _ | _ | m
  · omega
  · -- n = 1: only i = 0 possible, fssp_both_sides 1 = [(true, true)]
    have : i = 0 := by omega
    subst this
    simp [fssp_both_sides]
  · -- n = m + 2: [(true,false)] ++ replicate m (false,false) ++ [(false,true)]
    show ([(true, false)] ++ List.replicate m (false, false) ++ [(false, true)]
            : List (Bool × Bool))[i]'(by simp; omega) =
        (decide (i = 0), decide (i = m + 1 + 1 - 1))
    by_cases hi0 : i = 0
    · subst hi0
      simp
    · by_cases hil : i = m + 1
      · subst hil
        -- Index m+1 lands on the trailing [(false, true)].
        have h_len_pre : ([(true, false)] ++ List.replicate m (false, false)
            : List (Bool × Bool)).length = m + 1 := by simp
        set_option linter.unusedSimpArgs false in
        rw [List.getElem_append_right (by simp [h_len_pre])]
        set_option linter.unusedSimpArgs false in
        simp [h_len_pre]
      · -- 1 ≤ i ≤ m: lands inside replicate m (false, false)
        have h1 : 1 ≤ i := by omega
        have h2 : i ≤ m := by omega
        have h_len_pre : ([(true, false)] ++ List.replicate m (false, false)
            : List (Bool × Bool)).length = m + 1 := by simp
        have h_in_pre : i < ([(true, false)] ++ List.replicate m (false, false)
            : List (Bool × Bool)).length := by rw [h_len_pre]; omega
        rw [List.getElem_append_left h_in_pre]
        have h_after_one : ([(true, false)] : List (Bool × Bool)).length ≤ i := by
          simp; omega
        rw [List.getElem_append_right h_after_one]
        simp
        omega

end FsspInputCa

def fssp_input_is_const_time_1 {α : Type} [Alphabet α] :
    Advice.IsConstTimeAdvice 1 (Advice.fssp_input α) where
  C := fssp_input_ca α
  spec w := by
    show fssp_both_sides w.length = _
    apply List.ext_getElem (by simp)
    intro i h_lhs _h_rhs
    have hi : i < w.length := by simpa using h_lhs
    rw [fssp_both_sides_getElem_eq w.length i hi]
    simp only [List.getElem_map, List.getElem_range]
    rw [fssp_input_ca_comp_one_in_range w (i : ℤ)
        (Int.natCast_nonneg i) (by exact_mod_cast hi)]
    -- Equate ℕ-form decides with ℤ-form decides componentwise.
    apply Prod.ext
    · -- decide (i = 0) = decide ((i : ℤ) = 0)
      by_cases hi0 : i = 0
      · subst hi0; rfl
      · have h_iz0 : (i : ℤ) ≠ 0 := by exact_mod_cast hi0
        rw [decide_eq_false hi0, decide_eq_false h_iz0]
    · -- decide (i = w.length - 1) = decide ((i : ℤ) = (w.length : ℤ) - 1)
      by_cases hil : i = w.length - 1
      · have h_pos : 1 ≤ w.length := by omega
        have h_iz : ((i : ℤ) = (w.length : ℤ) - 1) := by
          rw [hil]; omega
        rw [decide_eq_true hil, decide_eq_true h_iz]
      · have h_iz : (i : ℤ) ≠ (w.length : ℤ) - 1 := by
          intro h
          apply hil
          have h_i_nn : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
          have h_pos : 1 ≤ w.length := by
            have : (0 : ℤ) ≤ (w.length : ℤ) - 1 := h ▸ h_i_nn
            omega
          have h_cast : ((w.length - 1 : ℕ) : ℤ) = (w.length : ℤ) - 1 := by omega
          have : (i : ℤ) = ((w.length - 1 : ℕ) : ℤ) := by rw [h_cast]; exact h
          exact_mod_cast this
        rw [decide_eq_false hil, decide_eq_false h_iz]


end FSSP

end CellularAutomatas
