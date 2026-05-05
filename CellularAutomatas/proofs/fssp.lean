import CellularAutomatas.defs

namespace CellularAutomatas

section FSSP

def fssp_left_side (n : ℕ) : Word Bool := [true] ++ List.replicate (n - 1) false

structure SolvesFSSP (C : CellAutomaton Bool？ Bool)
    (input : ℕ → Word Bool) (time : ℕ → ℕ) : Prop where
  quiescent_set : C.quiescent_set { C.border, C.inner false }
  fire_iff : ∀ n : ℕ, n ≥ 1 →
    let w := input n
    ∀ t : ℕ, ∀ p : ℤ, 0 ≤ p ∧ p < w.length →
        C.comp ⟬w⟭ t p = true ↔ t >= time n

def SolvesFSSPOptimal (C : CellAutomaton Bool？ Bool) := SolvesFSSP C fssp_left_side (fun n => 2 * n - 2)

def fssp_both_sides (n : ℕ) : Word Bool :=
  if n = 0 then []
  else if n = 1 then [true]
  else [true] ++ List.replicate (n - 2) false ++ [true]

def SolvesTwoSidedFSSPOptimal (C : CellAutomaton Bool？ Bool) := SolvesFSSP C fssp_both_sides (fun n => n - 1)


theorem SolvesFSSPOptimal_exists:
  ∃ C : CellAutomaton Bool？ Bool, SolvesFSSPOptimal C := by
  sorry


theorem SolvesTwoSidedFSSPOptimal_of_SolvesFSSPOptimal (C : CellAutomaton Bool？ Bool) (h : SolvesFSSPOptimal C):
    ∃ C': CellAutomaton Bool？ Bool, SolvesTwoSidedFSSPOptimal C' := by
  sorry


/-! ### `fssp_both_sides` length and the corresponding "first-or-last" advice -/

@[simp]
lemma fssp_both_sides_length (n : ℕ) : (fssp_both_sides n).length = n := by
  unfold fssp_both_sides
  rcases n with _ | _ | n <;> simp

/-- The `Advice` form of `fssp_both_sides`: maps a word `w` to the Bool word
    that is `true` at positions `0` and `|w| - 1` and `false` everywhere else.

    Concretely matches the input alphabet expected by a two-sided FSSP solver,
    and is itself computable in 1 CA step (see `fssp_input_is_const_time_1`). -/
def Advice.fssp_input (α : Type) [Alphabet α] : Advice α Bool where
  f := fun w => fssp_both_sides w.length
  len := by intro w; simp

/-- `Advice.fssp_input` is a constant-time (1-step) CA-advice.

    Witness CA: state `Bool`, `δ` is the 3-input OR, `embed none = true` (so
    borders carry `true`), `embed (some _) = false` (interior cells carry
    `false`), `project = id`. After one step, an interior cell projects to
    `true` iff at least one of its three neighbours was a border at step 0,
    which holds iff the cell sits at position `0` or `n − 1`. This matches
    `fssp_both_sides n`. -/
private def fssp_input_ca (α : Type) [Alphabet α] : CellAutomaton α？ Bool := {
  Q := Bool
  δ := fun l m r => l || m || r
  embed
    | none => true
    | some _ => false
  project := id
}

section FsspInputCa
variable {α : Type} [Alphabet α]

/-- The embed of `fssp_input_ca` on the word configuration is `true` exactly
    outside `[0, |w|)`. -/
private lemma fssp_input_ca_embed_eq (w : Word α) (p : ℤ) :
    @CellAutomaton.embed_config _ _ (fssp_input_ca α) (word_to_config w) p =
      decide (¬ (0 ≤ p ∧ p < (w.length : ℤ))) := by
  show (fssp_input_ca α).embed (word_to_config w p) = _
  unfold word_to_config
  by_cases h : (0 ≤ p ∧ p < (w.length : ℤ))
  · simp [h, fssp_input_ca]
  · simp [h, fssp_input_ca]

/-- For an in-range position `i` (so `0 ≤ i < n`), the value of
    `fssp_input_ca` after one step is `true ↔ i = 0 ∨ i = n − 1`. -/
private lemma fssp_input_ca_comp_one_in_range (w : Word α) (i : ℤ)
    (h0 : 0 ≤ i) (hn : i < (w.length : ℤ)) :
    (fssp_input_ca α).comp ⟬w⟭ 1 i =
      (decide (i = 0) || decide (i = (w.length : ℤ) - 1)) := by
  -- Unfold one step of the CA: project = id; δ = OR of three.
  show (fssp_input_ca α).project ((fssp_input_ca α).next ⦋⟬w⟭⦌ i) = _
  unfold CellAutomaton.next
  rw [fssp_input_ca_embed_eq, fssp_input_ca_embed_eq, fssp_input_ca_embed_eq]
  show (decide (¬(0 ≤ i - 1 ∧ i - 1 < (w.length : ℤ))) ||
        decide (¬(0 ≤ i ∧ i < (w.length : ℤ))) ||
        decide (¬(0 ≤ i + 1 ∧ i + 1 < (w.length : ℤ))) : Bool)
       = _
  -- Middle decide is `false`; left iff `i = 0`; right iff `i = n - 1`.
  by_cases hi0 : i = 0
  · subst hi0
    have hn0 : (0 : ℤ) < (w.length : ℤ) := hn
    have hRange : ¬ (0 ≤ (0 : ℤ) - 1 ∧ (0 : ℤ) - 1 < (w.length : ℤ)) := by
      intro ⟨ha, _⟩; omega
    simp
  · by_cases hin : i = (w.length : ℤ) - 1
    · subst hin
      have hL : 0 ≤ (w.length : ℤ) - 1 - 1 ∧ (w.length : ℤ) - 1 - 1 < (w.length : ℤ) := by omega
      have hM : 0 ≤ (w.length : ℤ) - 1 ∧ (w.length : ℤ) - 1 < (w.length : ℤ) := by omega
      have hR : ¬ (0 ≤ (w.length : ℤ) - 1 + 1 ∧ (w.length : ℤ) - 1 + 1 < (w.length : ℤ)) := by
        intro ⟨_, hb⟩; omega
      simp [hL, hM]
    · -- 0 < i < n - 1, so all three positions in range.
      have hL : 0 ≤ i - 1 ∧ i - 1 < (w.length : ℤ) := by
        constructor
        · have : i ≠ 0 := hi0
          omega
        · omega
      have hM : 0 ≤ i ∧ i < (w.length : ℤ) := ⟨h0, hn⟩
      have hR : 0 ≤ i + 1 ∧ i + 1 < (w.length : ℤ) := by
        constructor
        · omega
        · have : i ≠ (w.length : ℤ) - 1 := hin
          omega
      -- All three negations are False; both decides on RHS are false.
      rw [decide_eq_false (fun h => h hL), decide_eq_false (fun h => h hM),
          decide_eq_false (fun h => h hR), decide_eq_false hi0, decide_eq_false hin]
      rfl

/-- The `i`-th symbol of `fssp_both_sides n` (for `i < n`) is
    `true ↔ i = 0 ∨ i = n − 1`. -/
private lemma fssp_both_sides_getElem_eq (n : ℕ) (i : ℕ) (hi : i < n) :
    (fssp_both_sides n)[i]'(by simpa) =
      (decide (i = 0) || decide (i = n - 1)) := by
  rcases n with _ | _ | m
  · omega
  · -- n = 1: only i = 0 possible, fssp_both_sides 1 = [true]
    have : i = 0 := by omega
    subst this
    simp [fssp_both_sides]
  · -- n = m + 2: [true] ++ replicate m false ++ [true]
    -- Re-frame the goal with `m + 2` for the length.
    show ([true] ++ List.replicate m false ++ [true] : List Bool)[i]'(by simp; omega) =
        (decide (i = 0) || decide (i = m + 1 + 1 - 1))
    by_cases hi0 : i = 0
    · subst hi0
      simp
    · by_cases hil : i = m + 1
      · subst hil
        -- Index m+1 lands on the trailing [true].
        have h_len_pre : ([true] ++ List.replicate m false : List Bool).length = m + 1 := by simp
        set_option linter.unusedSimpArgs false in
        rw [List.getElem_append_right (by simp [h_len_pre])]
        set_option linter.unusedSimpArgs false in
        simp [h_len_pre]
      · -- 1 ≤ i ≤ m: lands inside replicate m false
        have h1 : 1 ≤ i := by omega
        have h2 : i ≤ m := by omega
        have h_len_pre : ([true] ++ List.replicate m false : List Bool).length = m + 1 := by simp
        have h_in_pre : i < ([true] ++ List.replicate m false : List Bool).length := by
          rw [h_len_pre]; omega
        rw [List.getElem_append_left h_in_pre]
        -- Inside [true] ++ replicate m false: index i ≥ 1 lies in replicate.
        have h_after_one : ([true] : List Bool).length ≤ i := by simp; omega
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
    -- LHS at index i.
    rw [fssp_both_sides_getElem_eq w.length i hi]
    -- RHS: simp through the map and range.
    simp only [List.getElem_map, List.getElem_range]
    rw [fssp_input_ca_comp_one_in_range w (i : ℤ)
        (Int.natCast_nonneg i) (by exact_mod_cast hi)]
    -- Equate ℕ-form decides with ℤ-form decides.
    by_cases hi0 : i = 0
    · subst hi0; simp
    · by_cases hil : i = w.length - 1
      · have hpos : 1 ≤ w.length := by omega
        have h_iz : ((i : ℤ) = (w.length : ℤ) - 1) := by
          rw [hil]; omega
        rw [decide_eq_true hil, decide_eq_true h_iz]
        simp
      · have h_zR : (i : ℤ) ≠ (w.length : ℤ) - 1 := by
          intro h
          apply hil
          have h_pos : 1 ≤ w.length := by
            have h_i_nn : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
            have : (0 : ℤ) ≤ (w.length : ℤ) - 1 := h ▸ h_i_nn
            omega
          have h_cast : ((w.length - 1 : ℕ) : ℤ) = (w.length : ℤ) - 1 := by omega
          have : (i : ℤ) = ((w.length - 1 : ℕ) : ℤ) := by rw [h_cast]; exact h
          exact_mod_cast this
        simp [h_zR, hi0, hil]


end FSSP

end CellularAutomatas
