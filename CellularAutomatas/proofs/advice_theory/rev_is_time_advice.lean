/-
  # Reversal is an `n`-time advice (= "rt + 1"-advice)

  Statement:

      `Advice.rev_is_time_advice : (Advice.rev α).IsTimeAdvice (fun n => n)`

  Construction. Each inner cell carries two tracks (`upper`, `lower`),
  each holding an `Option α`. Initially the lower track holds the input
  symbol and the upper track is blank. Per step:

  * the upper track moves rightward (next upper = left neighbour's upper);
  * the lower track moves leftward  (next lower = right neighbour's lower);
  * at the left edge — when the left neighbour is the border — the cell's
    own lower value is reflected onto the upper track.

  After `n = |w|` steps, the upper track at cell `i ∈ [0, n)` carries
  `w[n − 1 − i] = (rev w)[i]`. The lower track at cell `i` has carried
  `w[i]` leftward to cell `0` (arriving at time `i`); cell `0` reflected
  it onto the upper track at time `i + 1`; from there it travelled
  rightward, reaching cell `n − 1 − i` at time `i + 1 + (n − 1 − i) = n`.

  This is "rt + 1" because real-time reads at `t = n − 1`; the extra step
  is the reflection.
-/

import CellularAutomatas.defs

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

/-- The reversal advice: maps each word to its reverse. -/
def Advice.rev (α : Type) : Advice α α :=
  ⟨fun w => w.reverse, by simp⟩

namespace RevAdvice

/-! ## Witness CA -/

/-- State of the witness CA.

    * `none` — border (cell sitting outside the input range);
    * `some (u, ℓ)` — inner cell with upper-track value `u` and lower-track
      value `ℓ`. Each track holds an `Option α` (`none` = blank). -/
abbrev Q (α : Type) := Option (Option α × Option α)

/-- Local rule: borders stay borders; inner cells shift their two tracks
    in opposite directions; at the left edge the lower value is reflected
    onto the upper track. -/
def δ : Q α → Q α → Q α → Q α
  | _, none, _ => none
  | l, some (_, cl), r =>
    let new_upper :=
      match l with
      | none           => cl                -- left edge: reflect lower → upper
      | some (lu, _)   => lu                -- shift upper rightward
    let new_lower :=
      match r with
      | none           => none              -- right edge: nothing arrives
      | some (_, rl)   => rl                -- shift lower leftward
    some (new_upper, new_lower)

/-- Embedding: borders stay borders; inner cells start with the input on
    the lower track and a blank upper track. -/
def embed : Option α → Q α
  | none     => none
  | some a   => some (none, some a)

/-- Projection: read the upper track. (For blank/border states we fall
    back to `default`; the spec only inspects positions where the upper
    track is filled.) -/
def project : Q α → α
  | none                  => default
  | some (none,  _)       => default
  | some (some a, _)      => a

/-- The witness CA realising the reversal advice in time `n`. -/
def witnessCA (α : Type) [Alphabet α] : CellAutomaton α？ α where
  Q       := Q α
  δ       := δ
  embed   := embed
  project := project

/-! ## State invariant

    For an inner cell `i ∈ [0, n)` at time `t ≤ n` the witness state is
    `some (upperVal w t i, lowerVal w t i)`, where:

    * `upperVal` holds the symbol that arrived from the reflected wave;
    * `lowerVal` holds the symbol still travelling leftward. -/

/-- Upper-track value at inner cell `i` at time `t`. -/
def upperVal (w : Word α) (t i : ℕ) : Option α :=
  if i + 1 ≤ t then w[t - 1 - i]? else none

/-- Lower-track value at inner cell `i` at time `t`. -/
def lowerVal (w : Word α) (t i : ℕ) : Option α :=
  w[t + i]?

/-- Expected state at integer position `i` at time `t`. -/
def stateAt (w : Word α) (t : ℕ) (i : ℤ) : Q α :=
  if 0 ≤ i ∧ i < (w.length : ℤ) then
    some (upperVal w t i.toNat, lowerVal w t i.toNat)
  else
    none

/-! ### Helpers for `stateAt` -/

omit [Alphabet α] in
private lemma stateAt_outside (w : Word α) (t : ℕ) (i : ℤ)
    (h : ¬ (0 ≤ i ∧ i < (w.length : ℤ))) :
    stateAt w t i = none := by
  simp [stateAt, h]

omit [Alphabet α] in
private lemma stateAt_inside (w : Word α) (t : ℕ) (i : ℤ)
    (h : 0 ≤ i ∧ i < (w.length : ℤ)) :
    stateAt w t i = some (upperVal w t i.toNat, lowerVal w t i.toNat) := by
  simp [stateAt, h]

/-! ### `δ` helper lemmas

    Each lemma below specialises `δ` to a particular shape of the
    *neighbourhood*. The cell's own upper component is irrelevant —
    only its lower component (`cl`) matters — so we keep `cu` free. -/

omit [Alphabet α] in
private lemma δ_none (l r : Q α) : δ l none r = none := by
  cases l <;> cases r <;> rfl

omit [Alphabet α] in
private lemma δ_left_edge (cu cl : Option α) (ru rl : Option α) :
    δ none (some (cu, cl)) (some (ru, rl)) = some (cl, rl) := rfl

omit [Alphabet α] in
private lemma δ_interior (lu ll cu cl ru rl : Option α) :
    δ (some (lu, ll)) (some (cu, cl)) (some (ru, rl)) = some (lu, rl) := rfl

omit [Alphabet α] in
private lemma δ_right_edge_inner (lu ll cu cl : Option α) :
    δ (some (lu, ll)) (some (cu, cl)) none = some (lu, none) := rfl

omit [Alphabet α] in
private lemma δ_singleton (cu cl : Option α) :
    δ none (some (cu, cl)) none = some (cl, none) := rfl

/-! ### Bookkeeping for `upperVal` / `lowerVal` -/

omit [Alphabet α] in
@[simp] private lemma upperVal_zero (w : Word α) (i : ℕ) :
    upperVal w 0 i = none := by
  simp [upperVal]

omit [Alphabet α] in
@[simp] private lemma lowerVal_zero (w : Word α) (i : ℕ) :
    lowerVal w 0 i = w[i]? := by
  simp [lowerVal]

omit [Alphabet α] in
private lemma upperVal_succ_zero (w : Word α) (t : ℕ) :
    upperVal w (t + 1) 0 = lowerVal w t 0 := by
  simp [upperVal, lowerVal]

omit [Alphabet α] in
private lemma upperVal_succ_succ (w : Word α) (t i : ℕ) :
    upperVal w (t + 1) (i + 1) = upperVal w t i := by
  unfold upperVal
  by_cases h : i + 1 ≤ t
  · rw [if_pos h, if_pos (show i + 1 + 1 ≤ t + 1 from by omega)]
    have : (t + 1) - 1 - (i + 1) = t - 1 - i := by omega
    rw [this]
  · rw [if_neg h, if_neg (show ¬ i + 1 + 1 ≤ t + 1 from by omega)]

omit [Alphabet α] in
private lemma lowerVal_succ (w : Word α) (t i : ℕ) :
    lowerVal w (t + 1) i = lowerVal w t (i + 1) := by
  unfold lowerVal
  rw [show t + 1 + i = t + (i + 1) from by ring]

omit [Alphabet α] in
/-- For an in-range index `k = (n - 1)` the lower track has run off the
    right edge: `lowerVal w (t + 1) (n - 1) = none`. -/
private lemma lowerVal_at_right_edge (w : Word α) (t : ℕ) (hn : 1 ≤ w.length) :
    lowerVal w (t + 1) (w.length - 1) = none := by
  unfold lowerVal
  apply List.getElem?_eq_none
  omega

omit [Alphabet α] in
/-- For `k = 0` and `n = 1`, the lower track at `t + 1` is `none`. -/
private lemma lowerVal_singleton (w : Word α) (t : ℕ) (hn : w.length = 1) :
    lowerVal w (t + 1) 0 = none := by
  unfold lowerVal
  apply List.getElem?_eq_none
  omega

/-! ### Initial configuration -/

omit [Alphabet α] in
private lemma stateAt_zero (w : Word α) (i : ℤ) :
    stateAt w 0 i = embed (⟬w⟭ i) := by
  by_cases h : 0 ≤ i ∧ i < (w.length : ℤ)
  · -- Inner cell: lower has `w[i]`, upper is blank.
    have hi_w : i ≥ 0 ∧ i < w.length := ⟨h.1, h.2⟩
    have h_toNat_lt : i.toNat < w.length := by
      have h_eq := Int.toNat_of_nonneg h.1
      have h2 : (i.toNat : ℤ) < (w.length : ℤ) := by rw [h_eq]; exact h.2
      exact_mod_cast h2
    rw [stateAt_inside w 0 i h, upperVal_zero, lowerVal_zero]
    show some (none, w[i.toNat]?) = embed (⟬w⟭ i)
    rw [show (⟬w⟭ : Config α？) i = some w[i.toNat] from by
      unfold word_to_config
      simp [hi_w]]
    show some (none, w[i.toNat]?) = some (none, some w[i.toNat])
    rw [List.getElem?_eq_getElem h_toNat_lt]
  · rw [stateAt_outside w 0 i h]
    have hi_w : ¬ (i ≥ 0 ∧ i < w.length) :=
      fun ⟨ha, hb⟩ => h ⟨ha, by exact_mod_cast hb⟩
    show none = embed (⟬w⟭ i)
    rw [show (⟬w⟭ : Config α？) i = none from by
      unfold word_to_config; simp [hi_w]]
    rfl

/-! ### Embedding matches `stateAt` at time 0 -/

private lemma embed_eq_stateAt_zero (w : Word α) (i : ℤ) :
    @CellAutomaton.embed_config _ _ (witnessCA α) ⟬w⟭ i = stateAt w 0 i := by
  show (witnessCA α).embed (⟬w⟭ i) = _
  rw [stateAt_zero]
  rfl

/-! ### One-step transition lemma

    Applying the local rule to `stateAt w t` yields `stateAt w (t + 1)`.
    Split on whether the cell is in range, and on which boundary case
    applies. -/

omit [Alphabet α] in
private lemma next_stateAt (w : Word α) (t : ℕ) (i : ℤ) :
    δ (stateAt w t (i - 1)) (stateAt w t i) (stateAt w t (i + 1)) =
      stateAt w (t + 1) i := by
  by_cases hi : 0 ≤ i ∧ i < (w.length : ℤ)
  · -- Inner cell at position `i`. Examine left and right neighbours.
    obtain ⟨hi0, hin⟩ := hi
    rw [stateAt_inside w t i ⟨hi0, hin⟩, stateAt_inside w (t + 1) i ⟨hi0, hin⟩]
    set k : ℕ := i.toNat with hk
    have hk_eq : (k : ℤ) = i := Int.toNat_of_nonneg hi0
    have hk_lt : k < w.length := by
      have : (k : ℤ) < (w.length : ℤ) := hk_eq ▸ hin
      exact_mod_cast this
    by_cases hL : 0 ≤ i - 1
    · -- Left neighbour is inner, so `k ≥ 1`.
      have hk_pos : 1 ≤ k := by
        have h1 : (1 : ℤ) ≤ i := by omega
        have h2 : (1 : ℤ) ≤ (k : ℤ) := hk_eq ▸ h1
        exact_mod_cast h2
      have hLin : 0 ≤ i - 1 ∧ i - 1 < (w.length : ℤ) := ⟨hL, by omega⟩
      have hL_toNat : (i - 1).toNat = k - 1 := by
        have heq : i - 1 = ((k - 1 : ℕ) : ℤ) := by omega
        rw [heq]; simp
      rw [stateAt_inside w t (i - 1) hLin, hL_toNat]
      -- Reusable upper-component equation: `upperVal w (t+1) k = upperVal w t (k-1)`.
      have hU : upperVal w (t + 1) k = upperVal w t (k - 1) := by
        have hk_succ : k - 1 + 1 = k := by omega
        rw [← hk_succ]
        exact upperVal_succ_succ w t (k - 1)
      by_cases hR : i + 1 < (w.length : ℤ)
      · -- Both neighbours inner: position `1 ≤ k ≤ n - 2`. Use `δ_interior`.
        have hRin : 0 ≤ i + 1 ∧ i + 1 < (w.length : ℤ) := ⟨by omega, hR⟩
        have hR_toNat : (i + 1).toNat = k + 1 := by
          have heq : i + 1 = ((k + 1 : ℕ) : ℤ) := by omega
          rw [heq]; simp
        rw [stateAt_inside w t (i + 1) hRin, hR_toNat, δ_interior]
        have hLow : lowerVal w (t + 1) k = lowerVal w t (k + 1) := lowerVal_succ w t k
        rw [hU, hLow]
      · -- Right neighbour is border: position `k = n - 1`. Use `δ_right_edge_inner`.
        push_neg at hR
        have hRout : ¬ (0 ≤ i + 1 ∧ i + 1 < (w.length : ℤ)) := by
          intro ⟨_, h2⟩; exact absurd h2 (not_lt.mpr hR)
        -- Show `k = w.length - 1` as a Nat equality.
        have hk_eq_n : k = w.length - 1 := by
          have hZ_le : (w.length : ℤ) ≤ (k : ℤ) + 1 := by rw [hk_eq]; exact hR
          have hZ_lt : (k : ℤ) < (w.length : ℤ) := hk_eq ▸ hin
          have hpos : 1 ≤ w.length := by
            have : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
            have : (1 : ℤ) ≤ (w.length : ℤ) := by linarith
            exact_mod_cast this
          have hnat : (k : ℤ) = ((w.length - 1 : ℕ) : ℤ) := by omega
          exact_mod_cast hnat
        rw [stateAt_outside w t (i + 1) hRout, δ_right_edge_inner]
        have hLow : lowerVal w (t + 1) k = none := by
          rw [hk_eq_n]
          exact lowerVal_at_right_edge w t (by omega)
        rw [hU, hLow]
    · -- Left neighbour is border: position `k = 0`.
      push_neg at hL
      have hi_zero : i = 0 := by omega
      have hk_zero : k = 0 := by simp [hk, hi_zero]
      have hLout : ¬ (0 ≤ i - 1 ∧ i - 1 < (w.length : ℤ)) := by
        intro ⟨h1, _⟩; omega
      rw [stateAt_outside w t (i - 1) hLout, hk_zero]
      -- Reusable upper-component equation: `upperVal w (t+1) 0 = lowerVal w t 0`.
      have hU : upperVal w (t + 1) 0 = lowerVal w t 0 := upperVal_succ_zero w t
      by_cases hR : i + 1 < (w.length : ℤ)
      · -- Right neighbour is inner: `n ≥ 2`. Use `δ_left_edge`.
        have hRin : 0 ≤ i + 1 ∧ i + 1 < (w.length : ℤ) := ⟨by omega, hR⟩
        have hR_toNat : (i + 1).toNat = 1 := by
          have heq : i + 1 = ((1 : ℕ) : ℤ) := by push_cast; omega
          rw [heq]; simp
        rw [stateAt_inside w t (i + 1) hRin, hR_toNat, δ_left_edge]
        -- Goal: `some (lowerVal w t 0, lowerVal w t 1) = some (upperVal w (t+1) 0, lowerVal w (t+1) 0)`.
        have hLow : lowerVal w (t + 1) 0 = lowerVal w t 1 := lowerVal_succ w t 0
        rw [hU, hLow]
      · -- Both neighbours border: `n = 1`. Use `δ_singleton`.
        push_neg at hR
        have hRout : ¬ (0 ≤ i + 1 ∧ i + 1 < (w.length : ℤ)) := by
          intro ⟨_, h2⟩; exact absurd h2 (not_lt.mpr hR)
        have hn1 : w.length = 1 := by
          have h1 : (k : ℤ) < (w.length : ℤ) := hk_eq ▸ hin
          have h2 : (i : ℤ) + 1 ≥ (w.length : ℤ) := hR
          have h3 : (k : ℤ) + 1 ≥ (w.length : ℤ) := by rw [hk_eq]; exact h2
          have h4 : (1 : ℤ) ≤ (w.length : ℤ) := by linarith
          have h5 : (w.length : ℤ) ≤ 1 := by
            have : (k : ℤ) = 0 := by exact_mod_cast hk_zero
            linarith
          have h6 : w.length = 1 := by
            have h7 : (w.length : ℤ) = 1 := by linarith
            exact_mod_cast h7
          exact h6
        rw [stateAt_outside w t (i + 1) hRout, δ_singleton]
        -- Goal: `some (lowerVal w t 0, none) = some (upperVal w (t+1) 0, lowerVal w (t+1) 0)`.
        have hLow : lowerVal w (t + 1) 0 = none := lowerVal_singleton w t hn1
        rw [hU, hLow]
  · -- Outside cell at position `i`: stays `none`.
    rw [stateAt_outside w t i hi, stateAt_outside w (t + 1) i hi, δ_none]

/-! ### Iterated state -/

/-- The configuration at time `t` matches `stateAt w t`. -/
private lemma nextt_eq_stateAt (w : Word α) (t : ℕ) :
    (witnessCA α).nextt (⦋⟬w⟭⦌) t = stateAt w t := by
  induction t with
  | zero =>
    funext i
    show @CellAutomaton.embed_config _ _ (witnessCA α) ⟬w⟭ i = stateAt w 0 i
    rw [embed_eq_stateAt_zero]
  | succ t ih =>
    funext i
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply, ih]
    exact next_stateAt w t i

/-! ### Specialisation at `t = w.length` -/

omit [Alphabet α] in
private lemma upperVal_at_length (w : Word α) (i : ℕ) (hi : i < w.length) :
    upperVal w w.length i = some w[w.length - 1 - i] := by
  unfold upperVal
  rw [if_pos (show i + 1 ≤ w.length from hi)]
  exact List.getElem?_eq_getElem (by omega)

private lemma project_at_length (w : Word α) (i : ℕ) (hi : i < w.length) :
    project (some (upperVal w w.length i, lowerVal w w.length i)) =
      w[w.length - 1 - i] := by
  rw [upperVal_at_length w i hi]
  rfl

end RevAdvice

/-! ## Main theorem: reversal is an `n`-time advice -/

/-- **Reversal is an `n`-time advice.**

    The witness CA `RevAdvice.witnessCA α` carries two tracks at every
    inner cell — the upper one moves rightward, the lower one moves
    leftward — and reflects the lower track onto the upper track at the
    left edge. After `n = |w|` steps cell `i` carries `w[n − 1 − i]` on
    the upper track, i.e. the `i`-th symbol of `rev w`. -/
def Advice.rev_is_time_advice :
    (Advice.rev α).IsTimeAdvice (fun n => n) where
  C := RevAdvice.witnessCA α
  spec w := by
    show w.reverse = (List.range w.length).map
      (fun (i : ℕ) =>
        (RevAdvice.witnessCA α).comp (⦋⟬w⟭⦌) w.length (i : ℤ))
    apply List.ext_getElem
    · simp
    · intro i hi _
      have hi_w : i < w.length := by simpa using hi
      -- LHS: `(w.reverse)[i] = w[n - 1 - i]`.
      rw [List.getElem_reverse]
      simp only [List.getElem_map, List.getElem_range]
      -- Compute the witness state at `(t = n, p = i)`.
      show w[w.length - 1 - i]'(by omega) =
        (RevAdvice.witnessCA α).project
          ((RevAdvice.witnessCA α).nextt (⦋⟬w⟭⦌) w.length (i : ℤ))
      rw [RevAdvice.nextt_eq_stateAt]
      have hi_int : 0 ≤ (i : ℤ) ∧ (i : ℤ) < (w.length : ℤ) :=
        ⟨Int.natCast_nonneg i, by exact_mod_cast hi_w⟩
      rw [RevAdvice.stateAt_inside w w.length (i : ℤ) hi_int]
      have hi_toNat : (i : ℤ).toNat = i := by simp
      rw [hi_toNat]
      exact (RevAdvice.project_at_length w i hi_w).symm

end CellularAutomatas
