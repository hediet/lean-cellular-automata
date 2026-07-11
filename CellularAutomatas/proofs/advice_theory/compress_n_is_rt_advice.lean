/-
  # `compress_n` is `n`-time advice

  For every `k ≥ 2`, the width-`k` compression advice
  `compress_n k : Advice α (Fin k → Option α)` is computable in time `n`.

  `compress_n k w` is the word of length `|w|` whose `i`-th symbol is the
  `Fin k`-tuple `j ↦ w[k·i + j]?`.

  ## Construction (lean state design)

  State `Q := α？ × (Fin k → α？)`:
  * `inp : α？` — input symbol currently passing through this cell;
  * `bag : Fin k → α？` — accumulator, fills monotonically from slot `0` to
    slot `k − 1`. Once a slot becomes `some _`, it stays that way.

  **Behaviour.**
  * `inp` shifts left every step: `new_inp = right.inp` (a leftward-flowing
    input wave; at time `t` an inner cell `i` carries `w[i + t]?`).
  * `bag` advances by one slot each step at cell `i` provided
    `left.bag[k-2] = some _` (i.e. left neighbour has filled at least `k-1`
    slots — equivalently, has *started* its last slot) and our own bag
    isn't yet full. The slot written gets the cell's *old* `inp` value.

  **Embedding (border / inner).**
  * `embed none = (none, fun _ => some default)` — borders carry a *full*
    bag of garbage. That makes `left.bag[k-2] = some _` always true at the
    left of cell `0`, so cell `0` starts firing immediately at `t = 0`.
    It also makes the *right* border permanently look "ahead" of cell
    `n − 1`, but that doesn't matter (cells past the right border aren't
    reached by the projection).
  * `embed (some _) = (some _, fun _ => none)` — inner cells start with an
    empty bag.

  ## Invariant

  At time `t`, for an inner cell `i ∈ [0, n)`:
  * `inp` = `w[i + t]?`;
  * `bag j` = `w[k·i + j]?` if slot `j` has been filled (i.e.
    `(k−1)·i + j < t`), else `none`.

  At `t = n`, slot `j` is filled iff `(k−1)·i + j < n`. Slots with
  `(k−1)·i + j ≥ n` are still `none`, but their source index `k·i + j`
  is also out of range. Thus every bag equals the corresponding symbol of
  `compress_n k w` at time `n`.

  The extra tick is necessary. For example, when `i = 0` and `n = k`, slot
  `k - 1` receives `w[k - 1]` only on tick `k`; at time `n - 1` it is still
  `none`.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.advice_theory.time_advice_combinators

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

open CellAutomaton

/-! ## `Advice.compress_n`

    Width-`k` compression: bundles the `k` input symbols starting at position
    `k · i` into a single advice symbol at position `i`. Out-of-range indices
    yield `none`.

    For `k = 2` this matches `Advice.compress2` up to the isomorphism
    `Fin 2 → Option α  ≃  Option α × Option α`. -/
def Advice.compress_n (k : ℕ) (α : Type) [Alphabet α] :
    Advice α (Fin k → Option α) where
  f := fun w =>
    (List.range w.length).map fun i => fun (j : Fin k) => w[k * i + j.val]?
  len := by intro w; simp

namespace CompressNRt

/-! ## State and transition. -/

/-- The cell state: input track + monotone bag. -/
abbrev Q (α : Type) [Alphabet α] (k : ℕ) : Type :=
  α？ × (Fin k → α？)

/-- Embed an `α？` input symbol into a cell state.
    * `none` (border) → full bag of `some default`, empty `inp`.
    * `some a` (inner) → empty bag, `inp = some a`. -/
def embedQ (k : ℕ) : α？ → Q α k
  | none      => (none,     fun _ => some default)
  | some a    => (some a,   fun _ => none)

/-- Project to the bag (the advice value). -/
def projectQ (k : ℕ) : Q α k → (Fin k → Option α) :=
  fun s => s.2

/-- The next bag, given old bag and whether we fire one slot this step.
    "Fire" advances the lowest `none` slot to `some incoming`. If the bag
    is already full, no change. -/
def stepBag (k : ℕ) (fire : Bool) (incoming : α？)
    (bag : Fin k → α？) : Fin k → α？ :=
  fun j =>
    if fire ∧ bag j = none ∧ ∀ j' : Fin k, j' < j → bag j' ≠ none
    then incoming
    else bag j

/-- Local rule. New `inp` = right's old `inp`. Bag advances iff left's
    slot `k-2` is `some` (i.e. left has filled at least `k-1` slots). -/
def δQ (k : ℕ) (hk : 2 ≤ k) : Q α k → Q α k → Q α k → Q α k :=
  fun ql qm qr =>
    let new_inp : α？ := qr.1
    let fire : Bool := decide (ql.2 ⟨k - 2, by omega⟩ ≠ none)
    let new_bag : Fin k → α？ := stepBag k fire qm.1 qm.2
    (new_inp, new_bag)

/-- The witness CA. -/
def C (α : Type) [Alphabet α] (k : ℕ) (hk : 2 ≤ k) :
    CellAutomaton α？ (Fin k → Option α) where
  Q := Q α k
  δ := δQ k hk
  embed := embedQ k
  project := projectQ k

/-! ## Evolution invariants. -/

/-- Expected bag at inner cell `i` and time `t`. A slot that has not yet
    been reached and a slot whose source lies past the input both contain
    `none`; this is exactly what makes failed writes harmless. -/
private def expectedBag (w : Word α) (k i t : ℕ) : Fin k → α？ :=
  fun j =>
    if (k - 1) * i + j.val < t then w[k * i + j.val]?
    else none

omit [Alphabet α] in
private lemma expectedBag_ne_none_iff (w : Word α) (k i t : ℕ) (j : Fin k) :
    expectedBag w k i t j ≠ none ↔
      (k - 1) * i + j.val < t ∧ k * i + j.val < w.length := by
  unfold expectedBag
  by_cases h_filled : (k - 1) * i + j.val < t
  · by_cases h_source : k * i + j.val < w.length
    · simp [h_filled, h_source]
    · simp [h_filled, h_source]
  · simp [h_filled]

/-- At time `t`, cell `i` may advance its bag either at the left border or
    once the predecessor cell's slot `k - 2` is nonempty. -/
private def fires (w : Word α) (k i t : ℕ) : Prop :=
  i = 0 ∨
    ((k - 1) * (i - 1) + (k - 2) < t ∧
      k * (i - 1) + (k - 2) < w.length)

omit [Alphabet α] in
private instance firesDecidable (w : Word α) (k i t : ℕ) :
    Decidable (fires w k i t) := by
  unfold fires
  infer_instance

omit [Alphabet α] in
private lemma predecessor_ne_none_iff_fires (w : Word α) (k : ℕ) (hk : 2 ≤ k)
    (i t : ℕ) (hi : i ≠ 0) :
    expectedBag w k (i - 1) t ⟨k - 2, by omega⟩ ≠ none ↔
      fires w k i t := by
  rw [expectedBag_ne_none_iff]
  simp [fires, hi]

private lemma predecessor_time_add_one (k i : ℕ) (hk : 2 ≤ k) (hi : i ≠ 0) :
    (k - 1) * (i - 1) + (k - 2) + 1 = (k - 1) * i := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  simp only [Nat.succ_sub_one, Nat.mul_succ]
  omega

private lemma predecessor_source_add_two (k i : ℕ) (hk : 2 ≤ k) (hi : i ≠ 0) :
    k * (i - 1) + (k - 2) + 2 = k * i := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  simp only [Nat.succ_sub_one, Nat.mul_succ]
  omega

private lemma input_index_at_fill (k i j : ℕ) (hk : 2 ≤ k) :
    i + ((k - 1) * i + j) = k * i + j := by
  calc
    i + ((k - 1) * i + j) = ((k - 1) + 1) * i + j := by ring
    _ = k * i + j := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]

/-- One local bag update advances exactly the next scheduled slot. If that
    slot is past the word, the incoming value is also `none`, so the bag
    remains unchanged and no later slot can acquire a spurious value. -/
private lemma step_expectedBag (w : Word α) (k : ℕ) (hk : 2 ≤ k)
    (t i : ℕ) (hi : i < w.length) (j : Fin k) :
    stepBag k (decide (fires w k i t)) w[i + t]? (expectedBag w k i t) j =
      expectedBag w k i (t + 1) j := by
  by_cases h_source : k * i + j.val < w.length
  · by_cases h_filled : (k - 1) * i + j.val < t
    · -- An in-range slot that was already filled cannot be overwritten.
      have h_bag_ne : expectedBag w k i t j ≠ none :=
        (expectedBag_ne_none_iff w k i t j).2 ⟨h_filled, h_source⟩
      have h_filled_next : (k - 1) * i + j.val < t + 1 := by omega
      unfold stepBag
      rw [if_neg (by intro h_write; exact h_bag_ne h_write.2.1)]
      simp [expectedBag, h_filled, h_filled_next]
    · by_cases h_reached : (k - 1) * i + j.val < t + 1
      · -- This is the unique tick at which slot `j` is first reached.
        have h_time : t = (k - 1) * i + j.val := by omega
        have h_fire : fires w k i t := by
          by_cases hi_zero : i = 0
          · exact Or.inl hi_zero
          · right
            have h_predecessor_time := predecessor_time_add_one k i hk hi_zero
            have h_predecessor_source := predecessor_source_add_two k i hk hi_zero
            constructor <;> omega
        have h_bag_none : expectedBag w k i t j = none := by
          simp [expectedBag, h_filled]
        have h_earlier_full :
            ∀ j' : Fin k, j' < j → expectedBag w k i t j' ≠ none := by
          intro j' hj'
          apply (expectedBag_ne_none_iff w k i t j').2
          constructor <;> omega
        have h_input_index : i + t = k * i + j.val := by
          calc
            i + t = i + ((k - 1) * i + j.val) := by rw [h_time]
            _ = k * i + j.val := input_index_at_fill k i j.val hk
        unfold stepBag
        rw [if_pos ⟨by simpa using h_fire, h_bag_none, h_earlier_full⟩]
        rw [h_input_index]
        simp [expectedBag, h_reached]
      · -- Before its scheduled tick, a slot cannot be skipped over.
        have h_bag_none : expectedBag w k i t j = none := by
          simp [expectedBag, h_filled]
        have h_next_none : expectedBag w k i (t + 1) j = none := by
          simp [expectedBag, h_reached]
        have h_no_write :
            ¬ (decide (fires w k i t) ∧
              expectedBag w k i t j = none ∧
              ∀ j' : Fin k, j' < j → expectedBag w k i t j' ≠ none) := by
          intro h_write
          by_cases hj_zero : j.val = 0
          · have hi_ne : i ≠ 0 := by
              intro hi_zero
              subst i
              omega
            have h_not_fire : ¬ fires w k i t := by
              intro h_fire
              rcases h_fire with h_zero | h_predecessor
              · exact hi_ne h_zero
              · have h_predecessor_time := predecessor_time_add_one k i hk hi_ne
                omega
            have h_fire : fires w k i t := by simpa using h_write.1
            exact h_not_fire h_fire
          · let previous : Fin k := ⟨j.val - 1, by omega⟩
            have h_previous_val : previous.val = j.val - 1 := rfl
            have h_previous_lt : previous < j := by
              change previous.val < j.val
              rw [h_previous_val]
              omega
            have h_previous_none : expectedBag w k i t previous = none := by
              unfold expectedBag
              rw [if_neg (by rw [h_previous_val]; omega)]
            exact h_write.2.2 previous h_previous_lt h_previous_none
        unfold stepBag
        rw [if_neg h_no_write, h_bag_none, h_next_none]
  · -- Values beyond the end remain `none`, including attempted writes.
    have h_lookup_none : w[k * i + j.val]? = none := by
      apply List.getElem?_eq_none
      omega
    have h_bag_none : expectedBag w k i t j = none := by
      simp [expectedBag, h_lookup_none]
    have h_next_none : expectedBag w k i (t + 1) j = none := by
      simp [expectedBag, h_lookup_none]
    unfold stepBag
    by_cases h_write :
        decide (fires w k i t) ∧
          expectedBag w k i t j = none ∧
          ∀ j' : Fin k, j' < j → expectedBag w k i t j' ≠ none
    · have h_source_reached : k * i + j.val ≤ i + t := by
        by_cases hj_zero : j.val = 0
        · have hi_ne : i ≠ 0 := by
            intro hi_zero
            subst i
            omega
          have h_fire : fires w k i t := by simpa using h_write.1
          rcases h_fire with h_zero | h_predecessor
          · exact absurd h_zero hi_ne
          · have h_predecessor_time := predecessor_time_add_one k i hk hi_ne
            have h_input_index := input_index_at_fill k i 0 hk
            omega
        · let previous : Fin k := ⟨j.val - 1, by omega⟩
          have h_previous_val : previous.val = j.val - 1 := rfl
          have h_previous_lt : previous < j := by
            change previous.val < j.val
            rw [h_previous_val]
            omega
          have h_previous_ne := h_write.2.2 previous h_previous_lt
          have h_previous_filled :=
            (expectedBag_ne_none_iff w k i t previous).1 h_previous_ne
          have h_input_index := input_index_at_fill k i j.val hk
          rw [h_previous_val] at h_previous_filled
          omega
      have h_incoming_none : w[i + t]? = none := by
        apply List.getElem?_eq_none
        omega
      rw [if_pos h_write, h_incoming_none, h_next_none]
    · rw [if_neg h_write, h_bag_none, h_next_none]

/-- Inner cells start with the expected empty bag. -/
private lemma bag_zero (w : Word α) (k : ℕ) (hk : 2 ≤ k)
    (i : ℕ) (hi : i < w.length) (j : Fin k) :
    ((C α k hk).nextt ⦋w⦌ 0 (i : ℤ)).2 j = expectedBag w k i 0 j := by
  simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply]
  rw [show word_to_config w (i : ℤ) = some w[i] from by
    unfold word_to_config
    simp [hi]]
  simp [C, embedQ, expectedBag]

omit [Alphabet α] in
private lemma word_to_config_nat (w : Word α) (i : ℕ) :
    word_to_config w (i : ℤ) = w[i]? := by
  by_cases hi : i < w.length
  · rw [word_to_config_apply, dif_pos]
    · simp [List.getElem?_eq_getElem hi]
    · constructor <;> omega
  · rw [word_to_config_apply, dif_neg]
    · rw [List.getElem?_eq_none (by omega)]
    · intro h_range
      apply hi
      exact_mod_cast h_range.2

/-- The input track shifts left by one cell per step. -/
private lemma inp_eq (w : Word α) (k : ℕ) (hk : 2 ≤ k)
    (t : ℕ) (p : ℤ) :
    ((C α k hk).nextt ⦋w⦌ t p).1 = word_to_config w (p + t) := by
  induction t generalizing p with
  | zero =>
      simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply]
      cases h : word_to_config w p <;> simp [C, embedQ, h]
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      change ((C α k hk).nextt ⦋w⦌ t (p + 1)).1 = _
      rw [ih]
      congr 1
      push_cast
      omega

/-- Every cell initially to the left of the word keeps a full bag. -/
private lemma left_bag_full (w : Word α) (k : ℕ) (hk : 2 ≤ k)
    (t : ℕ) (p : ℤ) (hp : p < 0) (j : Fin k) :
    ((C α k hk).nextt ⦋w⦌ t p).2 j = some default := by
  induction t with
  | zero =>
      simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config_apply]
      have h_none : word_to_config w p = none := by
        unfold word_to_config
        simp [hp]
      simp [C, embedQ, h_none]
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      change stepBag k _ _ ((C α k hk).nextt ⦋w⦌ t p).2 j = some default
      unfold stepBag
      rw [ih]
      simp

/-- Bag invariant for every cell belonging to the input word. -/
private lemma bag_eq (w : Word α) (k : ℕ) (hk : 2 ≤ k)
    (t i : ℕ) (hi : i < w.length) (j : Fin k) :
    ((C α k hk).nextt ⦋w⦌ t (i : ℤ)).2 j = expectedBag w k i t j := by
  induction t generalizing i j with
  | zero =>
      exact bag_zero w k hk i hi j
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
      change stepBag k
        (decide (((C α k hk).nextt ⦋w⦌ t ((i : ℤ) - 1)).2
          ⟨k - 2, by omega⟩ ≠ none))
        (((C α k hk).nextt ⦋w⦌ t (i : ℤ)).1)
        (((C α k hk).nextt ⦋w⦌ t (i : ℤ)).2) j =
          expectedBag w k i (t + 1) j
      rw [inp_eq w k hk t (i : ℤ)]
      rw [show (i : ℤ) + (t : ℤ) = ((i + t : ℕ) : ℤ) by omega]
      rw [word_to_config_nat]
      have h_current_bag :
          ((C α k hk).nextt ⦋w⦌ t (i : ℤ)).2 = expectedBag w k i t := by
        funext slot
        exact ih i hi slot
      rw [h_current_bag]
      by_cases hi_zero : i = 0
      · subst i
        rw [show ((0 : ℕ) : ℤ) - 1 = -1 by omega]
        rw [left_bag_full w k hk t (-1) (by omega) ⟨k - 2, by omega⟩]
        simpa [fires] using step_expectedBag w k hk t 0 hi j
      · rw [show (i : ℤ) - 1 = ((i - 1 : ℕ) : ℤ) by omega]
        rw [ih (i - 1) (by omega) ⟨k - 2, by omega⟩]
        have h_fire_iff := predecessor_ne_none_iff_fires w k hk i t hi_zero
        by_cases h_fire : fires w k i t
        · have h_predecessor_ne := h_fire_iff.2 h_fire
          simpa [h_fire, h_predecessor_ne] using
            step_expectedBag w k hk t i hi j
        · have h_predecessor_not_ne :
              ¬ expectedBag w k (i - 1) t ⟨k - 2, by omega⟩ ≠ none :=
            fun h_ne => h_fire (h_fire_iff.1 h_ne)
          simpa [h_fire, h_predecessor_not_ne] using
            step_expectedBag w k hk t i hi j

omit [Alphabet α] in
/-- At time `|w|`, every source that exists has reached its slot; sources
    that do not exist are represented by `none` on both sides. -/
private lemma expectedBag_at_length (w : Word α) (k : ℕ) (hk : 2 ≤ k)
    (i : ℕ) (j : Fin k) :
    expectedBag w k i w.length j = w[k * i + j.val]? := by
  by_cases h_source : k * i + j.val < w.length
  · have h_index := input_index_at_fill k i j.val hk
    have h_filled : (k - 1) * i + j.val < w.length := by omega
    simp [expectedBag, h_filled]
  · have h_none : w[k * i + j.val]? = none := by
      apply List.getElem?_eq_none
      omega
    unfold expectedBag
    split <;> simp [h_none]

end CompressNRt

/-! ## Main theorem. -/

/-- Width-`k` compression is computable as spatial advice at time `n` for
    every `k ≥ 2`. -/
def Advice.compress_n_is_n_time_advice (k : ℕ) (hk : 2 ≤ k) :
    (Advice.compress_n k α).IsTimeAdvice (fun n => n) where
  C := CompressNRt.C α k hk
  spec w := by
    show (List.range w.length).map
        (fun i => fun j : Fin k => w[k * i + j.val]?) =
      (List.range w.length).map
        (fun (i : ℕ) =>
          (CompressNRt.C α k hk).comp (⦋⟬w⟭⦌) w.length (i : ℤ))
    apply List.ext_getElem
    · simp
    · intro i hi _
      have hi_w : i < w.length := by simpa using hi
      simp only [List.getElem_map, List.getElem_range]
      funext j
      show w[k * i + j.val]? =
        ((CompressNRt.C α k hk).nextt ⦋w⦌ w.length (i : ℤ)).2 j
      rw [CompressNRt.bag_eq w k hk w.length i hi_w j]
      exact (CompressNRt.expectedBag_at_length w k hk i j).symm

/-! ## Width two as the existing pair advice. -/

/-- Convert a width-two functional block to the pair representation used by
    `Advice.compress2`. -/
def Advice.block2ToPair (block : Fin 2 → Option α) : Option α × Option α :=
  (block 0, block 1)

/-- The existing pair-valued `compress2` advice is available at time `n`. -/
def Advice.compress2_is_n_time_advice :
    (Advice.compress2 α).IsNTimeAdvice :=
  let mapped :=
    (Advice.compress_n_is_n_time_advice (α := α) 2 (by omega)).map
      Advice.block2ToPair
  { C := mapped.C
    spec := fun w => by
      calc
        Advice.compress2 α w
            = Advice.map Advice.block2ToPair (Advice.compress_n 2 α) w := by
              simp [Advice.compress2, Advice.compress_n, Advice.block2ToPair]
        _ = (List.range w.length).map
              (fun (i : ℕ) => mapped.C.comp ⟬w⟭ w.length (i : ℤ)) :=
          mapped.spec w }

end CellularAutomatas
