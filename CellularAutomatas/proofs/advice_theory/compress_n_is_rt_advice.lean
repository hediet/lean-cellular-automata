/-
  # `compress_n` is rt-advice

  For every `k ≥ 2`, the width-`k` compression advice
  `compress_n k : Advice α (Fin k → Option α)` is an rt-advice.

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

  At `t = n − 1`, slot `j` is filled iff `(k−1)·i + j ≤ n − 2`. Slots `j`
  with `(k−1)·i + j ≥ n − 1` are still `none`, but for those we have
  `k·i + j ≥ (k−1)·i + j + i ≥ n − 1 + i ≥ n` (using `i ≥ 1` when `n ≥ 2`),
  so `w[k·i + j]? = none` anyway and the bag value matches.

  Subtle case: `i = 0`. Then slot `j` is filled iff `j < t`. At
  `t = n − 1`, slots `0..n-2` are filled with `w[j]?`, slot `n − 1`
  (and onwards, for `k > n`) is still `none` while `w[k·0 + j]? = w[j]?`
  may be `some` — but this only happens when `j ≥ n - 1` and so
  `w[j]? = none`. ✓
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

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

end CompressNRt

end CellularAutomatas
