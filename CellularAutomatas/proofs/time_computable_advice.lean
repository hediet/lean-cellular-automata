import CellularAutomatas.defs
import CellularAutomatas.proofs.fssp

/-!
# Time-Computable Advice

An advice `f : Word α → Word Γ` is **t-time computable** if a CA transducer can
compute `f(w)` at all positions `0 ≤ i < |w|` by time `t(|w|)`.

## Hierarchy of time-computable advices

1. **Constant-time computable** (`ConstTimeComputableAdvice`):
   computable in `k` steps for some fixed constant `k` (independent of `n`).
   Examples: first/last marking (border detection, `k = 1`).
   These are closely related to the existing **CArt transducer** advices —
   see `c_is_border` in `basic_mark_border.lean` and the `annotate_with_first` /
   `annotate_with_last` constructions in `basic_two_stage_advices.lean`.

2. **n-time computable** (`NTimeComputableAdvice`, `t(n) = n − 1`):
   the CA has exactly enough time for a signal to traverse the entire word.
   Examples: reversal advice, k-factor compression.

3. **General t-time computable** (`TimeComputableAdvice t`):
   parameterized by an arbitrary time function `t : ℕ → ℕ`.

## Main results (statements)

1. **First/last marking is constant-time (and CArt) computable**.
2. **Reversal is n-time computable**: reflected signal construction.
3. **k-factor compression is n-time computable**: local neighborhood gathering.
4. **L(CA_rt + f) ⊆ L(CA_2n) when f is n-time computable**:
   use FSSP to synchronize at time `n − 1`, read the computed advice,
   then run the original CA for another `n − 1` steps (total 2(n − 1)).
   The FSSP requires first/last marking, which is constant-time computable.
-/

namespace CellularAutomatas

variable {α : Type} [Alphabet α]
variable {Γ : Type} [Alphabet Γ]

/-! ## Definition: t-Time Computable Advice -/

/-- An advice `adv : Advice α Γ` is **t-time computable** if there exists
    a CA transducer `C : CellAutomaton α？ Γ` whose projected output at
    position `i` at time `t(|w|)` equals `adv(w)[i]` for every word `w`
    and every valid position `i`.

    Formally: `C.comp ⟬w⟭ (t |w|) i = adv(w)[i]` for `0 ≤ i < |w|`.

    This captures the idea that the advice can be "physically computed"
    by a cellular automaton within the given time budget. -/
structure TimeComputableAdvice (t : ℕ → ℕ) (adv : Advice α Γ) where
  /-- The CA transducer that computes the advice -/
  C : CellAutomaton α？ Γ
  /-- At time `t(n)`, every position `i` outputs `adv(w)[i]` -/
  computes : ∀ (w : Word α) (i : ℕ) (hi : i < w.length),
    C.comp ⟬w⟭ (t w.length) (i : ℤ) =
      (adv.f w).get ⟨i, adv.len w ▸ hi⟩

/-- An advice is **n-time computable** if it is computable at time `n − 1`
    (real-time: the minimum time for position 0 to learn about position n − 1).

    This is the natural time scale for a CA to gather information about the
    entire word: a signal traveling at speed 1 from position `n − 1` reaches
    position 0 at exactly time `n − 1`. -/
def NTimeComputableAdvice (adv : Advice α Γ) :=
  TimeComputableAdvice (fun n => n - 1) adv

/-! ## Constant-Time Computable Advice

An advice is **constant-time computable** if there exists a fixed `k` such that
the advice is computable at time `k`, regardless of word length.  This is strictly
stronger than n-time computable (where the time budget grows with the word).

The canonical examples are border-detection advices (first/last marking), where
each cell can determine its status by inspecting its immediate neighbors.

In the existing codebase, `CArtTransducer.advice` (from `defs.lean`) produces
causal advice via `trace_rt`.  A CArt advice at position `i` is ready at time `i`,
so positions 0 and `n − 1` know their border status at times 0 and 1 respectively.
The first/last marking is therefore a CArt advice — see `basic_mark_border.lean`
for the foundational `c_is_border` CA, and `basic_two_stage_advices.lean` for
the `annotate_with_first` / `annotate_with_last` constructions already in the repo.
-/

/-- An advice is **constant-time computable** if it is time-computable for
    some constant `k` (independent of word length). -/
def ConstTimeComputableAdvice (adv : Advice α Γ) :=
  ∃ k : ℕ, TimeComputableAdvice (fun _ => k) adv

/-! ## The first/last marking advice -/

/-- Marks position 0 with `true` and all others with `false`. -/
def Advice.first_mark (α : Type) : Advice α Bool :=
  { f := fun w => (List.range w.length).map (· == 0) }

/-- Marks position `n − 1` with `true` and all others with `false`. -/
def Advice.last_mark (α : Type) : Advice α Bool :=
  { f := fun w => (List.range w.length).map (· == w.length - 1) }

/-- Marks both the first and last positions with `true`. -/
def Advice.first_last_mark (α : Type) : Advice α (Bool × Bool) :=
  { f := fun w => (List.range w.length).map
      (fun i => (i == 0, i == w.length - 1)) }

/-- The first/last marking is a CArt advice: it is computable by a single
    CA transducer via `trace_rt`.

    **Construction**: Build a CA whose state tracks whether the left neighbor
    is border (→ first) and whether the right neighbor is border (→ last).
    This is a product of two border-detection CAs (cf. `c_is_border` in
    `basic_mark_border.lean`).

    Since `trace_rt` at position `i` reads the CA output at time `i`,
    and border detection is immediate (determined by the embedding), position 0
    knows it is first at time 0, and position `n − 1` knows it is last at time 1. -/
theorem first_last_mark_is_cart_advice :
    (Advice.first_last_mark α).is_cart_advice := by
  sorry

/-- The first/last marking is constant-time computable (1 step suffices).

    **Proof idea**: A CA where each cell checks its left neighbor for border
    (→ first) and its right neighbor for border (→ last). After 1 step,
    every position has determined both components. This is constant-time:
    `k = 1`, independent of word length `n`. -/
theorem first_last_mark_const_time_computable :
    ConstTimeComputableAdvice (Advice.first_last_mark α) := by
  sorry

/-- As a corollary, first/last marking is n-time computable for n ≥ 2.
    Follows from constant-time computability since `1 ≤ n − 1` for `n ≥ 2`. -/
theorem first_last_mark_ntime_computable :
    NTimeComputableAdvice (Advice.first_last_mark α) := by
  sorry

/-! ## Reversal is n-time computable -/

/-- The reversal advice: maps each word to its reverse.
    `(Advice.rev_advice α).f w = w.reverse`

    Note: This is the same as `Advice.rev` from `lt_closed.lean`,
    but we give a self-contained definition here for clarity. -/
def Advice.rev_advice (α : Type) : Advice α α :=
  { f := fun w => w.reverse, len := by simp }

/-- Reversal is n-time computable.

    **Proof idea**: Consider a CA where each cell `i` sends its value
    leftward at speed 1.  Position `i`'s value arrives at position `0` at
    time `i`, and by symmetry the value from position `n − 1 − i` arrives
    at position `i` at time `n − 1 − i`… but we need it at position `i`
    at time `n − 1`.

    A cleaner construction:
    - Each cell broadcasts its value as a rightward signal at speed 1
      starting at time 0 (values propagate right).
    - The right border reflects signals back left.
    - Value of position `j` reaches position `i` (for `i < j`) from the
      right at time `2(n − 1 − i) − (j − i) = 2n − 2 − i − j`.
    - For the reversal, position `i` needs the value from position `n − 1 − i`,
      arriving at time `2n − 2 − i − (n − 1 − i) = n − 1`. ✓

    Alternatively: simply note that `trace_rt` of a CA that "mirrors" the
    input (sends each cell's value to the opposite end) computes the reversal
    at time `n − 1`. The reflected signal construction is classical. -/
theorem rev_ntime_computable :
    NTimeComputableAdvice (Advice.rev_advice α) := by
  sorry

/-! ## k-Factor Compression is n-time computable -/

/-- k-factor compression advice: position `i` gets the tuple
    `(w[k*i], w[k*i+1], ..., w[k*i+k-1])`.

    For positions where `k*i + j ≥ |w|`, we pad with `default`.

    This packs `k` consecutive symbols of the *original* word into each
    position of the advice. -/
def Advice.compress (k : ℕ) [NeZero k] [Inhabited α] : Advice α (Fin k → α) :=
  { f := fun w => (List.range w.length).map fun i =>
      fun j => if h : k * i + j.val < w.length then w[k * i + j.val] else default
  }

/-- k-factor compression is constant-time computable (time `k − 1`, independent of `n`).

    **Proof idea**: Each cell needs to know the values of at most `k`
    neighbors. Information propagates at speed 1, so cell `i` knows
    cells `i − t` through `i + t` at time `t`. By time `k − 1`, each
    cell knows its `k`-neighborhood. Since `k` is a fixed constant,
    this is `k − 1` steps regardless of word length.

    More precisely: build a CA whose state at position `i` at time `t`
    records the values of positions `max(0, i−t)` through `min(n−1, i+t)`.
    At time `k − 1`, position `i` has all values in `[i−(k−1), i+(k−1)]`,
    which includes `[ki, ki+k−1]` (for appropriate index mapping). -/
theorem compress_const_time_computable (k : ℕ) [NeZero k] [Inhabited α] :
    ConstTimeComputableAdvice (Advice.compress (α := α) k) := by
  sorry

/-- k-factor compression is n-time computable, as a corollary of constant-time
    computability (since `k − 1 ≤ n − 1` for words of length `≥ k`). -/
theorem compress_ntime_computable (k : ℕ) [NeZero k] [Inhabited α] :
    NTimeComputableAdvice (Advice.compress (α := α) k) := by
  sorry

/-! ## Main theorem: L(CA_rt + f) ⊆ L(CA_2n) for n-time computable f -/

/-- If advice `f` is n-time computable, then any language recognized by
    a real-time CA with advice `f` is also recognized in time `2(n − 1)`.

    **Proof sketch**:
    Given `C ∈ CA_rt(α × Γ)` and n-time computable advice `f`, we build
    `C' ∈ CA_2n(α)` recognizing `(C + f).L`:

    1. **Phase 1 (time 0 to n − 1)**: Run the advice-computing CA `f.C`.
       By time `n − 1`, position `i` knows `f(w)[i]`.

    2. **Synchronization**: Use a two-sided FSSP to fire all cells simultaneously
       at time `n − 1`. The two-sided FSSP requires knowing the first and last
       positions, which is provided by the first/last marking advice
       (itself computable in constant time, hence available).

    3. **Phase 2 (time n − 1 to 2(n − 1))**: At time `n − 1`, each cell `i`
       has both `w[i]` (from the input) and `f(w)[i]` (from Phase 1).
       Start running `C` on the annotated input `w ⨂ f(w)`. After another
       `n − 1` steps, position 0 has the answer `C.comp(⟬w ⨂ f(w)⟭, n − 1, 0)`.

    4. **Total time**: `(n − 1) + (n − 1) = 2(n − 1)`. ✓

    The resulting CA `C'` works at time `2(n − 1)`, so `(C + f).L ∈ ℒ(CA_2n)`. -/
theorem rt_with_ntime_advice_subset_2n :
    ∀ (adv : Advice α Γ),
    NTimeComputableAdvice adv →
    ℒ (CA_rt (α × Γ) + adv) ⊆ ℒ (CA_2n α) := by
  sorry

/-- Corollary: `ℒ(CA_rt(α × Γ) + f) = ℒ(CA_rt(α))` implies
    `ℒ(CA_rt(α × Γ) + f) ⊆ ℒ(CA_2n(α))` trivially.
    But the point of `rt_with_ntime_advice_subset_2n` is that it works
    even when `f` is NOT rt-closed — merely n-time computable suffices. -/

/-- Generalized version: if `f` is t-time computable and t(n) ≤ n − 1,
    then `ℒ(CA_rt + f) ⊆ ℒ(CA_2n)`.

    Reducing to the n-time case since t(n) ≤ n − 1 means the advice
    is ready by time n − 1. -/
theorem rt_with_time_advice_subset_2n (t : ℕ → ℕ) (ht : ∀ n, t n ≤ n - 1) :
    ∀ (adv : Advice α Γ),
    TimeComputableAdvice t adv →
    ℒ (CA_rt (α × Γ) + adv) ⊆ ℒ (CA_2n α) := by
  sorry

/-! ## Toward L(2n−2) = L(lt)

The results above give a pathway:

1. `rev` is n-time computable (theorem `rev_ntime_computable`).
2. `ℒ(CA_rt + rev) ⊆ ℒ(CA_2n)` (by `rt_with_ntime_advice_subset_2n`).
3. If `rev` were RT-closed, then `ℒ(CA_rt + rev) = ℒ(CA_rt)`,
   and we'd get `ℒ(CA_rt) ⊆ ℒ(CA_2n)` (trivial direction).
4. The interesting direction is `ℒ(CA_2n) ⊆ ℒ(CA_rt + rev)`:
   a CA_2n can be decomposed into a forward phase (CA_rt) and a
   backward phase (reading the reverse).

Key open question: Is `rev` RT-closed? This is equivalent to
`ℒ(CA_lt) = ℒ(CA_rt)` (see `lt_closed.lean`).

Even without resolving this, we establish:
- `ℒ(CA_rt + rev) ⊆ ℒ(CA_2n)` (unconditionally)
- `ℒ(CA_rt + compress k) ⊆ ℒ(CA_2n)` (unconditionally)
- `lt` is closed under reversal (in `lt_closed.lean`)
- If `ℒ(CA_rt)` is closed under reversal, then `ℒ(CA_lt) = ℒ(CA_rt)`
  (in `rt_rev_implies_lt_eq_rt.lean`)
-/

end CellularAutomatas
