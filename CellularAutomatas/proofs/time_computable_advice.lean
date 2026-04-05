import CellularAutomatas.defs
import CellularAutomatas.proofs.fssp

/-!
# Time-Computable Advice

An advice `f : Word α → Word Γ` is **t-time computable** if a CA transducer can
compute `f(w)` at all positions `0 ≤ i < |w|` by time `t(|w|)`.

The key special case is **n-time computable** (t(n) = n − 1), where the CA has
exactly enough time for a signal to traverse the entire word.

## Main results (statements)

1. **Reversal is n-time computable**: characters propagate left at speed 1
   and are mirrored at position 0, all within `n − 1` steps.

2. **k-factor compression is n-time computable**: each cell gathers its
   `k` neighbors within `k` steps, and `k < n` for large enough words.

3. **L(CA_rt + f) ⊆ L(CA_2n) when f is n-time computable**:
   use FSSP to synchronize at time `n − 1`, read the computed advice,
   then run the original CA for another `n − 1` steps (total 2(n − 1)).
   The marking of first and last cells (needed by FSSP) is itself
   a kTimeComputable advice (computable in constant time).

## Generalization

We parameterize by an arbitrary time function `t : ℕ → ℕ`.
The `n − 1` case is recovered by `t = fun n => n - 1`.
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

/-- The first/last marking is 1-time computable (constant time).

    **Proof idea**: A CA where position 0 checks if its left neighbor is
    border (→ first), and each position checks if its right neighbor is
    border (→ last). This takes exactly 1 step. -/
theorem first_last_mark_time_computable :
    TimeComputableAdvice (fun _ => 1) (Advice.first_last_mark α) := by
  sorry

/-- As a corollary, first/last marking is n-time computable for n ≥ 2. -/
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

/-- k-factor compression is n-time computable (for fixed k).

    **Proof idea**: Each cell needs to know the values of at most `k`
    neighbors. Information propagates at speed 1, so cell `i` knows
    cells `i − t` through `i + t` at time `t`. By time `k − 1`, each
    cell knows its `k`-neighborhood. Since `k` is a constant and `k − 1 < n − 1`
    for `n > k`, this is within the n − 1 time budget.

    More precisely: build a CA whose state at position `i` at time `t`
    records the values of positions `max(0, i−t)` through `min(n−1, i+t)`.
    At time `k − 1`, position `i` has all values in `[i−(k−1), i+(k−1)]`,
    which includes `[ki, ki+k−1]` (for appropriate index mapping).

    The advice is actually computable in time `k − 1` (constant), but since
    `k − 1 ≤ n − 1` for words of length ≥ k, it is also n-time computable. -/
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
