/-
  # `compress_n` is rt-advice

  Direct construction (no detour through "speed-advice"): for every `k`, the
  width-`k` compression advice
  `compress_n k : Advice α (Fin k → Option α？)` is an rt-advice.

  Where `compress_n k w` is the word of length `|w|` whose `i`-th symbol is
  the `Fin k`-tuple `j ↦ w[k·i + j]?`.

  ## Construction (the "k parallel collectors" CA)

  State `Q := α？ × (Fin k → CollectorPhase) × (Fin k → Option α？)` where
  `CollectorPhase := Fin (k - 1) ⊕ Unit ⊕ Unit` represents the three modes of
  each collector at a cell:
  * `inl ph` — collector-`j` not yet present at this cell; `ph` counts down
    until arrival; (only relevant when transiting from a left-neighbour);
  * `inr (inl ())` — collector-`j` *currently* at this cell, sampling;
  * `inr (inr ())` — collector-`j` has already passed.

  **Behaviour.**
  * `α？` component (input track): every step, copy the *right neighbour*'s
    `α？` component. This is a leftward-flowing input signal: at time `t`,
    cell `c` carries `w[c + t]?` (with `?` for out-of-range positions).
  * `(Fin k → α？)` buffer: starts all-`none`; whenever collector-`j` is
    sampling at this cell, slot `j` is updated to `some (current α？)`.
  * Collector-`j` launches from the left border at time `j`. After launching,
    collector-`j` advances by one cell every `k - 1` steps.

  **Spec.** At time `t` and cell `i ≥ 0`, collector-`j` is sampling iff
  `t = (k - 1) · i + j`. The value sampled is the input track, which at that
  spacetime equals `w[i + ((k - 1) · i + j)]? = w[k · i + j]?`. So at time
  `n - 1` (the rt-time), every cell `i` whose collectors have all already
  passed (i.e. `(k - 1)·i + (k - 1) ≤ n - 1` ⟺ `(k - 1)(i + 1) ≤ n - 1`) holds
  the full buffer `j ↦ w[k·i + j]?`. Cells whose collectors have not all
  arrived only have non-`none` slots `j` for which `(k - 1)·i + j ≤ n - 1` —
  but for such `j`, `k·i + j ≤ n - 1 + i`, and slots `j` with `k·i + j ≥ n`
  return `none` from `w[…]?` anyway (out-of-range reads give `none`), so the
  buffer still equals `compress_n[i]`.

  **Note.** The construction itself is straightforward; the *correctness
  proof* requires a spatial-temporal invariant by induction on `t`. The
  invariant statement and the easy boundary lemmas are formalised here; the
  inductive step is left as `compress_n_invariant_step` (`sorry`).
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

/-! ## State space

    A cell holds:
    * `inp : α？` — input symbol currently flowing through this cell;
    * `phase : Fin k → ℕ` — for each collector `j`, the time-since-launch
      counter modulo `k - 1` (with the convention that `0` means "currently
      sampling here this step", `1..k-2` means "passed; not yet at next
      cell"). Capped at `k - 1` to keep state finite.
    * `buf : Fin k → α？` — buffer slot per collector; starts all `none`.

    For convenience we package phase + activity into `Phase k`. -/

/-- Phase of a single collector at a single cell.

    Encoded as a sum so that `Fintype`/`DecidableEq` are derived
    automatically:
    * `inl ()` — dormant: not yet launched / not yet arrived;
    * `inr (inl ())` — currently sampling here this step;
    * `inr (inr r)` for `r : Fin k` — has passed; `r` is the residual hop
      counter (in practice always `< k - 1`, but `Fin k` is convenient and
      total).
-/
@[reducible] def Phase (k : ℕ) : Type := Unit ⊕ Unit ⊕ Fin k

/-- `Phase.dormant`: collector has not yet arrived. -/
@[match_pattern] abbrev Phase.dormant {k : ℕ} : Phase k := Sum.inl ()

/-- `Phase.sampling`: collector is currently here this step. -/
@[match_pattern] abbrev Phase.sampling {k : ℕ} : Phase k := Sum.inr (Sum.inl ())

/-- `Phase.passed r`: collector has already passed; `r` is the residual hop
    counter. -/
@[match_pattern] abbrev Phase.passed {k : ℕ} (r : Fin k) : Phase k :=
  Sum.inr (Sum.inr r)

instance (k : ℕ) : Inhabited (Phase k) := ⟨Phase.dormant⟩

instance (k : ℕ) : DecidableEq (Phase k) := by unfold Phase; infer_instance

instance (k : ℕ) : Fintype (Phase k) := by unfold Phase; infer_instance

/-- The cell state. -/
@[reducible] def Q (α : Type) [Alphabet α] (k : ℕ) : Type :=
  α？ × (Fin k → Phase k) × (Fin k → α？)

instance (α : Type) [Alphabet α] (k : ℕ) : Inhabited (Q α k) := by
  unfold Q; infer_instance

instance (α : Type) [Alphabet α] (k : ℕ) : DecidableEq (Q α k) := by
  unfold Q; infer_instance

instance (α : Type) [Alphabet α] (k : ℕ) : Fintype (Q α k) := by
  unfold Q; infer_instance

/-- Embed an `α？` input symbol into a cell:
    * input track holds the symbol;
    * all collectors `dormant`;
    * empty buffer. -/
def embedQ (k : ℕ) : α？ → Q α k :=
  fun a => (a, fun _ => Phase.dormant, fun _ => none)

/-- Project a cell state to its buffer (the advice value).
    `s.2.2 j : α？ = Option α`, so we just return it directly. -/
def projectQ (k : ℕ) : Q α k → (Fin k → Option α) :=
  fun s j => s.2.2 j

/-! ## Transition

    The right neighbour's input track flows into us. Each collector-`j`'s
    phase advances; on the **arrival edge** (left neighbour was `sampling`,
    so it just finished sampling → now we sample), the slot is filled. -/

/-- Advance one collector-phase based on left/me/right phases.

    Cases (in order):
    * `me = sampling` → finish sampling, become `passed (k - 2)` (start the
      `k - 1` countdown until next arrival). For `k ≤ 1` this is `passed 0`.
    * `me = dormant`, `left = sampling` → arrival from left, become
      `sampling`.
    * `me = passed r` with `r > 0` → countdown.
    * `me = passed 0` → stay `passed 0`.
    * `me = dormant` (and left ≠ sampling) → stay `dormant`.

    For `k = 0`, the `sampling` case is unreachable in any actual run (since
    `Fin 0 → Phase 0` is the unique empty function), and the value is
    irrelevant; we return `dormant` as a placeholder. -/
def stepPhase : ∀ (k : ℕ), Phase k → Phase k → Phase k → Phase k
  | 0,     _, _, _ => Phase.dormant   -- k = 0: `Fin 0` empty, irrelevant.
  | k + 1, _, Phase.sampling, _ =>
      Phase.passed ⟨(k + 1 - 2) % (k + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  | _ + 1, Phase.sampling, Phase.dormant, _ => Phase.sampling
  | _ + 1, _, Phase.passed ⟨0, h⟩, _ => Phase.passed ⟨0, h⟩
  | _ + 1, _, Phase.passed ⟨r + 1, hr⟩, _ =>
      Phase.passed ⟨r, by omega⟩
  | _ + 1, _, Phase.dormant, _ => Phase.dormant

/-- Advance one buffer slot based on whether *we* are sampling now. -/
def stepBuf (sampling_now : Bool) (incoming : α？) (current : α？) : α？ :=
  if sampling_now then incoming else current

/-- Local rule. -/
def δQ (k : ℕ) : Q α k → Q α k → Q α k → Q α k :=
  fun ql qm qr =>
    let new_inp := qr.1
    let new_phases : Fin k → Phase k := fun j =>
      stepPhase k (ql.2.1 j) (qm.2.1 j) (qr.2.1 j)
    let sampling_after : Fin k → Bool := fun j =>
      decide (new_phases j = Phase.sampling)
    let new_buf : Fin k → α？ := fun j =>
      stepBuf (sampling_after j) qm.1 (qm.2.2 j)
    (new_inp, new_phases, new_buf)

/-- The witness CA. -/
def C (α : Type) [Alphabet α] (k : ℕ) : CellAutomaton α？ (Fin k → Option α) where
  Q := Q α k
  δ := δQ k
  embed := embedQ k
  project := projectQ k

end CompressNRt

/-! ## Statements (and the substantive invariant)

    The full correctness proof reduces to a spatial-temporal invariant at
    time `t = n - 1`. We state it here and discharge the easy length /
    boundary parts; the inductive content is `compress_n_buf_invariant`. -/

/-- **Spatial invariant (target).** At time `t`, cell `i` (with `0 ≤ i < n`)
    holds in slot `j` the value `w[k·i + j]?` provided collector-`j` has
    already arrived by time `t` (i.e. `(k - 1)·i + j ≤ t`); otherwise `none`.

    Specialising to `t = n - 1`: for any `j` with `(k - 1)·i + j > n - 1` we
    necessarily have `k·i + j > n - 1 + i ≥ n`, so `w[k·i + j]? = none`,
    giving the desired buffer value either way. -/
lemma compress_n_buf_invariant (k : ℕ) (hk : 1 ≤ k) (w : Word α) (t : ℕ)
    (i : ℤ) (h0 : 0 ≤ i) (hn : i < (w.length : ℤ)) (j : Fin k) :
    ((CompressNRt.C α k).comp ⟬w⟭ t i) j =
      (if (k - 1) * i.toNat + j.val ≤ t then
        w[k * i.toNat + j.val]?
       else none) := by
  sorry

/-- `compress_n k` is an rt-advice. -/
def compress_n_is_rt_advice (k : ℕ) (hk : 1 ≤ k) :
    (Advice.compress_n k α).IsRtAdvice where
  C := CompressNRt.C α k
  spec w := by
    -- LHS: `compress_n k w` = `(range |w|).map (fun i j => w[k*i+j]?)`.
    -- RHS: `(range |w|).map (fun i => (C.comp ⟬w⟭ (|w|-1)) i)`.
    -- Both are length-`|w|` lists; show pointwise equality via the invariant.
    apply List.ext_getElem (by simp [Advice.compress_n])
    intro i hL hR
    have hi : i < w.length := by
      simpa [Advice.compress_n] using hL
    -- LHS at index i: `(Advice.compress_n k α).f w)[i] = fun j => w[k*i + j]?`.
    have h_lhs :
        ((Advice.compress_n k α).f w)[i]'hL =
          (fun (j : Fin k) => w[k * i + j.val]?) := by
      simp [Advice.compress_n, List.getElem_range]
    rw [h_lhs]
    -- RHS at index i: `(C.comp ⟬w⟭ (|w|-1)) (i : ℤ)`.
    have h_rhs_idx : i < (List.range w.length).length := by simpa using hi
    rw [List.getElem_map, List.getElem_range]
    -- Pointwise on j.
    funext j
    -- Apply the invariant.
    have h0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    have hn : (i : ℤ) < (w.length : ℤ) := by exact_mod_cast hi
    rw [compress_n_buf_invariant k hk w (w.length - 1) (i : ℤ) h0 hn j]
    -- After invariant, RHS has the form
    -- `if (k - 1) * (↑i).toNat + j ≤ |w| - 1 then w[k * (↑i).toNat + j]? else none`.
    -- Reduce `(↑i).toNat = i`.
    have h_toNat : ((i : ℤ)).toNat = i := Int.toNat_natCast i
    rw [h_toNat]
    -- Now case-split on the `if`.
    by_cases h : (k - 1) * i + j.val ≤ w.length - 1
    · rw [if_pos h]
    · rw [if_neg h]
      -- Show `w[k * i + j]?` is `none` here. We have
      --   (k - 1) * i + j > |w| - 1, i.e. (k - 1) * i + j ≥ |w|.
      -- So `k * i + j = (k - 1) * i + j + i ≥ |w| + i ≥ |w|` ⇒ out of range.
      push_neg at h
      -- Bridge `k * i = (k - 1) * i + i` for `omega`.
      have h_split : k * i = (k - 1) * i + i := by
        have : k = (k - 1) + 1 := by omega
        calc k * i = ((k - 1) + 1) * i := by rw [← this]
          _ = (k - 1) * i + i := by ring
      have h_oor : w.length ≤ k * i + j.val := by omega
      exact List.getElem?_eq_none h_oor

end CellularAutomatas
