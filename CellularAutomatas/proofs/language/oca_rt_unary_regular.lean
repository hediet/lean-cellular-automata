/-
  # Unary Slices of OCA_rt Languages are Regular

  Main results:
  - `oca_rt_unary_slice_regular`:
      For any alphabet `α` and any letter `a : α`, every unary slice
      `unarySlice a L` of an `OCA_rt α` language `L` is regular.
  - `oca_rt_unary_regular` (corollary):
      Every language `L ∈ ℒ(OCA_rt Unit)` is regular (since over `Unit`,
      every word equals `()ⁿ`, so `unarySlice () L = L`).

  Key insight (the "diagonal" transition `δⁿ q := δ q q q`):
  - In a left-independent CA, the influence cone at position 0 at time t
    covers only cells 0..t (right-only cone: left neighbor is always ignored).
  - On a word `w = aⁿ`, every cell 0..n-1 starts in the same inner state
    `q₀ = C.embed (some a)`.
  - So cell 0 at time n-1 equals `(δⁿ)^{n-1}(q₀)`, which depends only on |w|.
  - A DFA over `α` with states `Option (Option C.Q)` and a sink for non-`a`
    inputs recognizes the unary slice exactly.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Option

namespace CellularAutomatas

open CellAutomaton

/-! ## The unary slice of a language

  For an alphabet `α` and a fixed letter `a : α`, the **unary slice** of a
  language `L : Language α` at `a` is the sublanguage of `L` consisting of
  words of the form `aⁿ` (only the letter `a` repeated). Equivalently it is
  `L ∩ {a}*`.

  This is the natural object to consider when generalizing
  `oca_rt_unary_regular` from `Unit` to arbitrary alphabets: the same diagonal-
  transition argument shows that for any `C : OCA_rt α` and any `a : α`, the
  unary slice `unarySlice a C.L` is regular. -/

/-- The unary slice of `L` at letter `a`: words `aⁿ` belonging to `L`. -/
def Language.unarySlice {α : Type} (a : α) (L : Language α) : Language α :=
  { w | (∃ n, w = List.replicate n a) ∧ w ∈ L }

@[simp]
lemma Language.mem_unarySlice {α : Type} (a : α) (L : Language α) (w : Word α) :
    w ∈ Language.unarySlice a L ↔ (∃ n, w = List.replicate n a) ∧ w ∈ L :=
  Iff.rfl

/-! ## Step 1: Right-only influence cone for left-independent CAs -/

/-- For a left-independent CA, `nextt c t p` depends only on cells p..p+t.
    Since δ ignores the left neighbor at every step, the influence cone is right-only. -/
private lemma left_indep_right_cone {α β : Type} (C : CellAutomaton α β)
    (h_li : C.left_independent) (c1 c2 : Config C.Q) (t : ℕ) (p : ℤ)
    (h : ∀ j : ℤ, p ≤ j → j ≤ p + t → c1 j = c2 j) :
    C.nextt c1 t p = C.nextt c2 t p := by
  induction t generalizing p c1 c2 with
  | zero =>
    show c1 p = c2 p
    exact h p le_rfl (by simp)
  | succ t ih =>
    simp only [nextt_succ, next_apply]
    -- Use IH for the center and right cells (left is irrelevant by h_li)
    have h_center : C.nextt c1 t p = C.nextt c2 t p :=
      ih c1 c2 p fun j hjl hjr =>
        h j hjl (by push_cast at hjr ⊢; linarith)
    have h_right : C.nextt c1 t (p + 1) = C.nextt c2 t (p + 1) :=
      ih c1 c2 (p + 1) fun j hjl hjr =>
        h j (by linarith) (by push_cast at hjr ⊢; linarith)
    -- Left-independence lets us swap the left argument freely
    rw [h_li (C.nextt c1 t (p - 1)) _ _ (C.nextt c2 t (p - 1)), h_center, h_right]

/-! ## Step 2: Uniform initial config evolves uniformly under δⁿ -/

/-- If all cells start in state q, they remain in state (δⁿ)^t(q) at every time t,
    where δⁿ(q) = δ(q,q,q) is the "diagonal" self-transition. -/
private lemma uniform_nextt_of_const {α β : Type} (C : CellAutomaton α β)
    (c : Config C.Q) (q : C.Q) (h : ∀ p, c p = q) :
    ∀ (t : ℕ) (p : ℤ), C.nextt c t p = Nat.iterate (fun x => C.δ x x x) t q := by
  intro t
  induction t with
  | zero =>
    intro p; simp [nextt_zero, h]
  | succ t ih =>
    intro p
    -- After t steps all cells hold iter t q; one more step applies δ(·,·,·)
    simp only [nextt_succ, next_apply, ih (p - 1), ih p, ih (p + 1),
               Function.iterate_succ_apply']

/-! ## Step 3: OCA over a uniform-`a` word computes via the diagonal transition

  The key step: for a left-independent CA `C` over alphabet `α`, if every cell
  inside a word `w` holds the same letter `a`, then cell 0 at time `t` (with
  `t < |w|`) equals `(δⁿ)^t(C.inner a)`. This is exactly the unary scenario,
  generalized from `Unit` to arbitrary `α`. -/

/-- For a left-independent CA, if every position of `w` is the letter `a`,
    then cell 0 at time `t < |w|` equals `(δⁿ)^t(C.inner a)`. -/
private lemma oca_unary_nextt_at_zero {α : Type} (a : α) (C : LCellAutomaton α)
    (h_li : C.left_independent) (w : Word α)
    (hw : ∀ i (hi : i < w.length), w[i] = a)
    (t : ℕ) (ht : t < w.length) :
    C.nextt ⦋⟬w⟭⦌ t 0 = Nat.iterate (fun q => C.δ q q q) t (C.inner a) := by
  -- Show that on [0, t] the input agrees with the all-(C.inner a) config
  have h_uniform : C.nextt ⦋⟬w⟭⦌ t 0 = C.nextt (fun _ => C.inner a) t 0 :=
    left_indep_right_cone C h_li ⦋⟬w⟭⦌ (fun _ => C.inner a) t 0 (by
      intro j hjl hjr
      show C.embed (⟬w⟭ j) = C.embed (some a)
      -- Position j is inside the word, so word_to_config gives some w[j]
      have h_range : 0 ≤ j ∧ j < (w.length : ℤ) := ⟨hjl, by omega⟩
      simp only [word_to_config_apply, dif_pos h_range]
      -- By hw, w[j.toNat] = a
      have hj_nat : j.toNat < w.length := by omega
      rw [hw j.toNat hj_nat])
  exact h_uniform.trans
    (uniform_nextt_of_const C (fun _ => C.inner a) (C.inner a) (fun _ => rfl) t 0)

/-! ## Step 4: DFA construction

  We build a DFA over the full alphabet `α` that recognizes the unary slice
  `unarySlice a (toRtCa C).L`. The DFA has three kinds of states:

  - `none` (sink): a non-`a` symbol has been read; reject.
  - `some none` (initial): no symbols read yet.
  - `some (some q)` (running): at least one `a` was read; current diagonal
    state is `q`.

  On reading `a`, the running state evolves via the diagonal transition
  `δⁿ q := δ q q q`. On reading any `b ≠ a`, we transition to the sink.
  An `Alphabet α` instance is needed for `DecidableEq α`. -/

/-- DFA recognizing `unarySlice a (toRtCa C).L` for a left-independent CA `C`. -/
private def unaryOcaDFA {α : Type} [Alphabet α] (a : α) (C : LCellAutomaton α) :
    DFA α (Option (Option C.Q)) where
  step := fun s b => match s with
    | none          => none
    | some none     => if b = a then some (some (C.inner a)) else none
    | some (some q) => if b = a then some (some (C.δ q q q)) else none
  start  := some none
  accept := { s | match s with
    | none          => False
    | some none     => C.project C.border = true
    | some (some q) => C.project q = true }

variable {α : Type} [Alphabet α]

@[simp]
private lemma unaryOcaDFA_step_sink (a : α) (C : LCellAutomaton α) (b : α) :
    (unaryOcaDFA a C).step none b = none := rfl

private lemma unaryOcaDFA_step_init_a (a : α) (C : LCellAutomaton α) :
    (unaryOcaDFA a C).step (some none) a = some (some (C.inner a)) := by
  simp [unaryOcaDFA]

private lemma unaryOcaDFA_step_running_a (a : α) (C : LCellAutomaton α) (q : C.Q) :
    (unaryOcaDFA a C).step (some (some q)) a = some (some (C.δ q q q)) := by
  simp [unaryOcaDFA]

private lemma unaryOcaDFA_step_init_other (a : α) (C : LCellAutomaton α) (b : α) (hb : b ≠ a) :
    (unaryOcaDFA a C).step (some none) b = none := by
  simp [unaryOcaDFA, hb]

private lemma unaryOcaDFA_step_running_other
    (a : α) (C : LCellAutomaton α) (q : C.Q) (b : α) (hb : b ≠ a) :
    (unaryOcaDFA a C).step (some (some q)) b = none := by
  simp [unaryOcaDFA, hb]

/-- From the sink state, evalFrom on any word stays in the sink. -/
private lemma unaryOcaDFA_evalFrom_sink (a : α) (C : LCellAutomaton α) (w : Word α) :
    (unaryOcaDFA a C).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons b w' ih =>
    -- Step at the sink stays at the sink, then ih on the tail
    show (unaryOcaDFA a C).evalFrom ((unaryOcaDFA a C).step none b) w' = none
    rw [unaryOcaDFA_step_sink]; exact ih

/-- From running state `some (some q)`, evalFrom on `replicate n a` gives
    `some (some ((δⁿ)^n q))`. -/
private lemma unaryOcaDFA_evalFrom_running_replicate
    (a : α) (C : LCellAutomaton α) (q : C.Q) (n : ℕ) :
    (unaryOcaDFA a C).evalFrom (some (some q)) (List.replicate n a) =
      some (some (Nat.iterate (fun r => C.δ r r r) n q)) := by
  induction n generalizing q with
  | zero => simp [DFA.evalFrom]
  | succ n ih =>
    -- replicate (n+1) a = a :: replicate n a
    rw [List.replicate_succ, Function.iterate_succ_apply]
    show (unaryOcaDFA a C).evalFrom
        ((unaryOcaDFA a C).step (some (some q)) a) (List.replicate n a) = _
    rw [unaryOcaDFA_step_running_a]
    exact ih (C.δ q q q)

/-- From any state, on a word containing a non-`a` symbol, evalFrom is the sink. -/
private lemma unaryOcaDFA_evalFrom_eq_sink_of_mem_ne
    (a : α) (C : LCellAutomaton α) (s : Option (Option C.Q)) (w : Word α)
    (hw : ∃ b ∈ w, b ≠ a) :
    (unaryOcaDFA a C).evalFrom s w = none := by
  -- Generalize `s` and `hw` so the IH quantifies over both
  revert s hw
  induction w with
  | nil =>
    intro s hw
    -- Vacuous: no element of [] can witness ∃ b ∈ w, b ≠ a
    obtain ⟨b, hb, _⟩ := hw
    exact absurd hb List.not_mem_nil
  | cons c w' ih =>
    intro s hw
    show (unaryOcaDFA a C).evalFrom ((unaryOcaDFA a C).step s c) w' = none
    by_cases hca : c = a
    · -- c = a: the witness must be in w'; apply IH
      subst hca
      have hw' : ∃ b ∈ w', b ≠ c := by
        obtain ⟨b, hb, hbc⟩ := hw
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hbc
        · exact ⟨b, hb', hbc⟩
      exact ih _ hw'
    · -- c ≠ a: step sends us to the sink, which then absorbs the rest
      have h_step : (unaryOcaDFA a C).step s c = none := by
        rcases s with _ | _ | _
        · rfl
        · exact unaryOcaDFA_step_init_other a C c hca
        · exact unaryOcaDFA_step_running_other a C _ c hca
      rw [h_step]
      exact unaryOcaDFA_evalFrom_sink a C w'

/-! ## Step 5: DFA correctness

  We split on whether `w` is `replicate w.length a` (i.e., consists entirely
  of `a`'s). If yes, the DFA reaches a running state matching the CA's
  computation; if not, the DFA reaches the sink and rejects, while the unary
  slice excludes `w` by definition. -/

/-- The DFA accepts `w` iff `w` lies in the unary slice of `(toRtCa C).L`. -/
private lemma unaryOcaDFA_accepts_iff
    (a : α) (C : LCellAutomaton α) (h_li : C.left_independent) (w : Word α) :
    w ∈ (unaryOcaDFA a C).accepts ↔ w ∈ Language.unarySlice a (toRtCa C).L := by
  simp only [DFA.mem_accepts, Language.mem_unarySlice, tCellAutomaton.L,
             tCellAutomaton.accepts, toRtCa, AcceptanceSchema.rt_left,
             CellAutomaton.comp_apply]
  by_cases h_rep : w = List.replicate w.length a
  · -- Case 1: w is a replicate. Both sides reduce to a CA-acceptance condition.
    rcases Nat.eq_zero_or_pos w.length with h_zero | h_pos
    · -- w = [] (length zero)
      have hw : w = [] := List.eq_nil_of_length_eq_zero h_zero
      subst hw
      -- DFA stays at start (some none); CA reads the border at position 0
      simp only [unaryOcaDFA, DFA.eval, DFA.evalFrom, List.foldl_nil, Set.mem_setOf_eq,
                 CellAutomaton.border]
      refine ⟨fun h => ⟨⟨0, rfl⟩, h⟩, fun ⟨_, h⟩ => h⟩
    · -- w = replicate w.length a, with length ≥ 1
      have ht : w.length - 1 < w.length := Nat.sub_lt h_pos Nat.one_pos
      -- Decompose the replicate as `a :: replicate (w.length - 1) a`
      have h_rep_cons :
          List.replicate w.length a = a :: List.replicate (w.length - 1) a := by
        conv_lhs => rw [show w.length = (w.length - 1) + 1 from by omega]
        rfl
      -- DFA eval: start (some none) -[a]→ some (some (C.inner a)),
      -- then |w|-1 more diagonal steps via the running-replicate lemma
      have h_dfa : (unaryOcaDFA a C).eval w =
          some (some (Nat.iterate (fun q => C.δ q q q) (w.length - 1) (C.inner a))) := by
        show (unaryOcaDFA a C).evalFrom (some none) w = _
        -- Only rewrite `w` on the LHS, leaving `w.length - 1` on the RHS untouched
        conv_lhs => rw [h_rep, h_rep_cons]
        show (unaryOcaDFA a C).evalFrom
            ((unaryOcaDFA a C).step (some none) a) (List.replicate (w.length - 1) a) = _
        rw [unaryOcaDFA_step_init_a]
        exact unaryOcaDFA_evalFrom_running_replicate a C (C.inner a) (w.length - 1)
      -- All positions of w hold `a` (since w = replicate w.length a)
      have hw_all : ∀ i (hi : i < w.length), w[i] = a := by
        have h_mem := List.eq_replicate_length.mp h_rep
        intro i hi
        exact h_mem _ (List.getElem_mem hi)
      have h_oca : C.nextt ⦋⟬w⟭⦌ (w.length - 1) 0 =
          Nat.iterate (fun q => C.δ q q q) (w.length - 1) (C.inner a) :=
        oca_unary_nextt_at_zero a C h_li w hw_all (w.length - 1) ht
      rw [h_dfa]
      simp only [unaryOcaDFA, Set.mem_setOf_eq]
      constructor
      · -- DFA accept ⇒ slice membership
        intro h
        refine ⟨⟨w.length, h_rep⟩, ?_⟩
        show C.project (C.nextt ⦋⟬w⟭⦌ (w.length - 1) 0) = true
        rw [h_oca]; exact h
      · -- slice membership ⇒ DFA accept
        rintro ⟨_, h⟩
        have h' : C.project (C.nextt ⦋⟬w⟭⦌ (w.length - 1) 0) = true := h
        rw [h_oca] at h'; exact h'
  · -- Case 2: w contains a non-a symbol. Both sides are False.
    have hw_ne : ∃ b ∈ w, b ≠ a := by
      by_contra h
      push_neg at h
      exact h_rep (List.eq_replicate_length.mpr h)
    have h_eval : (unaryOcaDFA a C).eval w = none :=
      unaryOcaDFA_evalFrom_eq_sink_of_mem_ne a C _ w hw_ne
    constructor
    · intro h_dfa
      rw [h_eval] at h_dfa
      exact absurd h_dfa (by simp [unaryOcaDFA])
    · rintro ⟨⟨n, hn⟩, _⟩
      -- w = replicate n a contradicts h_rep (since |w| = n)
      exfalso
      apply h_rep
      have hlen : w.length = n := by rw [hn]; simp
      rw [hlen]; exact hn

/-! ## Main Results -/

/-- **Generalized regularity.** For any alphabet `α` and any letter `a : α`,
    every unary slice of an `OCA_rt α` language is regular.

    Proof: the DFA `unaryOcaDFA a C` over alphabet `α` recognizes the slice. -/
theorem oca_rt_unary_slice_regular (a : α) :
    ∀ L ∈ ℒ (OCA_rt α), (Language.unarySlice a L).IsRegular := by
  intro L ⟨C, hL⟩
  rw [hL]
  refine ⟨Option (Option C.val.Q), inferInstance,
          unaryOcaDFA a C.val.toCellAutomaton, ?_⟩
  ext w
  rw [DFA.mem_accepts]
  show w ∈ (unaryOcaDFA a C.val.toCellAutomaton).accepts ↔
       w ∈ Language.unarySlice a (DefinesLanguage.L C)
  rw [unaryOcaDFA_accepts_iff a C.val.toCellAutomaton C.prop w]
  simp [DefinesLanguage.L, toRtCa]

/-- Every word over the unary alphabet `Unit` is `replicate n ()` for some `n`. -/
private lemma unit_word_replicate (w : Word Unit) :
    w = List.replicate w.length () := by
  rw [List.eq_replicate_length]
  intro b _; cases b; rfl

/-- For the unary alphabet `Unit`, every language is its own unary slice at `()`,
    since every word is of the form `()ⁿ`. -/
private lemma unarySlice_unit_eq (L : Language Unit) :
    Language.unarySlice () L = L := by
  ext w
  simp only [Language.mem_unarySlice]
  refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨w.length, unit_word_replicate w⟩, h⟩⟩

/-- **Original theorem (Unit corollary).** Every language recognized by
    `OCA_rt Unit` is regular.

    Follows from `oca_rt_unary_slice_regular` because over `Unit` every word
    is a replicate, so `unarySlice () L = L`. -/
theorem oca_rt_unary_regular : ∀ L ∈ ℒ (OCA_rt Unit), L.IsRegular := by
  intro L hL
  have h := oca_rt_unary_slice_regular () L hL
  rwa [unarySlice_unit_eq] at h

end CellularAutomatas
