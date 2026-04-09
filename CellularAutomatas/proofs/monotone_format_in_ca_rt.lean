/-
  # MonotoneFormat Language in CA_rt

  Proves that the monotone format language `true^* false^*` is in ℒ(CA_rt Bool),
  and that MonotoneFormat α is in ℒ(CA_rt (Option α)) via preimage.
-/

import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.dfa_to_left_indep_ca
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [Alphabet α]

/-! ## MonotoneFormat Definition -/

/-- Monotone format: words of the form `some^* ++ none^*` over Option α. -/
def MonotoneFormat (α : Type) : Language (Option α) :=
  { u | ∃ (w : Word α) (k : ℕ), u = w.map some ++ List.replicate k none }

/-! ## DFA for true^* false^*

The DFA has 3 states: reading_trues (start, accept), reading_falses (accept), reject.
-/

inductive MonotoneDFAState
  | reading_trues | reading_falses | reject
deriving DecidableEq, Fintype, Inhabited

def monotoneDFA_step : MonotoneDFAState → Bool → MonotoneDFAState
  | .reading_trues, true => .reading_trues
  | .reading_trues, false => .reading_falses
  | .reading_falses, true => .reject
  | .reading_falses, false => .reading_falses
  | .reject, _ => .reject

def monotoneDFA : DFA Bool MonotoneDFAState where
  step := monotoneDFA_step
  start := .reading_trues
  accept := { .reading_trues, .reading_falses }

instance : DecidablePred (· ∈ monotoneDFA.accept) := fun s =>
  match s with
  | .reading_trues => isTrue (by simp [monotoneDFA])
  | .reading_falses => isTrue (by simp [monotoneDFA])
  | .reject => isFalse (by simp [monotoneDFA])

/-! ## DFA Correctness

We prove correctness by tracking the foldl computation directly.
-/

/-- foldl monotoneDFA_step reading_trues on all-true list stays reading_trues. -/
private lemma foldl_trues (n : ℕ) :
    List.foldl monotoneDFA_step .reading_trues (List.replicate n true) = .reading_trues := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.foldl_cons, monotoneDFA_step, ih]

/-- foldl monotoneDFA_step reading_falses on all-false list stays reading_falses. -/
private lemma foldl_falses (n : ℕ) :
    List.foldl monotoneDFA_step .reading_falses (List.replicate n false) = .reading_falses := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.foldl_cons, monotoneDFA_step, ih]

/-- foldl monotoneDFA_step reject on any list stays reject. -/
private lemma foldl_reject (xs : List Bool) :
    List.foldl monotoneDFA_step .reject xs = .reject := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [List.foldl_cons, monotoneDFA_step, ih]

/-- If a list contains true, foldl from reading_falses reaches reject. -/
private lemma foldl_falses_with_true (xs : List Bool) (hx : true ∈ xs) :
    List.foldl monotoneDFA_step .reading_falses xs = .reject := by
  induction xs with
  | nil => simp at hx
  | cons b bs ih =>
    simp only [List.foldl_cons, monotoneDFA_step]
    cases b with
    | true => exact foldl_reject bs
    | false =>
      apply ih
      simp only [List.mem_cons] at hx
      exact hx.resolve_left (by simp)

/-- `true^n ++ false^m` is accepted by monotoneDFA. -/
lemma monotoneDFA_accepts_pattern (n m : ℕ) :
    (List.replicate n true ++ List.replicate m false) ∈ monotoneDFA.accepts := by
  simp only [DFA.mem_accepts, DFA.eval, monotoneDFA, DFA.evalFrom]
  rw [List.foldl_append, foldl_trues]
  cases m with
  | zero => simp
  | succ m =>
    simp only [List.replicate_succ, List.foldl_cons, monotoneDFA_step]
    rw [foldl_falses]
    simp

/-- A word accepted by monotoneDFA has the form `true^* false^*`. -/
lemma monotoneDFA_accepts_iff (w : List Bool) :
    w ∈ monotoneDFA.accepts ↔ ∃ n m, w = List.replicate n true ++ List.replicate m false := by
  constructor
  · -- If accepted, decompose w = true-prefix ++ false-suffix
    intro h
    simp only [DFA.mem_accepts, DFA.eval, monotoneDFA, DFA.evalFrom] at h
    -- Induction: track foldl state through the list
    suffices ∀ (s : MonotoneDFAState) (xs : List Bool),
        List.foldl monotoneDFA_step s xs ∈ ({.reading_trues, .reading_falses} : Set _) →
        (s = .reading_trues → ∃ n m, xs = List.replicate n true ++ List.replicate m false) ∧
        (s = .reading_falses → ∃ m, xs = List.replicate m false) ∧
        (s = .reject → False) by
      exact (this .reading_trues w h).1 rfl
    intro s xs
    induction xs generalizing s with
    | nil =>
      intro h_acc
      simp only [List.foldl_nil] at h_acc
      refine ⟨fun _ => ⟨0, 0, by simp⟩, fun _ => ⟨0, by simp⟩, fun hs => ?_⟩
      subst hs; simp at h_acc
    | cons b bs ih =>
      simp only [List.foldl_cons]
      intro h_acc
      cases s with
      | reading_trues =>
        cases b with
        | true =>
          simp only [monotoneDFA_step] at h_acc ⊢
          obtain ⟨h1, _, _⟩ := ih .reading_trues h_acc
          obtain ⟨n, m, hbs⟩ := h1 rfl
          exact ⟨fun _ => ⟨n + 1, m, by simp [List.replicate_succ, hbs]⟩,
                 fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
        | false =>
          simp only [monotoneDFA_step] at h_acc ⊢
          obtain ⟨_, h2, _⟩ := ih .reading_falses h_acc
          obtain ⟨m, hbs⟩ := h2 rfl
          exact ⟨fun _ => ⟨0, m + 1, by simp [List.replicate_succ, hbs]⟩,
                 fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
      | reading_falses =>
        cases b with
        | false =>
          simp only [monotoneDFA_step] at h_acc ⊢
          obtain ⟨_, h2, _⟩ := ih .reading_falses h_acc
          obtain ⟨m, hbs⟩ := h2 rfl
          exact ⟨fun h => absurd h (by simp),
                 fun _ => ⟨m + 1, by simp [List.replicate_succ, hbs]⟩,
                 fun h => absurd h (by simp)⟩
        | true =>
          simp only [monotoneDFA_step] at h_acc ⊢
          have := foldl_reject bs
          rw [this] at h_acc; simp at h_acc
      | reject =>
        simp only [monotoneDFA_step] at h_acc ⊢
        rw [foldl_reject] at h_acc; simp at h_acc
  · intro ⟨n, m, hw⟩
    rw [hw]; exact monotoneDFA_accepts_pattern n m

/-! ## OCA_rt to CA_rt inclusion -/

theorem ℒ_OCA_rt_sub_CA_rt {β : Type} [Alphabet β] :
    ℒ (OCA_rt β) ⊆ ℒ (CA_rt β) := by
  intro L ⟨C, hC, hL⟩
  exact ⟨C, ⟨hC.1.1, hC.2⟩, hL⟩

/-! ## Main Results -/

/-- The `true^* false^*` language is in ℒ(CA_rt Bool). -/
theorem truestar_falsestar_in_ca_rt :
    monotoneDFA.accepts ∈ ℒ (CA_rt Bool) :=
  ℒ_OCA_rt_sub_CA_rt (dfa_language_in_OCA_rt monotoneDFA)

/-- MonotoneFormat α is the preimage of monotoneDFA.accepts under Option.isSome. -/
lemma monotoneFormat_eq_preimage :
    MonotoneFormat α = { w | w.map Option.isSome ∈ monotoneDFA.accepts } := by
  ext u
  simp only [MonotoneFormat, Set.mem_setOf_eq, monotoneDFA_accepts_iff]
  constructor
  · intro ⟨w, k, hu⟩
    exact ⟨w.length, k, by subst hu; simp [List.map_append, List.map_map, List.map_replicate,
      show (Option.isSome ∘ @some α) = fun _ => true from funext (fun _ => rfl)]⟩
  · intro ⟨n, m, hu⟩
    -- u.map isSome = true^n ++ false^m → first n are some, rest are none
    have h_len : u.length = n + m := by simpa using congrArg List.length hu
    have h_some : ∀ i (hi : i < n), ∃ a, u[i]'(by omega) = some a := by
      intro i hi
      have : (u.map Option.isSome)[i]'(by simp; omega) = true := by rw [hu]; simp [hi]
      simp at this; exact Option.isSome_iff_exists.mp this
    have h_none : ∀ i (hi : i < m), u[n + i]'(by omega) = none := by
      intro i hi
      have : (u.map Option.isSome)[n + i]'(by simp; omega) = false := by
        rw [hu]; simp only [List.getElem_append]; simp [show ¬(n + i < n) from by omega]
      simp at this; exact Option.not_isSome_iff_eq_none.mp this
    -- Build w from the some-prefix
    let w := (u.take n).filterMap id
    use w, m
    -- u = w.map some ++ none^m
    have h_take : u.take n = w.map some := by
      apply List.ext_getElem
      · -- lengths match
        simp only [w, List.length_map]
        induction n generalizing u with
        | zero => simp
        | succ n ih =>
          match u, h_some, h_len, hu with
          | a :: u', h_some', h_len', hu' =>
            obtain ⟨a', ha'⟩ := h_some' 0 (by omega)
            simp at ha'; subst ha'
            simp only [List.take_succ_cons, List.filterMap_cons, List.length_cons, List.length_map]
            have h_len'' : u'.length = n + m := by simp at h_len'; omega
            have hu'' : u'.map Option.isSome = List.replicate n true ++ List.replicate m false := by
              simpa using hu'
            have h_some'' : ∀ i (hi : i < n), ∃ a, u'[i]'(by omega) = some a := by
              intro i hi; exact h_some (i + 1) (by omega) |>.imp fun a h => by simpa using h
            specialize ih u' h_some'' h_len'' hu''
            omega
      · -- elements match
        intro i hi1 hi2
        simp only [List.getElem_map, w]
        induction n generalizing u i with
        | zero => simp at hi1
        | succ n ih =>
          match u, h_some, h_len, hu with
          | a :: u', h_some', h_len', hu' =>
            obtain ⟨a', ha'⟩ := h_some' 0 (by omega)
            simp at ha'; subst ha'
            simp only [List.take_succ_cons, List.filterMap_cons] at hi1 hi2 ⊢
            cases i with
            | zero => simp
            | succ i' =>
              simp only [List.getElem_cons_succ, List.getElem_map]
              have h_len'' : u'.length = n + m := by simp at h_len'; omega
              have hu'' : u'.map Option.isSome = List.replicate n true ++ List.replicate m false := by
                simpa using hu'
              have h_some'' : ∀ j (hj : j < n), ∃ a, u'[j]'(by omega) = some a := by
                intro j hj; exact h_some' (j + 1) (by omega) |>.imp fun a h => by simpa using h
              exact ih u' h_some'' h_len'' hu'' i' (by omega) (by omega)
    have h_drop : u.drop n = List.replicate m none := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 _; simp only [List.length_drop] at hi1
        simp only [List.getElem_drop, List.getElem_replicate]; exact h_none i (by omega)
    calc u = u.take n ++ u.drop n := (List.take_append_drop n u).symm
      _ = w.map some ++ List.replicate m none := by rw [h_take, h_drop]

/-- The monotone format language is in ℒ(CA_rt (Option α)). -/
theorem monotone_format_in_ca_rt : MonotoneFormat α ∈ ℒ (CA_rt (Option α)) := by
  rw [monotoneFormat_eq_preimage]
  obtain ⟨C, hC_rt, hC_L⟩ := truestar_falsestar_in_ca_rt
  refine ⟨C.map_embed Option.isSome, ?_, ?_⟩
  · rw [c_map_embed_in_ca_rt_iff_c_in_ca_rt]; exact hC_rt
  · ext w; simp only [Set.mem_setOf_eq, DefinesLanguage.L, tCellAutomaton.L]
    rw [map_embed_L, ← hC_L]; rfl

end CellularAutomatas
/-
  # MonotoneFormat Language in CA_rt

  This file proves that the monotone format language is in ℒ(CA_rt (Option α)).

  **MonotoneFormat α** = { w | ∃ v : Word α, k : ℕ, w = v.map some ++ none^k }

  This is the language of words over Option α that have the form `some^* ++ none^*`:
  all `some` values come before all `none` values.

  ## Approach

  1. Define a DFA on Bool that recognizes `true^* false^*`
  2. Use `dfa_language_in_OCA_rt` to show this DFA language is in `ℒ(OCA_rt Bool)`
  3. Show `ℒ(OCA_rt Bool) ⊆ ℒ(CA_rt Bool)`
  4. Use `tCellAutomaton.map_embed Option.isSome` to lift from `CA_rt Bool` to `CA_rt (Option α)`
  5. Show language equality: `MonotoneFormat α = { w | w.map Option.isSome ∈ (true^* false^*) }`
-/

import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.dfa_to_left_indep_ca
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [Alphabet α]

/-! ## MonotoneFormat Definition -/

/-- Monotone format: words of the form `some^* ++ none^*` over Option α. -/
def MonotoneFormat (α : Type) : Language (Option α) :=
  { u | ∃ (w : Word α) (k : ℕ), u = w.map some ++ List.replicate k none }

/-! ## DFA for true^* false^* -/

/-- States for the monotone DFA on Bool:
    - `reading_trues`: initial state, accepting true values
    - `reading_falses`: switched to false values
    - `reject`: saw true after false (invalid) -/
inductive MonotoneDFAState
  | reading_trues : MonotoneDFAState
  | reading_falses : MonotoneDFAState
  | reject : MonotoneDFAState
deriving DecidableEq, Fintype, Inhabited

/-- DFA transition: true stays/rejects based on state, false transitions. -/
def monotoneDFA_step : MonotoneDFAState → Bool → MonotoneDFAState
  | .reading_trues, true => .reading_trues
  | .reading_trues, false => .reading_falses
  | .reading_falses, true => .reject
  | .reading_falses, false => .reading_falses
  | .reject, _ => .reject

/-- The DFA recognizing `true^* false^*`. -/
def monotoneDFA : DFA Bool MonotoneDFAState where
  step := monotoneDFA_step
  start := .reading_trues
  accept := { .reading_trues, .reading_falses }

/-- Accept states are decidable. -/
instance : DecidablePred (· ∈ monotoneDFA.accept) := fun s =>
  match s with
  | .reading_trues => isTrue (by simp [monotoneDFA])
  | .reading_falses => isTrue (by simp [monotoneDFA])
  | .reject => isFalse (by simp [monotoneDFA])

/-! ## DFA Correctness -/

/-- Abbreviation for the explicit DFA struct to avoid unfolding issues. -/
private abbrev theDFA : DFA Bool MonotoneDFAState :=
  { step := monotoneDFA_step, start := .reading_trues,
    accept := {.reading_trues, .reading_falses} }

/-- monotoneDFA equals theDFA. -/
private lemma monotoneDFA_eq_theDFA : monotoneDFA = theDFA := rfl

/-- Evaluating true^n from reading_trues stays in reading_trues. -/
private lemma evalFrom_trues (n : ℕ) :
    theDFA.evalFrom .reading_trues (List.replicate n true) = .reading_trues := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold DFA.evalFrom at *
    simp only [List.replicate_succ, List.foldl_cons, theDFA, monotoneDFA_step]
    exact ih

/-- Evaluating false^m from reading_falses stays in reading_falses. -/
private lemma evalFrom_falses (m : ℕ) :
    theDFA.evalFrom .reading_falses (List.replicate m false) = .reading_falses := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold DFA.evalFrom at *
    simp only [List.replicate_succ, List.foldl_cons, theDFA, monotoneDFA_step]
    exact ih

/-- `true^n ++ false^m` is accepted by the DFA. -/
lemma monotoneDFA_accepts_pattern (n m : ℕ) :
    (List.replicate n true ++ List.replicate m false) ∈ monotoneDFA.accepts := by
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append, monotoneDFA_eq_theDFA]
  rw [evalFrom_trues]
  cases m with
  | zero =>
    unfold DFA.evalFrom
    simp [theDFA]
  | succ m =>
    unfold DFA.evalFrom
    simp only [List.replicate_succ, List.foldl_cons, theDFA, monotoneDFA_step]
    have h := evalFrom_falses m
    unfold DFA.evalFrom at h
    simp only [h, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

/-- After seeing a true in reading_falses, we go to reject and stay there. -/
private lemma evalFrom_reading_falses_with_true (xs : List Bool) (hx : true ∈ xs) :
    theDFA.evalFrom .reading_falses xs = .reject := by
  induction xs with
  | nil => simp at hx
  | cons b bs ih =>
    unfold DFA.evalFrom
    simp only [List.foldl_cons, theDFA, monotoneDFA_step]
    cases hb : b with
    | true =>
      -- Reach reject state, then stay there
      clear ih hx
      induction bs with
      | nil => rfl
      | cons c cs ih =>
        simp only [List.foldl_cons, monotoneDFA_step]
        exact ih
    | false =>
      have h := ih (by simp only [List.mem_cons, hb] at hx; cases hx with | inl h => simp at h | inr h => exact h)
      unfold DFA.evalFrom at h
      exact h

/-- A word is in monotoneDFA.accepts iff it has the form `true^* false^*`. -/
lemma monotoneDFA_accepts_iff (w : List Bool) :
    w ∈ monotoneDFA.accepts ↔ ∃ n m, w = List.replicate n true ++ List.replicate m false := by
  constructor
  · -- If accepted, find n and m
    intro h
    -- Use takeWhile/dropWhile to find n and m
    use (w.takeWhile (· == true)).length, (w.dropWhile (· == true)).length
    -- w = takeWhile ++ dropWhile
    have h_concat : w = w.takeWhile (· == true) ++ w.dropWhile (· == true) :=
      (List.takeWhile_append_dropWhile (· == true) w).symm
    rw [h_concat]
    congr 1
    · -- takeWhile (· == true) = replicate n true
      have h_all : (w.takeWhile (· == true)).all (· == true) = true := List.all_takeWhile _ w
      apply List.eq_replicate_iff.mpr
      constructor
      · rfl
      · intro b hb
        simp only [List.all_eq_true, beq_iff_eq] at h_all
        exact h_all b hb
    · -- dropWhile (· == true) = replicate m false
      simp only [DFA.mem_accepts, DFA.eval, monotoneDFA_eq_theDFA] at h
      -- Track the DFA state through the computation
      -- After reading true-prefix, we're in reading_trues.
      rw [h_concat, DFA.evalFrom_of_append, evalFrom_trues] at h
      -- h: evalFrom reading_trues (dropWhile) ∈ {reading_trues, reading_falses}
      -- This means dropWhile must be all falses (otherwise we'd see a true and go to reject)
      apply List.eq_replicate_iff.mpr
      constructor
      · rfl
      · intro b hb
        by_contra h_not_false
        push_neg at h_not_false
        have h_is_true : b = true := by cases b <;> simp_all
        -- dropWhile starts with a non-true element (if non-empty)
        have h_drop := w.dropWhile (· == true)
        cases h_empty : h_drop with
        | nil => simp [h_empty] at hb
        | cons c cs =>
          -- c is the first element of dropWhile, so c ≠ true (by dropWhile property)
          have h_c_not_true : c ≠ true := by
            have := List.head_dropWhile_not (p := (· == true)) (l := w)
            simp only [bne_iff_ne, ne_eq, beq_iff_eq] at this
            simp only [h_empty, List.head?_cons, Option.map_some'] at this
            intro hc
            have : some c ≠ some true := this (by simp)
            exact this (congrArg some hc)
          have h_c_false : c = false := by cases c <;> simp_all
          -- After c (which is false), we're in reading_falses
          -- If b = true ∈ (c :: cs), then either b = c (contradiction) or b ∈ cs
          simp only [h_empty, List.mem_cons] at hb
          cases hb with
          | inl hbc =>
            rw [hbc] at h_is_true
            simp at h_is_true h_c_false
            exact h_c_false h_is_true
          | inr hb_in_cs =>
            -- b = true ∈ cs, so evalFrom reading_falses (c :: cs) = reject
            have h_eval_reject : theDFA.evalFrom .reading_falses (c :: cs) = .reject := by
              simp only [DFA.evalFrom, List.foldl_cons, theDFA, monotoneDFA_step, h_c_false]
              rw [← DFA.evalFrom]
              rw [h_is_true] at hb_in_cs
              exact evalFrom_reading_falses_with_true cs hb_in_cs
            -- But evalFrom reading_trues (c :: cs) started from reading_trues, first step is
            -- reading_trues --> reading_falses (since c = false)
            have h_eval_from_trues : theDFA.evalFrom .reading_trues (c :: cs) =
                theDFA.evalFrom .reading_falses cs := by
              simp only [DFA.evalFrom, List.foldl_cons, theDFA, monotoneDFA_step, h_c_false]
            simp only [h_empty] at h
            rw [h_eval_from_trues] at h
            rw [h_is_true] at hb_in_cs
            have := evalFrom_reading_falses_with_true cs hb_in_cs
            rw [this] at h
            simp [theDFA] at h
  · -- If w = true^n ++ false^m, then accepted
    intro ⟨n, m, hw⟩
    rw [hw]
    exact monotoneDFA_accepts_pattern n m

/-! ## OCA_rt to CA_rt inclusion -/

/-- ℒ(OCA_rt β) ⊆ ℒ(CA_rt β): every OCA_rt language is a CA_rt language. -/
theorem ℒ_OCA_rt_sub_CA_rt {β : Type} [Alphabet β] :
    ℒ (OCA_rt β) ⊆ ℒ (CA_rt β) := by
  intro L ⟨C, hC, hL⟩
  exact ⟨C, ⟨hC.1.1, hC.2⟩, hL⟩

/-! ## Main Theorem -/

/-- The `true^* false^*` language is in ℒ(CA_rt Bool). -/
theorem truestar_falsestar_in_ca_rt :
    monotoneDFA.accepts ∈ ℒ (CA_rt Bool) := by
  have h_oca := dfa_language_in_OCA_rt monotoneDFA
  exact ℒ_OCA_rt_sub_CA_rt h_oca

/-- MonotoneFormat α equals the preimage of `true^* false^*` under `Option.isSome`. -/
lemma monotoneFormat_eq_preimage :
    MonotoneFormat α = { w | w.map Option.isSome ∈ monotoneDFA.accepts } := by
  ext u
  simp only [MonotoneFormat, Set.mem_setOf_eq]
  rw [monotoneDFA_accepts_iff]
  constructor
  · -- MonotoneFormat → pattern
    intro ⟨w, k, hu⟩
    use w.length, k
    subst hu
    simp only [List.map_append, List.map_map, Function.comp_apply, Option.isSome_some,
      List.map_replicate, Option.isSome_none]
    congr 1
    induction w with
    | nil => rfl
    | cons a w ih => simp [ih]
  · -- Pattern → MonotoneFormat
    intro ⟨n, m, hu⟩
    -- u.map Option.isSome = true^n ++ false^m
    have h_len : u.length = n + m := by
      have := congrArg List.length hu
      simp at this
      exact this
    -- Split u: first n are some, last m are none
    have h_take_some : ∀ i (hi : i < n), ∃ a, u[i]'(by omega) = some a := by
      intro i hi
      have : (u.map Option.isSome)[i]'(by simp; omega) = true := by
        rw [hu]; simp [hi]
      simp at this
      exact Option.isSome_iff_exists.mp this
    have h_drop_none : ∀ i (hi : i < m), u[n + i]'(by omega) = none := by
      intro i hi
      have : (u.map Option.isSome)[n + i]'(by simp; omega) = false := by
        rw [hu]
        simp only [List.getElem_append]
        have : ¬(n + i < n) := by omega
        simp [this]
      simp at this
      exact Option.not_isSome_iff_eq_none.mp this
    -- Build w from u.take n
    let w := (u.take n).filterMap id
    use w, m
    -- Prove u = w.map some ++ none^m
    have h_take : u.take n = w.map some := by
      simp only [w]
      apply List.ext_getElem
      · simp
        induction n generalizing u with
        | zero => simp
        | succ n ih =>
          cases u with
          | nil => simp at h_len
          | cons a u' =>
            simp only [List.take_succ_cons, List.filterMap_cons, List.length_cons, Nat.add_eq,
              Nat.add_zero, List.length_map]
            obtain ⟨a', ha'⟩ := h_take_some 0 (by omega)
            simp at ha'
            subst ha'
            simp only [Option.some.injEq, List.length_filterMap_eq_length_filter,
              List.filter_cons, Option.isSome_some, ↓reduceIte, List.length_cons]
            have h_len' : u'.length = n + m := by
              simp at h_len; omega
            have hu' : u'.map Option.isSome = List.replicate n true ++ List.replicate m false := by
              have : (some a' :: u').map Option.isSome = true :: u'.map Option.isSome := by simp
              rw [this] at hu
              simpa using hu
            have h_take_some' : ∀ j (hj : j < n), ∃ a, u'[j]'(by omega) = some a := by
              intro j hj
              have := h_take_some (j + 1) (by omega)
              simp at this
              exact this
            specialize ih u' h_len' hu' h_take_some'
            omega
      · intro i hi1 hi2
        simp only [List.getElem_map]
        simp only [w]
        -- Need: ((u.take n).filterMap id)[i] = some of (u.take n)[i]
        induction n generalizing u i with
        | zero => simp at hi1
        | succ n ih =>
          cases u with
          | nil => simp at h_len
          | cons a u' =>
            obtain ⟨a', ha'⟩ := h_take_some 0 (by omega)
            simp at ha'
            subst ha'
            simp only [List.take_succ_cons, List.filterMap_cons, Option.some.injEq,
              List.length_filterMap_eq_length_filter, List.filter_cons, Option.isSome_some,
              ↓reduceIte, List.length_cons] at hi1 hi2 ⊢
            cases i with
            | zero => simp
            | succ i' =>
              simp only [List.getElem_cons_succ, List.getElem_map]
              have h_len' : u'.length = n + m := by simp at h_len; omega
              have hu' : u'.map Option.isSome = List.replicate n true ++ List.replicate m false := by
                have : (some a' :: u').map Option.isSome = true :: u'.map Option.isSome := by simp
                rw [this] at hu
                simpa using hu
              have h_take_some' : ∀ j (hj : j < n), ∃ a, u'[j]'(by omega) = some a := by
                intro j hj
                have := h_take_some (j + 1) (by omega)
                simp at this
                exact this
              exact ih u' h_len' hu' h_take_some' i' (by omega : i' < (u'.take n).length)
                (by simp; omega)
    have h_drop : u.drop n = List.replicate m none := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2
        simp only [List.length_drop] at hi1
        simp only [List.getElem_drop, List.getElem_replicate]
        exact h_drop_none i (by omega)
    calc u = u.take n ++ u.drop n := (List.take_append_drop n u).symm
      _ = w.map some ++ List.replicate m none := by rw [h_take, h_drop]

/-- The monotone format language is in ℒ(CA_rt (Option α)).

**Construction**: Map input through `Option.isSome` to Bool, then check
the Bool word is `true^* false^*` via a 3-state DFA.

Uses `tCellAutomaton.map_embed Option.isSome` to lift from `CA_rt Bool` to `CA_rt (Option α)`. -/
theorem monotone_format_in_ca_rt : MonotoneFormat α ∈ ℒ (CA_rt (Option α)) := by
  rw [monotoneFormat_eq_preimage]
  -- Get CA for true^* false^*
  obtain ⟨C, hC_rt, hC_L⟩ := truestar_falsestar_in_ca_rt
  -- Lift to Option α via map_embed
  let C' := C.map_embed Option.isSome
  use C'
  constructor
  · -- C' ∈ CA_rt (Option α)
    rw [c_map_embed_in_ca_rt_iff_c_in_ca_rt]
    exact hC_rt
  · -- Language equality
    ext w
    simp only [Set.mem_setOf_eq, DefinesLanguage.L, tCellAutomaton.L]
    rw [map_embed_L]
    rw [← hC_L]
    rfl

end CellularAutomatas
