/-
  # Finite Languages are Regular

  This file proves that finite languages are regular (recognized by DFAs).
-/

import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Language

variable {α : Type*}

/-! ## Empty Language is Regular -/

/-- The empty language is regular: recognized by a DFA that rejects everything. -/
theorem empty_isRegular : (0 : Language α).IsRegular := by
  use Unit, inferInstance
  use { step := fun _ _ => (), start := (), accept := ∅ }
  ext x
  simp [DFA.mem_accepts, Set.mem_empty_iff_false]

/-! ## Singleton Languages are Regular -/

/-- DFA recognizing exactly {w}: states are Option (Fin (w.length + 1)).
    - `some k` = read k characters, all matching w so far
    - `none` = mismatch (sink state) -/
private def singletonDFA [DecidableEq α] (w : List α) : DFA α (Option (Fin (w.length + 1))) where
  step := fun s a =>
    match s with
    | none => none  -- sink state absorbs
    | some k =>
      if h : k.val < w.length then
        if w[k.val] = a then some ⟨k.val + 1, by omega⟩ else none
      else none  -- already matched all of w, extra char = fail
  start := some ⟨0, by omega⟩
  accept := {some ⟨w.length, by omega⟩}

/-- Key lemma: after reading a prefix of w, we're in the matching state. -/
private lemma singletonDFA_eval_take [DecidableEq α] (w : List α) (n : ℕ) (hn : n ≤ w.length) :
    (singletonDFA w).eval (w.take n) = some ⟨n, by omega⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < w.length := Nat.lt_of_succ_le hn
    rw [List.take_succ_eq_append_getElem hn']
    simp only [DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_singleton]
    rw [← DFA.eval, ih (le_of_lt hn')]
    simp only [singletonDFA, hn', ↓reduceDIte, ↓reduceIte]

/-- Evaluating the DFA on w itself yields the accept state. -/
private lemma singletonDFA_eval_self [DecidableEq α] (w : List α) :
    (singletonDFA w).eval w = some ⟨w.length, by omega⟩ := by
  simpa using singletonDFA_eval_take w w.length le_rfl

/-- Once in sink state (none), we stay there. -/
private lemma singletonDFA_none_absorb [DecidableEq α] (w : List α) (x : List α) :
    (singletonDFA w).evalFrom none x = none := by
  induction x with
  | nil => rfl
  | cons a x ih => exact ih

/-- If we reach `some k` after reading x, then x = w.take k. -/
private lemma singletonDFA_some_means_prefix [DecidableEq α] (w x : List α) (k : Fin (w.length + 1))
    (h : (singletonDFA w).eval x = some k) : x = w.take k.val := by
  induction x using List.reverseRecOn generalizing k with
  | nil =>
    simp only [DFA.eval, DFA.evalFrom, singletonDFA] at h
    have : k = ⟨0, by omega⟩ := by
      cases h
      rfl
    simp [this]
  | append_singleton xs a ih =>
    simp only [DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_singleton] at h
    rw [← DFA.eval] at h
    -- Let s = eval xs
    generalize hs : (singletonDFA w).eval xs = s at h
    match s with
    | none =>
      exact Option.noConfusion (by simpa only [singletonDFA] using h)
    | some j =>
      simp only [singletonDFA] at h
      by_cases hj : j.val < w.length
      · simp only [hj, ↓reduceDIte] at h
        by_cases hmatch : w[j.val] = a
        · simp only [hmatch, ↓reduceIte, Option.some.injEq] at h
          -- h : ⟨j.val + 1, _⟩ = k
          have hxs := ih j hs
          rw [hxs]
          have hk : k.val = j.val + 1 := by rw [← h]
          rw [hk, List.take_succ_eq_append_getElem (by omega)]
          simp [hmatch]
        · exact Option.noConfusion (by simpa only [hmatch, ↓reduceIte] using h)
      · exact Option.noConfusion (by simpa only [hj, ↓reduceDIte] using h)

/-- The singleton DFA accepts exactly w. -/
private theorem singletonDFA_accepts [DecidableEq α] (w : List α) :
    (singletonDFA w).accepts = {w} := by
  ext x
  simp only [DFA.mem_accepts, singletonDFA, Set.mem_singleton_iff]
  constructor
  · intro h
    simpa using singletonDFA_some_means_prefix w x ⟨w.length, by omega⟩ h
  · intro h
    rw [h]
    simpa only [singletonDFA] using singletonDFA_eval_self w

/-- Any singleton language {w} is regular. -/
theorem singleton_isRegular [DecidableEq α] (w : List α) :
    ({w} : Language α).IsRegular := by
  use Option (Fin (w.length + 1)), inferInstance, singletonDFA w
  exact singletonDFA_accepts w

/-! ## Finite Languages are Regular -/

/-- Helper: product DFA evalFrom equals component evalFroms. -/
private lemma productDFA_evalFrom {σ₁ σ₂ : Type*} (M₁ : DFA α σ₁) (M₂ : DFA α σ₂)
    (s₁ : σ₁) (s₂ : σ₂) (x : List α) :
    let M : DFA α (σ₁ × σ₂) := {
      step := fun (s₁, s₂) a => (M₁.step s₁ a, M₂.step s₂ a)
      start := (M₁.start, M₂.start)
      accept := {s | s.1 ∈ M₁.accept ∨ s.2 ∈ M₂.accept}
    }
    M.evalFrom (s₁, s₂) x = (M₁.evalFrom s₁ x, M₂.evalFrom s₂ x) := by
  induction x generalizing s₁ s₂ with
  | nil => rfl
  | cons a x ih =>
    simp only [DFA.evalFrom, List.foldl_cons]
    exact ih _ _

/-- Closure under union: if L₁ and L₂ are regular, then so is L₁ ∪ L₂. -/
private theorem isRegular_union [DecidableEq α] {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) : (L₁ + L₂).IsRegular := by
  obtain ⟨σ₁, _, M₁, hM₁⟩ := h₁
  obtain ⟨σ₂, _, M₂, hM₂⟩ := h₂
  -- Product DFA
  let M : DFA α (σ₁ × σ₂) := {
    step := fun (s₁, s₂) a => (M₁.step s₁ a, M₂.step s₂ a)
    start := (M₁.start, M₂.start)
    accept := {s | s.1 ∈ M₁.accept ∨ s.2 ∈ M₂.accept}
  }
  use σ₁ × σ₂, inferInstance, M
  ext x
  simp only [DFA.mem_accepts, Language.add_def, ← hM₁, ← hM₂, DFA.mem_accepts, DFA.eval]
  rw [productDFA_evalFrom]
  rfl

/-- Any finite language is regular.

    Proved by induction on the finite set: the empty language is regular,
    and if F is regular then F ∪ {w} is regular (using closure under union). -/
theorem finite_isRegular [DecidableEq α] {L : Language α} (hL : L.Finite) :
    L.IsRegular := by
  refine _root_.Set.Finite.induction_on (motive := fun S _ => Language.IsRegular S) L hL ?_ ?_
  · -- Base case: empty language
    exact empty_isRegular
  · -- Inductive case: L = insert w S where S is regular
    intro w S _ _ hS_reg
    rw [Set.insert_eq]
    -- {w} ∪ S is regular since {w} is regular and S is regular
    have hw_reg := singleton_isRegular w
    exact isRegular_union hw_reg hS_reg

end Language
