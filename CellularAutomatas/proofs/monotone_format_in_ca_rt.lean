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
    have h_len : u.length = n + m := by
      have := congrArg List.length hu; simp at this; exact this
    -- Element-wise: u[p].isSome matches (true^n ++ false^m)[p]
    have h_elem (p : ℕ) (hp : p < n + m) :
        (u[p]'(by omega)).isSome =
        (List.replicate n true ++ List.replicate m false)[p]'(by simp; omega) := by
      have : (u.map Option.isSome)[p]'(by simp; omega) =
          (List.replicate n true ++ List.replicate m false)[p]'(by simp; omega) := by congr 1
      simpa using this
    -- First n elements are some _
    have h_some (p : ℕ) (hp : p < n) : (u[p]'(by omega)).isSome = true := by
      rw [h_elem p (by omega),
          List.getElem_append_left (show p < (List.replicate n true).length by simp; omega)]
      simp
    -- Remaining m elements are none
    have h_none (p : ℕ) (hp1 : n ≤ p) (hp2 : p < n + m) : u[p]'(by omega) = none := by
      have h1 := h_elem p hp2
      rw [List.getElem_append_right (show (List.replicate n true).length ≤ p by simp; omega)] at h1
      simp at h1
      cases hx : u[p] <;> simp_all
    -- Build w by extracting values from the first n elements
    let w : Word α := List.ofFn fun (k : Fin n) =>
      (u[k.val]'(by omega)).get (h_some k.val k.isLt)
    exact ⟨w, m, List.ext_getElem (by simp [w, h_len]) fun p hp1 hp2 => by
      simp only [List.length_append, List.length_map, List.length_replicate, w,
                  List.length_ofFn] at hp2
      by_cases hp : p < n
      · -- p in the some-part
        rw [List.getElem_append_left (by simp [w]; omega)]
        rw [List.getElem_map, List.getElem_ofFn]
        exact (Option.some_get _).symm
      · -- p in the none-part
        push_neg at hp
        rw [List.getElem_append_right (by simp [w]; omega), List.getElem_replicate]
        simp [(h_none p hp (by omega)).symm]
        ⟩

/-- The monotone format language is in ℒ(CA_rt (Option α)). -/
theorem monotone_format_in_ca_rt : MonotoneFormat α ∈ ℒ (CA_rt (Option α)) := by
  rw [monotoneFormat_eq_preimage]
  obtain ⟨C, hC_rt, hC_L⟩ := truestar_falsestar_in_ca_rt
  refine ⟨C.map_embed Option.isSome, ?_, ?_⟩
  · exact (c_map_embed_in_ca_rt_iff_c_in_ca_rt C Option.isSome).mpr hC_rt
  · ext w
    -- Goal: w.map isSome ∈ monotoneDFA.accepts ↔ w ∈ (C.map_embed isSome).L
    -- map_embed_L: w ∈ (C.map_embed f).L ↔ w.map f ∈ C.L
    -- hC_L: monotoneDFA.accepts = C.L (as DefinesLanguage.L C)
    constructor
    · intro hw
      have : w.map Option.isSome ∈ DefinesLanguage.L C := hC_L ▸ hw
      exact (map_embed_L C Option.isSome w).mpr this
    · intro hw
      have := (map_embed_L C Option.isSome w).mp hw
      exact hC_L ▸ this

end CellularAutomatas
