import CellularAutomatas.defs
import Mathlib.Data.List.Basic

namespace scan_lemmas


lemma scanr_foldr_cons {α: Type u} [Alphabet α] {M: FiniteStateMachine α} (p: Word α) (q: M.Q) (tail: List M.Q) (q_ignored: M.Q):
    List.foldr (M.scanr_step q_ignored) (q :: tail) p = List.append (M.scanr_q p q) (q :: tail) := by
  induction p with
  | nil =>
    unfold FiniteStateMachine.scanr_q
    simp
  | cons a p' ih =>
    unfold FiniteStateMachine.scanr_q
    simp
    rw [ih]
    generalize hqs : M.scanr_q p' q = qs
    unfold FiniteStateMachine.scanr_q at hqs
    rw [hqs]
    cases qs with
    | nil => simp [FiniteStateMachine.scanr_step]
    | cons x xs => simp [FiniteStateMachine.scanr_step]

lemma scanr_append_take {α: Type u} [Alphabet α] {M: FiniteStateMachine α} (p s: Word α):
    (M.scanr (p.append s)).take p.length = M.scanr_q p (M.scanr_reduce s) := by
  change List α at p s
  unfold FiniteStateMachine.scanr
  unfold FiniteStateMachine.scanr_q
  change (List.foldr (M.scanr_step M.q0) [] (p ++ s)).take p.length = _
  have h_fold := List.foldr_append (f := M.scanr_step M.q0) (b := []) (l := p) (l' := s)
  rw [h_fold]
  generalize hs : s.foldr (M.scanr_step M.q0) [] = res_s
  cases res_s with
  | nil =>
    have h_len : s.length = 0 := by
      rw [← FiniteStateMachine.scanr_q_len M.q0 s]
      unfold FiniteStateMachine.scanr_q
      rw [hs]
      rfl
    have h_s_empty : s = [] := List.eq_nil_of_length_eq_zero h_len
    subst h_s_empty
    simp [FiniteStateMachine.scanr_reduce, FiniteStateMachine.scanr]
    rw [List.take_of_length_le]
    · simp [FiniteStateMachine.scanr_q]
    · change (M.scanr_q p M.q0).length ≤ p.length
      rw [FiniteStateMachine.scanr_q_len]
  | cons q_mid tail =>
    have h_reduce : M.scanr_reduce s = q_mid := by
      unfold FiniteStateMachine.scanr_reduce FiniteStateMachine.scanr FiniteStateMachine.scanr_q
      rw [hs]
    rw [h_reduce]
    rw [scanr_foldr_cons]
    change (List.append (M.scanr_q p q_mid) (q_mid :: tail)).take p.length = M.scanr_q p q_mid
    erw [List.take_append]
    rw [FiniteStateMachine.scanr_q_len]
    simp

lemma nextt_congr (C: CellAutomaton) (c1 c2: Config C.Q) (t: ℕ) (i: ℤ):
    (∀ j, i - t ≤ j ∧ j ≤ i + t → c1 j = c2 j) →
    (C.nextt c1 t) i = (C.nextt c2 t) i := by
  induction t generalizing i c1 c2 with
  | zero =>
    intro h
    simp [CellAutomaton.nextt, apply_iterated]
    apply h
    constructor <;> omega
  | succ t ih =>
    intro h
    simp [CellAutomaton.nextt, apply_iterated]
    -- The goal is now nextt (next c1) t i = nextt (next c2) t i
    apply ih
    intro j hj
    unfold CellAutomaton.next
    congr 1
    · apply h
      constructor <;> omega
    · apply h
      constructor <;> omega
    · apply h
      constructor <;> omega

theorem list_map_congr {α β} {f g : α → β} {l : List α} (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
  simp only [List.map_cons, List.cons.injEq]
  constructor
  · apply h; simp
  · apply ih; intro x hx; apply h; simp [hx]

lemma scan_temporal_independence {α: Type u} [Alphabet α] (C: LCellAutomaton α) (p s: Word α):
  (C.scan_temporal (List.append p s)).take p.length = C.scan_temporal p := by
  unfold LCellAutomaton.scan_temporal
  rw [← List.map_take, List.take_range, min_eq_left (by simp)]
  apply list_map_congr
  intro t ht
  rw [List.mem_range] at ht
  apply nextt_congr
  intro j hj
  unfold LCellAutomaton.embed_word
  split_ifs with h1 h2
  · congr 1
    unfold Word.get'
    simp only [List.get_eq_getElem]
    apply List.getElem_append_left
  · exfalso; unfold Word.range at *; simp at *; omega
  · exfalso; unfold Word.range at *; simp at *; omega
  · rfl
end scan_lemmas
