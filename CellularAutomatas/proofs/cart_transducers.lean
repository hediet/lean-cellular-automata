import CellularAutomatas.defs
import Mathlib.Data.List.Basic

private lemma list_map_congr {α β} {f g : α → β} {l : List α} (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
  simp only [List.map_cons, List.cons.injEq]
  constructor
  · apply h; simp
  · apply ih; intro x hx; apply h; simp [hx]


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

theorem LCellAutomaton.scan_temporal_independence [Alphabet α] (C: LCellAutomaton α) (p s: Word α):
  (C.scan_temporal_rt (p ++ s)).take p.length = C.scan_temporal_rt p := by
  unfold LCellAutomaton.scan_temporal_rt LCellAutomaton.scan_temporal
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

theorem CArtTransducer.scan_temporal_independence [Alphabet α] [Alphabet Γ] (C: CArtTransducer α Γ) (p s: Word α):
  (C.advice.f (p ++ s)).take p.length = C.advice.f p := by
  unfold CArtTransducer.advice
  simp
  rw [←List.map_take]
  rw [LCellAutomaton.scan_temporal_independence]
