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








namespace compress_by_3
  variable [Alphabet α] [Alphabet β]

  theorem compression1 (C: LCellAutomaton α):
      ∃ (C': LCellAutomaton α) (f: C'.Q → Option (C.Q × C.Q × C.Q)),
      ∀ w (t: ℕ) (p: ℤ),
        f (C'.comp w t p) =
          if p >= 0 ∧ t = 2 * p + 3
          then
            let i := (3 * p).natAbs;
            some (C.comp w (i) 0, C.comp w (i + 1) 0, C.comp w (i + 2) 0)
          else none
          := by
    sorry

end compress_by_3



namespace speedup_factor_k
  variable [Alphabet α] [Alphabet β]

  variable {Q: Type}
  variable (k: ℕ) [NeZero k]

  def compress (c: Config Q): Config (Fin k → Q) :=
    fun p => fun j => c (p * k + j)

  def decompress (c: Config (Fin k → Q)): Config Q :=
    fun p => c (p / k) (Fin.intCast p)

  lemma compress_decompress (c: Config Q):
      decompress k (compress k c) = c := by
        sorry

  variable (C: CellAutomaton)

  def Q' := Fin k → C.Q

  def local_config (a b c: Q' k C): Config C.Q :=
      fun p => if p <= -k then a (Fin.intCast 0) else
        if p < 0 then a (Fin.intCast (p + k))
        else if p < k then b (Fin.intCast p)
        else c (Fin.intCast (p - k))

  def to_local_config (c: Config (C.Q)): Q' k C := fun j => c j

  def C': CellAutomaton := {
    Q := Fin k → C.Q
    δ := fun a b c =>
      to_local_config k C (C.nextt (local_config k C (a) (b) (c)) k)
  }



  lemma compression_k_step (c: Config C.Q):
      (C' k C).next (compress k c) = compress k (C.nextt c k) :=
        sorry

  theorem spec (c: Config C.Q):
      ∀ t, (C' k C).nextt (compress k c) t = compress k (C.nextt c (k * t)) :=
        sorry

end speedup_factor_k



namespace simulation
  structure Params where
    C_inr: CellAutomaton
    C_ctl: CellAutomaton
    f: C_ctl.Q → Option C_inr.Q

  variable (e: Params)
/-

  structure Q1 where
    state: e.C_ctl.Q
    counter: Fin 3
  deriving Inhabited, DecidableEq, Fintype

  instance [Alphabet α] : Alphabet (Option α) := {}
  instance : Alphabet (Q1 e) := {}

  def C': CellAutomaton := {
    Q := Option (Q1 e × e.C_inr.Q)
    δ := fun a b c =>
      match (a, b, c) with
      | (some qa, some (qb, _), some qc) =>
        if qb.counter = 2
        then sorry
        else none
      | _ => none
  }

  variable (c_ctl: Config e.C_ctl.Q)
  variable (c_inr: Config e.C_inr.Q)
  variable (h_CM: ∀ (t: ℕ) (p: ℤ),
    e.f (e.C_ctl.nextt c_ctl t p) =
      if t = 3 + 2 * p.natAbs then some (c_inr p)
      else none
  )


  def to_C'Q: e.C_ctl.Q → (C' e).Q := sorry
  def to_CinrQ: (C' e).Q → e.C_inr.Q := sorry

  theorem spec: ∀ (t: ℕ) (p: ℤ),
    let c' := (to_C'Q e) ∘ c_ctl
    let proj := to_CinrQ e;
    let C' := C' e
    proj (C'.nextt c' (3 + 3 * t) 0) = e.C_inr.nextt c_inr t 0 := by
      sorry
-/
end simulation









def CArtTransducer.compose [Alphabet α] [Alphabet β] [Alphabet γ] (t1: CArtTransducer β γ) (t2: CArtTransducer α β):
    CArtTransducer α γ :=
  sorry

def CArtTransducer.compose_spec [Alphabet α] [Alphabet β] [Alphabet γ]
    {t1: CArtTransducer β γ} {t2: CArtTransducer α β}:
    (CArtTransducer.compose t1 t2).advice.f =
      t1.advice.f ∘ t2.advice.f := by
        sorry
