import CellularAutomatas.defs
import Mathlib.Data.List.Basic


def id_transducer (Q) [Alphabet Q]: FiniteStateTransducer Q Q := {
  Q := Q
  δ := fun _ a => a
  q0 := default
  f := id
}

@[simp]
lemma id_transducer_scanr_eq [Alphabet Q]:
  (id_transducer Q).scanr = id := by
  funext w
  simp [FiniteStateTransducer.scanr, FiniteStateTransducer.scanr_q]
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [FiniteStateTransducer.scanr_step]
    rw [ih]
    cases w <;> simp [id_transducer]

@[simp]
lemma id_transducer_advice_eq [Alphabet Q]:
  (id_transducer Q).advice.f = id := by
  simp [FiniteStateTransducer.advice]
  rfl


def FiniteStateTransducer.map_output [Alphabet α] [Alphabet β] [Alphabet γ]
    {M: FiniteStateTransducer α β} (g: β → γ): FiniteStateTransducer α γ := {
  Q := M.Q
  δ := M.δ
  q0 := M.q0
  f := g ∘ M.f
}


namespace FiniteStateTransducer

  variable {α β : Type} {M: FiniteStateTransducer α β}

  lemma scanr_foldr_state (p: Word α) (q: M.Q) (tail: List β):
      (p.foldr M.scanr_step (q, tail)).fst = M.scanr_reduce_q q p := by
    induction p generalizing q tail with
    | nil => simp [scanr_reduce_q]
    | cons a p' ih =>
      simp [scanr_step, scanr_reduce_q]
      rw [ih]

  lemma scanr_foldr_cons (p: Word α) (q: M.Q) (tail: List β):
      (p.foldr M.scanr_step (q, tail)).snd = (M.scanr_q p q) ++ tail := by
    induction p generalizing q tail with
    | nil =>
      simp [scanr_q]
    | cons a p' ih =>
      simp [scanr_q, scanr_step]
      rw [scanr_foldr_state]
      rw [scanr_foldr_state (tail := [])]
      rw [ih]
      simp [scanr_q]

  lemma scanr_q_append (p s: Word α) (q: M.Q):
      M.scanr_q (p ++ s) q = M.scanr_q p (M.scanr_reduce_q q s) ++ M.scanr_q s q := by
    unfold scanr_q
    rw [List.foldr_append]
    let res_s := s.foldr M.scanr_step (q, [])
    have h_fst : res_s.fst = M.scanr_reduce_q q s := by
      dsimp [res_s]
      rw [scanr_foldr_state]
    have h_snd : res_s.snd = M.scanr_q s q := rfl
    rw [scanr_foldr_cons]
    rw [h_fst]
    rfl

  lemma scanr_append_take (p s: Word α):
      (M.scanr (p ++ s)).take p.length = M.scanr_q p (M.scanr_reduce s) := by
    unfold scanr
    rw [scanr_q_append]
    apply List.take_left'
    simp

end FiniteStateTransducer
