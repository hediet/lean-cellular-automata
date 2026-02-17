import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

section DeadBorder

  lemma dead_border_prop {α β : Type}
      (C: CellAutomaton (Option α) β) (h_dead: C.dead C.border)
      (w: Word α) (t: ℕ) (p: ℤ) (h_p: p ∉ w.range):
      C.nextt (C.embed_word w) t p = C.border := by
    induction t with
    | zero =>
      simp only [CellAutomaton.nextt_zero]
      rw [embed_word_at_eq2 (C:=C) w p h_p]
      rfl
    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next]
      apply h_dead
      exact ih


  lemma initial_border_prop {α β : Type}
      (C: CellAutomaton (Option α) β)
      (h_initial_border: C.initial C.border)
      (h: C.inj_embed none)
      (w: Word α) (t: ℕ) (p: ℤ) (h_p: p ∈ w.range):
      C.nextt (C.embed_word w) t p ≠ C.border := by
      induction t with
      | zero =>
        simp only [CellAutomaton.nextt_zero]
        rw [embed_word_at_eq1 (C:=C) w p h_p]
        unfold CellAutomaton.inj_embed at h
        grind [CellAutomaton.border]
      | succ t ih =>
        rw [CellAutomaton.nextt_succ]
        intro h
        apply ih
        rw [CellAutomaton.next] at h
        apply h_initial_border _ _ _ h

  lemma to_word_exists_generic {α : Type} [Inhabited α] {c: Config (Option α)} {len: ℕ}
    (h: ∀ p, (c p).isSome ↔ 0 ≤ p ∧ p < len):
    ∃ w': Word α, w'.length = len ∧ c = word_to_config w' := by

    set l := (List.range len).map (fun (i: ℕ) => (c i).get!)
    exists l

    constructor
    · simp [l]
    · funext p
      simp only [word_to_config]
      have h_len_l : l.length = len := by simp [l]
      by_cases hp: 0 ≤ p ∧ p < len
      · have hp_l : 0 ≤ p ∧ p < l.length := by rw [h_len_l]; exact hp
        simp_all
        simp_all [l]
        have : (c p).isSome := by
          grind

        rw [←Option.get_eq_get! (h := by simp_all)]
        rw [Option.some_get]

      · have hp_l : ¬(0 ≤ p ∧ p < l.length) := by rw [h_len_l]; exact hp
        rw [dif_neg hp_l]
        match hc : c p with
        | some v =>
           have : (c p).isSome := by simp [hc]
           rw [h] at this
           contradiction
        | none => rfl

end DeadBorder


section LeftDead

  lemma dead_implies_left_dead {C: CellAutomaton α？ β} (h: C.dead C.border): C.left_dead C.border := by
    intro a b c ⟨ha, hb⟩
    exact h a b c hb

  lemma left_dead_border_left {C: CellAutomaton α？ β} (h: C.left_dead C.border) (w: Word α) (t: ℕ) (p: ℤ) (hp: p < 0):
      C.nextt w t p = C.border := by
    induction t generalizing p with
    | zero =>
      simp only [nextt0]
      have : p ∉ w.range := by simp [Word.range]; omega
      rw [embed_word_at_eq2 w p this]
      rfl
    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next]
      apply h
      constructor
      · exact ih (p - 1) (by omega)
      · exact ih p hp

end LeftDead


section BorderStaysRight

  variable {α β : Type} [Alphabet α]

  omit [Alphabet α] in
  lemma CellAutomaton.quiescent_δ {C : CellAutomaton α？ β} (h : C.quiescent C.border) :
      C.δ C.border C.border C.border = C.border := by
    unfold CellAutomaton.quiescent CellAutomaton.quiescent_set at h
    exact h ⟨C.border, rfl⟩ ⟨C.border, rfl⟩ ⟨C.border, rfl⟩

  omit [Alphabet α] in
  theorem CellAutomaton.border_stays_right (C : CellAutomaton α？ β)
      (h_left_indep : C.left_independent) (h_quiescent : C.quiescent C.border)
      (w : Word α) (i : ℤ) (hi : i ≥ w.length) (t : ℕ) :
      C.nextt (CellAutomaton.embed_word w) t i = C.border := by
    induction t generalizing i with
    | zero =>
      simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_word, CellAutomaton.embed_config,
                 word_to_config, CellAutomaton.border]
      split_ifs with h
      · omega
      · rfl
    | succ t iht =>
      simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
      have hm := iht i hi
      have hr := iht (i + 1) (by omega)
      rw [hm, hr, h_left_indep _ _ _ C.border]
      exact C.quiescent_δ h_quiescent

end BorderStaysRight

end CellularAutomatas
