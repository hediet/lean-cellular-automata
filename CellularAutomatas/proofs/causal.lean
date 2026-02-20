import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import Mathlib.Data.List.Basic

namespace CellularAutomatas

section Causal

@[simp]
lemma IsCausal.empty {α β: Type} {f: Word α → Word β} (h: IsCausal f): f [] = [] := by
  have := (h []).1
  simp_all

@[simp]
lemma IsCausal.comp {α β γ: Type} (f: Word α → Word β) (g: Word β → Word γ)
    (hf: IsCausal f) (hg: IsCausal g): IsCausal (g ∘ f) := by
  intro w
  constructor
  · simp only [Function.comp_apply, (hg (f w)).1, (hf w).1]
  · intro i
    simp only [Function.comp_apply]
    rw [(hf w).2 i, (hg _).2 i]

@[simp]
lemma IsCausal.take_of_concat {α β: Type} {f: Word α → Word β} (h: IsCausal f) (v w: Word α):
    (f (v ++ w))⟦*..v.length⟧ = f v := by
  rw [← (h (v ++ w)).2 v.length]
  simp

private lemma word_getElem_eq_take_getLast {α: Type} (w: Word α) {i: ℕ} (h: i < w.length):
    w[i] = (w.take (i + 1)).getLast (by simp; grind) := by
  grind

lemma IsCausal.eq_iff {α β: Type} (f g: Word α → Word β) (h1: IsCausal f) (h2: IsCausal g):
  (f = g) ↔ (∀ w, (f w).getLast? = (g w).getLast?) := by
  constructor
  · intro h w; simp [h]
  · intro h
    funext w
    apply List.ext_getElem ((h1 w).1.trans (h2 w).1.symm)
    intro i h_len _
    let w' := w.take (i + 1)
    have hw' : f w' = (f w).take (i+1) := by rw [(h1 w).2]
    have gw' : g w' = (g w).take (i+1) := by rw [(h2 w).2]
    have h_last := h w'
    rw [hw', gw'] at h_last

    rw [word_getElem_eq_take_getLast _ h_len]
    rw [word_getElem_eq_take_getLast _ (by rw [(h2 w).1, ←(h1 w).1]; exact h_len)]

    have ne_nil : (f w).take (i+1) ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_take]
      have : i < (f w).length := h_len
      omega

    have ne_nil_g : (g w).take (i+1) ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_take]
      rw [(h2 w).1, ←(h1 w).1]
      have : i < (f w).length := h_len
      omega

    rw [List.getLast?_eq_getLast_of_ne_nil ne_nil, List.getLast?_eq_getLast_of_ne_nil ne_nil_g] at h_last
    simp_all

lemma Advice.causal_iff {α Γ: Type} (adv: Advice α Γ): adv.causal ↔ IsCausal adv.f := by rfl

end Causal

end CellularAutomatas
