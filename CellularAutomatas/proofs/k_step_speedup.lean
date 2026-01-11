import CellularAutomatas.defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Linarith
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

section Causal

/-- A function is Causal if the output prefix depends only on the input prefix of the same length,
    and it preserves the length of the word (synchronous). -/
def IsCausal (f: Word α → Word β): Prop := ∀ w, (f w).length = w.length ∧ ∀ i, f (w.take i) = (f w).take i

lemma is_causal_len (h: IsCausal f) w: (f w).length = w.length := (h w).1

@[simp]
lemma is_causal_empty (h: IsCausal f): (f []) = [] := by
  have := (h []).1
  simp_all

@[simp]
lemma comp_is_causal {α β γ} (f: Word α → Word β) (g: Word β → Word γ)
    (hf: IsCausal f) (hg: IsCausal g): IsCausal (g ∘ f) := by
  intro w
  constructor
  · simp only [Function.comp_apply, (hg _).1, (hf _).1]
  · intro i
    simp only [Function.comp_apply]
    rw [(hf w).2 i, (hg _).2 i]

@[simp]
lemma take_of_concat_is_causal (h: IsCausal f) (v w: Word _): (f (v ++ w))⟦*..v.length⟧ = f v := by
  rw [← (h (v ++ w)).2 v.length]
  simp

lemma word_getElem_eq_take_getLast (w: Word α) (h: i < w.length): w[i] = (w.take (i + 1)).getLast (by simp; grind) := by
  grind

lemma eq_of_is_causal (f g: Word α → Word β) (h1: IsCausal f) (h2: IsCausal g):
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



@[simp]
lemma trace_is_causal {α β} [Alphabet α] [Alphabet β] (C: CellAutomaton α？ β): IsCausal C.trace_rt := by
  intro w
  constructor
  · apply trace_rt_len
  · intro i
    let p := w.take i
    let s := w.drop i
    conv =>
      rhs
      rw [(List.take_append_drop i w).symm]
    change C.trace_rt p = (C.trace_rt (p ++ s)).take i
    rw [←LCellAutomaton.scan_temporal_independence C p s]
    apply List.ext_getElem
    · simp only [trace_rt_len, p, s, List.length_take, List.length_drop, List.length_append]
      omega
    · intro j h1 h2
      simp only [List.getElem_take]

end Causal




structure LeftBorderDead where
  {α: Type}
  {β: Type}
  [inst: Alphabet α]
  C_orig: CellAutomaton α？ β
  h_quiet: C_orig.δ C_orig.border C_orig.border C_orig.border = C_orig.border

attribute [instance] LeftBorderDead.inst

namespace LeftBorderDead

  variable (e: LeftBorderDead)

  def Q_fold := e.C_orig.Q × e.C_orig.Q

  instance : Alphabet (Q_fold e) := inferInstanceAs (Alphabet (e.C_orig.Q × e.C_orig.Q))


  def C: CellAutomaton e.α？ e.β := {
    Q := Option (Q_fold e),
    embed := fun
      | some a => some (e.C_orig.embed (some a), e.C_orig.border) -- p >= 0 starts with border at -(p+1)
      | none => none, -- p < 0 is dead
    project := fun
      | some (r, _) => e.C_orig.project r
      | none => e.C_orig.project e.C_orig.border, -- dummy
    δ := fun l c r =>
      match c with
      | none => none -- Dead zone stays dead
      | some (rc, lc) =>
        -- Neighbors for rc (at p)
        let left_of_rc := match l with
          | some (rl, _) => rl
          | none => lc -- Boundary: left of 0 is -1 (stored in lc)

        let right_of_rc := match r with
          | some (rr, _) => rr
          | none => e.C_orig.border -- Right border

        -- Neighbors for lc (at -(p+1))
        let left_of_lc := match r with
          | some (_, lr) => lr
          | none => e.C_orig.border -- Left border (deep negative)

        let right_of_lc := match l with
          | some (_, ll) => ll
          | none => rc -- Boundary: right of -1 is 0 (stored in rc)

        let rc' := e.C_orig.δ left_of_rc rc right_of_rc
        let lc' := e.C_orig.δ left_of_lc lc right_of_lc
        some (rc', lc')
  }


  lemma spec_comp_trace: e.C.trace = e.C_orig.trace := by
    sorry


  lemma spec_left_border_dead (w: Word e.α) (h: w ≠ []) (t: ℕ): e.C.nextt w t (-1) = e.C.border := by
    sorry

end LeftBorderDead






section

  private def φ {C: CellAutomaton α？ β} (b: C.Q) (c: C.Q) := (b, fun a => C.δ a b c)

  private def Sp (C: CellAutomaton α？ β): CellAutomaton α？ (C.Q -> β) := by
    exact {
      Q := C.Q × (C.Q → C.Q)
      δ := fun a b c => φ (C.δ a.fst b.fst c.fst) (c.snd b.fst),
      embed a := φ (C.embed a) C.border,
      project qc := fun l => C.project (qc.snd l),
    }

  variable {C: LCellAutomaton α}

  private lemma fst_prop {w: Word α} (t: ℕ) (i: ℤ):
      ((Sp C).nextt w t i).fst = C.nextt w t i := by
    induction t generalizing i with
    | zero =>
      simp [Sp, φ, embed_word_at_eq]
    | succ t ih =>
      simp [CellAutomaton.next]
      set c := (Sp C).nextt (embed_word w) t
      simp [Sp, φ, ih]


  private lemma snd_prop (w: Word α) (t: ℕ) (i: ℤ) (h: t + i + 1 ≥ w.length):
    ((Sp C).nextt w t i).snd (C.nextt w t (i - 1)) = C.nextt w (t + 1) i := by

    induction t generalizing i with
    | zero =>
      rw [LCellAutomaton.nextt_succ_eq, nextt0, nextt0]

      have cp1_border : (embed_word w) (i+1) = C.border := by
        have: i + 1 ∉ w.range := by simp [Word.range]; omega
        simp_all [CellAutomaton.border, embed_word_at_eq2]

      simp [Sp, φ, cp1_border, CellAutomaton.next, embed_word_at_eq]


    | succ t ih =>
      rw [LCellAutomaton.nextt_succ_eq, CellAutomaton.next]

      set c' := (Sp C).nextt w t
      set c := C.nextt w t

      conv in (Sp C).δ => dsimp [Sp]

      have this i : (c' i).1 = c i := by simp [c', c, fst_prop]
      rw [this]
      rw [this]
      rw [this]

      rw [←CellAutomaton.next]

      have ih := ih (i + 1) (by omega)
      rw [add_sub_cancel_right] at ih
      rw [ih]
      unfold φ
      simp
      rfl

  private lemma spec (w: Word α) (t: ℕ) (h: t + 1 ≥ w.length):
    ((Sp C).trace w t) (C.nextt w t (-1)) = C.trace w (t + 1) := by
    sorry

end




structure SpeedupKSteps where
  {α: Type}
  {β: Type}
  [inst1: Alphabet α]
  [inst2: Alphabet β]
  C_orig: CellAutomaton α？ β
  k: ℕ

attribute [instance] SpeedupKSteps.inst1
attribute [instance] SpeedupKSteps.inst2


namespace SpeedupKSteps

  variable (e: SpeedupKSteps)

  def C: CellAutomaton e.α？ e.β := sorry

  lemma inv (w: Word e.α): e.C.trace w w.length = e.C_orig.trace w (w.length + e.k) := by
    sorry

  theorem spec (w: Word e.α) (i: ℕ) (h_len: i ≥ w.length - 1): e.C.trace w i = e.C_orig.trace w (i + e.k) := by
    sorry

end SpeedupKSteps
end CellularAutomatas
