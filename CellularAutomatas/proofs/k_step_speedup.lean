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
import CellularAutomatas.proofs.dead_border

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









section

  def φ {C: CellAutomaton α？ β} (b: C.Q) (c: C.Q) := (b, fun a => C.δ a b c)

  def Sp (C: CellAutomaton α？ β): CellAutomaton α？ (C.Q -> β) := by
    exact {
      Q := C.Q × (C.Q → C.Q)
      δ := fun a b c => φ (C.δ a.fst b.fst c.fst) (c.snd b.fst),
      embed a := φ (C.embed a) C.border,
      project qc := fun l => C.project (qc.snd l),
    }

  variable {C: CellAutomaton α？ β}

  private lemma fst_prop {w: Word α} (t: ℕ) (i: ℤ):
      ((Sp C).nextt w t i).fst = C.nextt w t i := by
    induction t generalizing i with
    | zero =>
      simp [Sp, φ, embed_word_at_eq]
    | succ t ih =>
      simp [CellAutomaton.next]
      set c := (Sp C).nextt (CellAutomaton.embed_word w) t
      simp [Sp, φ, ih]


  private lemma snd_prop (w: Word α) (t: ℕ) (i: ℤ) (h: t + i + 1 ≥ w.length):
    ((Sp C).nextt w t i).snd (C.nextt w t (i - 1)) = C.nextt w (t + 1) i := by

    induction t generalizing i with
    | zero =>
      rw [CellAutomaton.nextt_succ, nextt0, nextt0]

      have cp1_border : (CellAutomaton.embed_word w) (i+1) = C.border := by
        have: i + 1 ∉ w.range := by simp [Word.range]; omega
        simp_all [CellAutomaton.border, embed_word_at_eq2]

      simp [Sp, φ, cp1_border, CellAutomaton.next, embed_word_at_eq]


    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next]

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

  lemma spec (w: Word α) (t: ℕ) (h: t + 1 ≥ w.length):
    ((Sp C).trace w t) (C.nextt w t (-1)) = C.trace w (t + 1) := by
    unfold CellAutomaton.trace CellAutomaton.comp
    simp only [Function.comp_apply]
    unfold CellAutomaton.project_config Sp
    simp only
    have := snd_prop (C := C) w t 0 (by simp; omega : (t : ℤ) + 0 + 1 ≥ w.length)
    simp only at this
    convert congrArg C.project this using 2

end

def SpB (C: CellAutomaton α？ β) := (Sp C).map_project (fun q => q C.border)

def SpBk (k: ℕ) (C: CellAutomaton α？ β) := (SpB)^[k] C

-- dead implies left_dead
lemma dead_implies_left_dead {C: CellAutomaton α？ β} (h: C.dead C.border): C.left_dead C.border := by
  intro a b c ⟨ha, hb⟩
  exact h a b c hb

-- All positions to the left of 0 stay as border when border is left_dead
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

-- SpB speeds up by 1 step when the condition t + 1 ≥ w.length holds
lemma SpB_trace_eq {C: CellAutomaton α？ β} (h: C.left_dead C.border) (w: Word α) (t: ℕ) (ht: t + 1 ≥ w.length):
    (SpB C).trace w t = C.trace w (t + 1) := by
  simp only [SpB, trace_of_map_project, Function.comp_apply]
  have h_neg1 : C.nextt w t (-1) = C.border := left_dead_border_left h w t (-1) (by omega)
  conv_lhs => rw [←h_neg1]
  exact spec w t ht

-- DeadBorder wrapper function: takes an automaton and wraps it with DeadBorder
def withDeadBorder (c_val: ℕ) (C: CellAutomaton α？ β) [Alphabet α]: CellAutomaton α？ β :=
  let db : DeadBorder := { c := c_val, C_orig := C }
  db.C

-- DeadBorder.C has dead border by construction
lemma withDeadBorder_dead_border [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β):
    (withDeadBorder c_val C).dead (withDeadBorder c_val C).border :=
  DeadBorder.spec_left_border_dead

-- DeadBorder.C has left_dead border
lemma withDeadBorder_left_dead [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β):
    (withDeadBorder c_val C).left_dead (withDeadBorder c_val C).border :=
  dead_implies_left_dead (withDeadBorder_dead_border c_val C)

-- DeadBorder preserves trace within bounds
lemma withDeadBorder_trace_eq [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β) (w: Word α) (t: ℕ)
    (h_bound: t < c_val * w.length):
    (withDeadBorder c_val C).trace w t = C.trace w t := by
  unfold withDeadBorder
  let db : DeadBorder := { c := c_val, C_orig := C }
  exact @DeadBorder.spec_comp_trace db w t h_bound

-- SpB applied to DeadBorder.C then wrapped again - one step of speedup
def SpBD [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β): CellAutomaton α？ β :=
  withDeadBorder c_val (SpB (withDeadBorder c_val C))

-- k iterations of SpBD
def SpBDk [Alphabet α] (c_val k: ℕ) (C: CellAutomaton α？ β): CellAutomaton α？ β :=
  (SpBD c_val)^[k] C

-- Main speedup lemma using DeadBorder at each step
lemma SpBD_trace_eq [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β) (w: Word α) (t: ℕ)
    (ht: t + 1 ≥ w.length) (h_bound: t + 1 < c_val * w.length):
    (SpBD c_val C).trace w t = C.trace w (t + 1) := by
  unfold SpBD
  -- withDeadBorder c_val (SpB (withDeadBorder c_val C)).trace w t
  -- = C.trace w (t + 1)

  -- Step 1: inner DeadBorder has left_dead border
  set C1 := withDeadBorder c_val C
  have h_C1_left_dead : C1.left_dead C1.border := withDeadBorder_left_dead c_val C

  -- Step 2: SpB of C1 speeds up by 1
  have h_spb : (SpB C1).trace w t = C1.trace w (t + 1) := SpB_trace_eq h_C1_left_dead w t ht

  -- Step 3: relate C1.trace to C.trace using DeadBorder preservation
  have h_db_trace : C1.trace w (t + 1) = C.trace w (t + 1) :=
    withDeadBorder_trace_eq c_val C w (t + 1) h_bound

  -- Step 4: outer DeadBorder doesn't change trace within bounds
  have h_outer : (withDeadBorder c_val (SpB C1)).trace w t = (SpB C1).trace w t :=
    withDeadBorder_trace_eq c_val (SpB C1) w t (by omega)

  rw [h_outer, h_spb, h_db_trace]

-- k-step speedup using DeadBorder at each iteration
lemma SpBDk_trace_eq [Alphabet α] (c_val k: ℕ) (C: CellAutomaton α？ β) (w: Word α) (t: ℕ)
    (ht: t + 1 ≥ w.length) (h_bound: t + k < c_val * w.length):
    (SpBDk c_val k C).trace w t = C.trace w (t + k) := by
  unfold SpBDk
  induction k generalizing t with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.add_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    -- (SpBD c_val ((SpBD c_val)^[k] C)).trace w t = C.trace w (t + k + 1)
    set Ck := (SpBD c_val)^[k] C
    have h_step : (SpBD c_val Ck).trace w t = Ck.trace w (t + 1) := by
      apply SpBD_trace_eq
      · exact ht
      · omega
    rw [h_step]
    rw [ih (t + 1) (by omega) (by omega)]
    ring_nf

structure SpeedupKSteps where
  {α: Type}
  {β: Type}
  [inst1: Alphabet α]
  [inst2: Alphabet β]
  C_orig: CellAutomaton α？ β
  k: ℕ
  c: ℕ  -- speedup factor bound (from DeadBorder)

attribute [instance] SpeedupKSteps.inst1
attribute [instance] SpeedupKSteps.inst2


namespace SpeedupKSteps

  variable (e: SpeedupKSteps)

  -- The speedup automaton: k iterations of SpBD
  def C : CellAutomaton e.α？ e.β := SpBDk e.c e.k e.C_orig

  theorem spec (w: Word e.α) (i: ℕ) (h_len: i ≥ w.length - 1) (h_bound: i + e.k < e.c * w.length):
      e.C.trace w i = e.C_orig.trace w (i + e.k) := by
    exact SpBDk_trace_eq e.c e.k e.C_orig w i (by omega) h_bound

end SpeedupKSteps
end CellularAutomatas
