import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import CellularAutomatas.defs
import CellularAutomatas.proofs.cart_transducers
import CellularAutomatas.proofs.finite_state_transducers


--def extend_word_to k: Word α → Word (Option α)
/-
def Lk L k := sorry


lemma X (Ls1 Ls2: Set (Language α))
  (h1: P Ls1) (h2: P Ls2)
  (h: ∀ L ∈ ℒ CA_rt, ∃ L2 ∈ Ls2, (∀ w ∈ L, w.length.div k) → w ∈ L2):
    ∀ α, Ls1 α ⊆ Ls2 α := sorry

Let L ∈ Ls1.

-/


lemma tCellAutomatonWithAdvice.elem_L_iff {O: tCellAutomatonWithAdvice α}:
  w ∈ O.L ↔ (O.adv.annotate w) ∈ O.C.L := by rfl

lemma tCellAutomaton.elem_L_iff {C: tCellAutomaton α}:
  w ∈ C.L ↔ C.F_pos ((C.comp w (C.t w.length)) 0) := by rfl

@[simp]
lemma scan_temporal_length {C: LCellAutomaton α} (w : Word α) :
  (C.scan_temporal_rt w).length = w.length := by
  unfold LCellAutomaton.scan_temporal_rt LCellAutomaton.scan_temporal
  simp


lemma scan_temporal_in_F_pos {C: tCellAutomaton α} (hC: C ∈ CA_rt α) {w: Word α} (i: Nat) (h: i < (C.scan_temporal_rt w).length ):
    C.F_pos (C.scan_temporal_rt w)[i] = true ↔ w.take (i+1) ∈ C.L := by
  rw [scan_temporal_length] at h
  have h_len : i < w.length := h
  have h_take_len : (w.take (i+1)).length = i + 1 := by
    rw [List.length_take]
    rw [min_eq_left]
    omega
  have h_t : C.t (w.take (i+1)).length = i := by
    simp [CA_rt, t_rt] at hC
    rw [hC.2]
    rw [h_take_len]
    simp
  dsimp [tCellAutomaton.L, Membership.mem, Set.Mem]
  rw [h_t]
  unfold LCellAutomaton.scan_temporal_rt LCellAutomaton.scan_temporal
  rw [List.getElem_map]
  simp
  congr 1
  apply nextt_congr
  intro j hj
  unfold LCellAutomaton.embed_word
  split_ifs with h1 h2
  · -- j in range of w and w.take
    unfold Word.get'
    simp
  · -- j in range of w but not w.take
    unfold Word.range at *
    simp at *
    grind
  · -- j not in range of w but in range of w.take
    unfold Word.range at *
    simp at *
    grind
  · -- neither
    rfl

def ProdCA (α: Type) (β: Type) [DecidableEq β] [Fintype β] (f: β → LCellAutomaton α): LCellAutomaton α := {
  Q := ∀ b: β, (f b).Q
  δ := fun qL qC qR a => (f a).δ (qL a) (qC a) (qR a)
  embed := fun a b => (f b).embed a
  border := fun b => (f b).border
}

namespace ProdCA


variable {β: Type} [Alphabet β]
variable {f: β → LCellAutomaton α}

lemma comp (f: β → LCellAutomaton α)
    (w: Word α) (t: ℕ) (i: ℤ):
    (ProdCA α β f).comp w t i = fun b => (f b).comp w t i := by
  unfold LCellAutomaton.comp
  unfold CellAutomaton.nextt

  have nextt_proj (c: Config (ProdCA α β f).Q) (t: ℕ) (i: ℤ) (b: β):
      (ProdCA α β f).next^[t] c i b = (f b).next^[t] (fun j => c j b) i := by
    induction t generalizing i c with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ]
      rw [Function.iterate_succ]
      dsimp
      rw [ih]
      dsimp [CellAutomaton.next, ProdCA]
      rfl

  funext b
  simp [apply_iterated]
  rw [nextt_proj]
  apply congr_arg (fun c => (f b).next^[t] c i)
  funext j
  unfold LCellAutomaton.embed_word
  dsimp [ProdCA]
  split_ifs <;> rfl


-- zipMany over { x => [a, b, c], y => [1, 2, 3] } should be  [ {x => a, y => 1}, {x => b, y => 2}, {x => c, y => 3} ]

def zipMany {γ: β -> Type v} [∀ b, Inhabited (γ b)] (f: (b: β) → Word (γ b)) : Word ((b: β) -> (γ b)) :=
  let n := (f default).length
  (List.range n).map fun i => fun b => (f b).getD i default

lemma zipMany_get? {γ: β -> Type v} [∀ b, Inhabited (γ b)] (f: (b: β) → Word (γ b)) (i: ℕ):
    (ProdCA.zipMany f)[i]? = if i < (f default).length then some (fun b => (f b).getD i default) else none := by
  simp [zipMany]
  grind

lemma scan_temporal (f: β → LCellAutomaton α) (w: Word α):
    (ProdCA α β f).scan_temporal t p w = zipMany (fun b => (f b).scan_temporal t p w) := by
  unfold LCellAutomaton.scan_temporal
  simp [zipMany]
  intro t ht
  funext b
  rw [comp]
  grind

end ProdCA

open Classical


attribute [ext] Advice

variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]

def L_c (adv: Advice α Γ) (c: Γ) : Language α :=
  { w | (adv.f w).getLast? = some c }

namespace LcInRt

def DiagonalShiftCA (A : Type) [Alphabet A] : LCellAutomaton A := {
  Q := Option A
  δ := fun _ _ r => r
  embed := some
  border := none
}

@[simp]
lemma DiagonalShiftCA_comp_p0  (w : Word α) :
  (DiagonalShiftCA α).comp w t 0 = w[t]? := by
  unfold LCellAutomaton.comp

  have shift_next c : (DiagonalShiftCA α).next c = fun i => c (i + 1) := by
    funext i
    simp [CellAutomaton.next, DiagonalShiftCA]

  have shift_nextt k c i: ((DiagonalShiftCA α).nextt c k) i = c (i + k) := by
    induction k generalizing c with
    | zero =>
      simp [CellAutomaton.nextt, apply_iterated]
    | succ k ih =>
      rw [CellAutomaton.nextt, apply_iterated]
      simp only [Nat.iterate]
      rw [shift_next]
      rw [← apply_iterated]
      rw [← CellAutomaton.nextt]
      rw [ih]
      simp
      ring_nf

  rw [shift_nextt]
  unfold LCellAutomaton.embed_word
  dsimp [DiagonalShiftCA]
  unfold Word.get'
  unfold Word.range
  grind

lemma DiagonalShiftCA_scan_temporal {Q : Type} [Alphabet Q] (w : Word Q) :
  (DiagonalShiftCA Q).scan_temporal_rt w = w.map some := by
  unfold LCellAutomaton.scan_temporal_rt LCellAutomaton.scan_temporal
  apply List.ext_getElem
  · simp
  · intro i h_i h_len
    simp [←getElem?_pos]


def AdvCALc (c : Γ) : tCellAutomaton (α × Γ) := {
  toLCellAutomaton := DiagonalShiftCA (α × Γ)
  t := fun n => n - 1
  p := fun _ => 0
  F_pos := fun q => match q with
    | some (_, g) => g == c
    | none => false
}

lemma myCA_in_rt (c : Γ) : AdvCALc c ∈ CA_rt (α × Γ) := by
  simp [CA_rt, t_rt, AdvCALc, tCellAutomatons, CA]

lemma scan_temporal_get_last {C: tCellAutomaton α} (w : Word α):
  (C.scan_temporal_rt w).getLast? = if w = [] then none else ((C.comp w (w.length - 1)) 0) := by
  cases h_w : w.length with
  | zero =>
    simp [LCellAutomaton.scan_temporal_rt, LCellAutomaton.scan_temporal]
    have h_nil : w = [] := List.length_eq_zero_iff.mp h_w
    subst h_nil
    unfold LCellAutomaton.comp
    unfold LCellAutomaton.embed_word
    simp
  | succ n =>
    have h_len_pos : w.length > 0 := by rw [h_w]; simp
    have h_scan_len : (C.scan_temporal_rt w).length = w.length := scan_temporal_length w
    have h_scan_pos : (C.scan_temporal_rt w).length > 0 := by rw [h_scan_len]; exact h_len_pos

    rw [List.getLast?_eq_some_getLast (List.ne_nil_of_length_pos h_scan_pos)]
    simp
    rw [List.getLast_eq_getElem]
    unfold LCellAutomaton.scan_temporal_rt LCellAutomaton.scan_temporal
    simp
    grind


def O (adv : Advice α Γ) (c : Γ) : tCellAutomatonWithAdvice α := ⟨Γ, adv, AdvCALc c⟩

lemma O_L_eq_L_c (adv : Advice α Γ) (c : Γ) : (O adv c).L = L_c adv c := by
  ext w
  simp [tCellAutomatonWithAdvice.L, L_c]
  let w_ann := adv.annotate w
  have h_len : w_ann.length = w.length := by
    simp [w_ann, Advice.annotate, zip_words, adv.len]

  change (AdvCALc c).F_pos ((AdvCALc c).comp w_ann ((AdvCALc c).t w_ann.length) 0) ↔ (adv.f w).getLast? = some c
  dsimp [AdvCALc]
  rw [DiagonalShiftCA_comp_p0]

  cases h_w : w.length with
  | zero =>
    have h_nil : w = [] := List.length_eq_zero_iff.mp h_w
    subst h_nil
    have h_ann_nil : w_ann = [] := by simp [w_ann, Advice.annotate, zip_words]
    rw [h_ann_nil]
    simp
    have h_f_nil : adv.f [] = [] := by
      have := adv.len []
      simp at this
      exact this
    rw [h_f_nil]
    simp
  | succ n =>
    have h_ann_len_pos : w_ann.length > 0 := by rw [h_len, h_w]; simp
    have h_idx : w_ann.length - 1 < w_ann.length := by omega

    rw [List.getElem?_eq_getElem (h:=h_idx)]
    simp

    have h_idx_f : (adv.f w).length - 1 < (adv.f w).length := by
      rw [adv.len]
      rw [h_len] at h_idx
      exact h_idx

    have h_snd : (w_ann[w_ann.length - 1]).2 = (adv.f w)[(adv.f w).length - 1] := by
      simp [w_ann, Advice.annotate, zip_words]
      simp [adv.len]

    rw [h_snd]

    have h_f_ne : adv.f w ≠ [] := by
      rw [← List.length_pos_iff_ne_nil]
      rw [adv.len, h_w]
      simp

    rw [List.getLast?_eq_some_getLast h_f_ne]
    rw [List.getLast_eq_getElem]
    simp


end LcInRt

lemma L_c_in_rt (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) :
      ∃ M : tCellAutomaton α, M ∈ CA_rt α ∧ M.L = L_c adv c := by
  let O := LcInRt.O adv c
  have h_in : O.L ∈ ℒ (CA_rt (α × Γ) + adv) := by
    use O
    constructor
    · change O ∈ tCellAutomatonWithAdvice.with_advice (CA_rt (α × Γ)) adv
      simp [tCellAutomatonWithAdvice.with_advice]
      use LcInRt.AdvCALc c
      exact ⟨LcInRt.myCA_in_rt c, rfl⟩
    · rfl

  erw [h] at h_in
  rcases h_in with ⟨M, hM_in, hM_L⟩
  use M
  constructor
  · exact hM_in
  · change DefinesLanguage.L M = L_c adv c
    rw [← hM_L, LcInRt.O_L_eq_L_c]

noncomputable def CALc (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) : tCellAutomaton α :=
  Classical.choose (L_c_in_rt adv h c)

lemma CALc_spec_1 (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) :
    (CALc adv h c) ∈ CA_rt α :=
  (Classical.choose_spec (L_c_in_rt adv h c)).1

lemma CALc_spec_2 (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) :
    (CALc adv h c).L = L_c adv c :=
  (Classical.choose_spec (L_c_in_rt adv h c)).2



namespace PrefixStableProof

  variable (adv: Advice α Γ) (h1: adv.rt_closed)

  noncomputable abbrev M_prod := ProdCA α Γ (fun c => (CALc adv h1 c).toLCellAutomaton)

  noncomputable def t_map (q: (M_prod adv h1).Q) : Γ :=
    let valid_c := Finset.univ.filter (fun c => (CALc adv h1 c).F_pos (q c))
    valid_c.toList.head?.getD default



  noncomputable def ts_adv : TwoStageAdvice α Γ := {
    C := ⟨ M_prod adv h1, t_map adv h1 ⟩
    β := Γ
    M := id_transducer Γ
  }

  lemma getLastOfTake (h: i < w.length): (List.take (i + 1) w).getLast? = w[i]? := by
    grind

  lemma f (h2: adv.prefix_stable): (ts_adv adv h1).advice = adv := by
    apply Advice.ext
    funext w
    simp [TwoStageAdvice.advice]
    unfold ts_adv
    simp

    unfold CArtTransducer.advice
    simp [LCellAutomaton.scan_temporal_rt]
    rw [ProdCA.scan_temporal]
    conv =>
      pattern LCellAutomaton.scan_temporal _ _ _ _
      rw [←LCellAutomaton.scan_temporal_rt]

    apply List.ext_getElem?

    intro i
    rw [List.getElem?_map]
    erw [ProdCA.zipMany_get?]
    simp

    by_cases h_i : i < w.length
    case neg => simp [h_i, Advice.len]

    unfold t_map
    simp


    simp [scan_temporal_in_F_pos (CALc_spec_1 adv h1 _), h_i]
    simp [CALc_spec_2 adv h1]
    unfold L_c

    have h2 := h2 w (i+1)

    -- TODO@lean: This is annoying
    suffices
      some ((Finset.univ.filter (fun c => List.getLast? (adv.f (List.take (i + 1) w)) = some c)).toList.head?.getD default) = (adv.f w)[i]? by
        grind

    rw [h2]
    have : i < (adv.f w).length := by
      simp [h_i, adv.len]

    rw [getLastOfTake this]

    rw [List.getElem?_eq_getElem this]
    simp
    have h_singleton : (Finset.univ.filter (fun c => (adv.f w)[i] = c)) = {(adv.f w)[i]} := by grind
    rw [h_singleton]
    simp


end PrefixStableProof



theorem is_two_stage_of_rt_closed_and_prefix_stable (adv: Advice α Γ) (h1: adv.rt_closed) (h2: adv.prefix_stable):
    adv.is_two_stage_advice := by

    unfold Advice.is_two_stage_advice
    use PrefixStableProof.ts_adv adv h1
    simp [PrefixStableProof.f adv h1 h2]
