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
import CellularAutomatas.proofs.composition
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.finite_state_transducers

namespace CellularAutomatas


@[simp]
lemma adv_empty (adv : Advice α Γ) : adv.f [] = [] := by
  have h_len : (adv.f []).length = 0 := by simp [adv.len]
  rw [List.length_eq_zero_iff.mp h_len]


lemma tCellAutomatonWithAdvice.elem_L_iff {O: tCellAutomatonWithAdvice α}:
  w ∈ O.L ↔ (O.adv.annotate w) ∈ O.C.L := by rfl


-- Reconstruct a two stage advice from a rt-closed and prefix-stable advice

open Classical


variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]

def L_c (adv: Advice α Γ) (c: Γ) : Language α :=
  { w | (adv.f w).getLast? = some c }



/-





* L_c := { w | adv.f(w).getLast? = c }
* (prefix_mem L_c) is two_stage, because L_c is in L(RT-CA) by rt-closedness of adv
 h: adv.rt_closed
* ((⊗ fun c => prefix_mem_two_stage L_c h).map_project first_true_or_default).advice = adv
-/

--

namespace LcInRt


def AdvCALc (c : Γ) : tCellAutomaton (α × Γ) := {
  toCellAutomaton := (ca_id_word (α × Γ)).map_project (fun (_, g) => g == c)
  t := fun n => n - 1
  p := fun _ => 0
}

lemma myCA_in_rt (c : Γ) : AdvCALc c ∈ CA_rt (α × Γ) := by
  simp [CA_rt, t_rt, AdvCALc, tCellAutomata, CA]



def O (adv : Advice α Γ) (c : Γ) : tCellAutomatonWithAdvice α := ⟨Γ, adv, AdvCALc c⟩


lemma O_L_eq_L_c (adv : Advice α Γ) (c : Γ) : (O adv c).L = L_c adv c := by
  ext w
  simp [tCellAutomatonWithAdvice.L, L_c]
  let w_ann := adv.annotate w
  have h_len : w_ann.length = w.length := by
    simp [w_ann, Advice.annotate, zip_words, adv.len]

  change ((AdvCALc c).comp w_ann ((AdvCALc c).t w_ann.length) 0) ↔ (adv.f w).getLast? = some c
  dsimp [AdvCALc]
  rw [DiagonalShiftCA_comp_p0]

  cases h_w : w.length with
  | zero =>
    have h_nil : w = [] := List.length_eq_zero_iff.mp h_w
    subst h_nil
    have h_ann_nil : w_ann = [] := by simp [w_ann, Advice.annotate, zip_words]
    rw [h_ann_nil]
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

  noncomputable abbrev M_prod := ProdCA (fun c => (CALc adv h1 c).toCellAutomaton)

  noncomputable def first_true_or_default (q: Γ → Bool) : Γ :=
    let valid_c := Finset.univ.filter (fun c => q c)
    valid_c.toList.head?.getD default

  noncomputable def ts_adv : TwoStageAdvice α Γ := {
    C := (M_prod adv h1).map_project first_true_or_default
    β := Γ
    M := FiniteStateTransducer.M_id Γ
  }

  lemma getLastOfTake (h: i < w.length): (List.take (i + 1) w).getLast? = w[i]? := by
    grind

  lemma f (h2: adv.prefix_stable): (ts_adv adv h1).advice = adv := by
    apply Advice.ext
    funext w
    simp [TwoStageAdvice.advice]
    unfold ts_adv
    simp

    rw [ProdCA.trace_rt]

    apply List.ext_getElem?



    intro i
    rw [List.getElem?_map]
    erw [ProdCA.zipMany_get?]
    simp

    by_cases h_i : i < w.length
    case neg => simp [h_i]

    unfold first_true_or_default
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
