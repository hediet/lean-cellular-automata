import CellularAutomatas.defs
import CellularAutomatas.proofs.scan_lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open TwoStageAdvice

variable {α: Type u} [Alphabet α]
variable {Γ: Type u} [Alphabet Γ]

def rel_repr (adv: Advice α Γ) (p s: Word α) := (adv.f (p.append s)).take p.length

lemma two_stage_rel_repr_eq (adv: TwoStageAdvice α Γ) (p s: Word α):
    rel_repr adv.advice p s =
        (adv.M.scanr_q
            (adv.C.scan_temporal p)
            (adv.M.scanr_reduce
                ((adv.C.scan_temporal (List.append p s)).drop p.length)
            )
        ).map adv.t
          := by
    dsimp [rel_repr, TwoStageAdvice.advice]
    rw [← List.map_take]
    congr 1
    let W := adv.C.scan_temporal (List.append p s)
    change (adv.M.scanr W).take p.length = _
    have h_split : W = W.take p.length ++ W.drop p.length := (List.take_append_drop p.length W).symm
    conv in (adv.M.scanr W) => rw [h_split]
    have h_indep : W.take p.length = adv.C.scan_temporal p := by
      simp [W]
      change (adv.C.scan_temporal (List.append p s)).take p.length = _
      erw [scan_temporal_independence (p := p) (s := s)]
    rw [h_indep]
    have h_len_p : (adv.C.scan_temporal p).length = p.length := by
      rw [LCellAutomaton.scan_temporal]
      simp only [List.length_map, List.length_range]
    conv => lhs; arg 1; rw [← h_len_p]
    erw [@scanr_append_take _ _ adv.M (adv.C.scan_temporal p) (W.drop p.length)]
    simp [W]

def possible_advice_prefixes (adv: TwoStageAdvice α Γ) (p: Word α) : Finset (List Γ) :=
  Finset.univ.image (fun q : adv.M.Q => (adv.M.scanr_q (adv.C.scan_temporal p) q).map adv.t)

lemma two_stage_restriction_cardinality (adv: TwoStageAdvice α Γ) (p: Word α) :
  (possible_advice_prefixes adv p).card ≤ Fintype.card adv.M.Q := by
  unfold possible_advice_prefixes
  apply le_trans (Finset.card_image_le)
  simp

lemma two_stage_advice_in_possible (adv: TwoStageAdvice α Γ) (p s: Word α) :
  rel_repr adv.advice p s ∈ possible_advice_prefixes adv p := by
  rw [two_stage_rel_repr_eq]
  unfold possible_advice_prefixes
  simp

lemma middle_idx_mul_two (n : ℕ) : middle_idx (2 * n) = n := by
  unfold middle_idx
  simp

def marker_list (n pos : ℕ) : List Bool :=
  (List.range n).map (fun i => i + 1 == pos)

lemma marker_list_len (n pos : ℕ) : (marker_list n pos).length = n := by
  simp [marker_list]



lemma marker_list_take {n m k : ℕ} (h_le : m ≤ n) :
  (marker_list n k).take m = marker_list m k := by
  unfold marker_list
  rw [← List.map_take]
  rw [List.take_range]
  rw [min_eq_left h_le]




theorem middle_not_two_stage_advice : ¬ (Advice.middle α).is_two_stage_advice := by sorry
