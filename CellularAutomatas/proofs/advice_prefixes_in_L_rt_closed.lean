import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs
import CellularAutomatas.proofs.scan_lemmas
import CellularAutomatas.proofs.fsm_lemmas

variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]


def CA_rt_to_TwoStage (C: CA_rt α): TwoStageAdvice α Bool :=
  {
    C := C.val.toLCellAutomaton
    M := LastInputFSM C.val.Q
    t := C.val.F_pos
  }

lemma CA_rt_to_TwoStage_eq (C: CA_rt α):
  (CA_rt_to_TwoStage C).advice.f = (Advice.prefixes_in_L C.val.L).f := by
  funext w
  simp only [CA_rt_to_TwoStage, TwoStageAdvice.advice, Advice.prefixes_in_L]
  rw [LastInputFSM_scanr_eq]
  apply List.ext_getElem
  · simp [LCellAutomaton.scan_temporal]
  · intro i h1 h2
    simp
    unfold LCellAutomaton.scan_temporal
    rw [List.getElem_map]
    simp only [List.getElem_range]

    have h_len_scan : ((C.val.toLCellAutomaton).scan_temporal w).length = w.length := by
      simp [LCellAutomaton.scan_temporal]

    have h_i_lt_w : i < w.length := by
      rw [← h_len_scan]
      rw [List.length_map] at h1
      exact h1

    let w_pref := w.take (i+1)
    have h_pref_eq : w.take (i+1) = w_pref := rfl
    rw [h_pref_eq]

    have h_pref_len : w_pref.length = i + 1 := by
      show (w.take (i+1)).length = i + 1
      rw [List.length_take]
      rw [min_eq_left]
      omega

    unfold tCellAutomaton.L
    simp
    have h_t : C.val.t (i + 1) = i := by
      have h_rt := C.property.2 (i + 1)
      simp at h_rt
      exact h_rt
    rw [h_pref_len, h_t]

    congr 1

    have h_w : w = w_pref ++ w.drop (i+1) := (List.take_append_drop (i + 1) w).symm

    have h_scan_eq : (C.val.toLCellAutomaton.scan_temporal w).take (i+1) = C.val.toLCellAutomaton.scan_temporal w_pref := by
      nth_rewrite 1 [h_w]
      rw [← h_pref_len]
      apply scan_temporal_independence

    have h_len_scan_pref : ((C.val.toLCellAutomaton).scan_temporal w_pref).length = i + 1 := by
      simp [LCellAutomaton.scan_temporal]
      exact h_pref_len

    have h_idx_valid : i < ((C.val.toLCellAutomaton.scan_temporal w).take (i+1)).length := by
      rw [List.length_take]
      rw [h_len_scan]
      rw [min_eq_left]
      · omega
      · omega

    have h_get : ((C.val.toLCellAutomaton).scan_temporal w)[i] = ((C.val.toLCellAutomaton).scan_temporal w_pref)[i] := by
      trans ((C.val.toLCellAutomaton.scan_temporal w).take (i+1))[i]'h_idx_valid
      · rw [List.getElem_take]
      · simp [h_scan_eq]

    unfold LCellAutomaton.scan_temporal at h_get
    rw [List.getElem_map, List.getElem_map] at h_get
    simp at h_get
    exact h_get

theorem advice_prefixes_in_L_is_two_stage_advice (C: CA_rt α):
    (Advice.prefixes_in_L C.val.L).is_two_stage_advice := by
  use CA_rt_to_TwoStage C
  have h_eq := CA_rt_to_TwoStage_eq C
  match (CA_rt_to_TwoStage C).advice, (Advice.prefixes_in_L C.val.L), h_eq with
  | ⟨f1, l1⟩, ⟨f2, l2⟩, h =>
    simp at h
    subst h
    rfl
