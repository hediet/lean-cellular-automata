import CellularAutomatas.defs
import CellularAutomatas.proofs.scan_lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Range

open TwoStageAdvice
open Classical
open scan_lemmas

variable {α: Type u} [Alphabet α]
variable {Γ: Type v} [Alphabet Γ]

-- We define rel_repr for generic Γ, but we will use it for Bool later.
def rel_repr (adv: Advice α Γ) (p s: Word α) := (adv.f (p ++ s)).take p.length

def rel (adv: Advice α Γ) (p s1 s2: Word α) :=
  rel_repr adv p s1 = rel_repr adv p s2

def Advice.finite_lookahead (adv: Advice α Γ) :=
  ∃ N: ℕ, ∀ p: Word α, (Set.univ.image (fun s: Word α => rel_repr adv p s)).encard ≤ N

namespace middle_not_two_stage


lemma two_stage_rel_repr_eq (adv: TwoStageAdvice α Γ) (p s: Word α):
    rel_repr adv.advice p s =
        (adv.M.scanr_q
            (adv.C.scan_temporal p)
            (adv.M.scanr_reduce
                ((adv.C.scan_temporal (p ++ s)).drop p.length)
            )
        ).map adv.t
          := by
    dsimp [rel_repr, TwoStageAdvice.advice]
    rw [← List.map_take]
    congr 1
    let W := adv.C.scan_temporal (p ++ s)
    change (adv.M.scanr W).take p.length = _
    have h_split : W = W.take p.length ++ W.drop p.length := (List.take_append_drop p.length W).symm
    conv in (adv.M.scanr W) => rw [h_split]
    have h_indep : W.take p.length = adv.C.scan_temporal p := by
      simp [W]
      change (adv.C.scan_temporal (p ++ s)).take p.length = _
      erw [scan_temporal_independence (p := p) (s := s)]
    rw [h_indep]
    have h_len_p : (adv.C.scan_temporal p).length = p.length := by
      rw [LCellAutomaton.scan_temporal]
      simp only [List.length_map, List.length_range]
    conv => lhs; arg 1; rw [← h_len_p]
    erw [@scanr_append_take _ _ adv.M (adv.C.scan_temporal p) (W.drop p.length)]

def possible_advice_prefixes (adv: TwoStageAdvice α Γ) (p: Word α) : Finset (List Γ) :=
  Finset.univ.image (fun q : adv.M.Q => (adv.M.scanr_q (adv.C.scan_temporal p) q).map adv.t)

-- 1. The Bottleneck Lemma
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

-- Helper lemmas for markers
def marker_list (n pos : ℕ) : List Bool :=
  (List.range n).map (fun i => i + 1 == pos)

lemma marker_list_len (n pos : ℕ) : (marker_list n pos).length = n := by
  simp [marker_list]

lemma marker_list_inj {n k1 k2 : ℕ} (h1 : k1 ≤ n) (h_pos1 : k1 > 0) :
  marker_list n k1 = marker_list n k2 → k1 = k2 := by
  intro h
  have h_get1 : (marker_list n k1)[k1 - 1]'(by simp [marker_list_len]; omega) = true := by
    simp [marker_list, List.getElem_map, List.getElem_range]
    have : k1 - 1 + 1 = k1 := by omega
    rw [this]

  have h_get2 : (marker_list n k2)[k1 - 1]'(by simp [marker_list_len]; omega) = (k1 == k2) := by
    simp [marker_list, List.getElem_map, List.getElem_range]
    have : k1 - 1 + 1 = k1 := by omega
    rw [this]

  have h_eq_elems : (marker_list n k1)[k1 - 1]'(by simp [marker_list_len]; omega) = (marker_list n k2)[k1 - 1]'(by simp [marker_list_len]; omega) := by
    simp [h]

  rw [h_get1, h_get2] at h_eq_elems
  simp at h_eq_elems
  exact h_eq_elems

lemma marker_list_take {n m k : ℕ} (h_le : m ≤ n) :
  (marker_list n k).take m = marker_list m k := by
  unfold marker_list
  rw [← List.map_take]
  rw [List.take_range]
  rw [min_eq_left h_le]

lemma from_len_marker_eq_marker_list {α} (f : ℕ → Option ℕ) (w : Word α) (k : ℕ) (h : f w.length = some k) :
  (Advice.from_len_marker f).f w = marker_list w.length k := by
  dsimp [Advice.from_len_marker]
  simp [h, marker_list]

-- 2. The Marker Counting Lemma
noncomputable def reachable_markers (f : ℕ → Option ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun pos =>
    pos > 0 ∧ ∃ n ≥ k, f n = some pos
  )

lemma distinct_prefixes_from_markers (f : ℕ → Option ℕ) (p : Word α) :
  ∃ S : Finset (List Bool),
    (S : Set (List Bool)) ⊆ { l | ∃ s, l = rel_repr (Advice.from_len_marker f) p s } ∧
    S.card = (reachable_markers f p.length).card := by
  let k := p.length
  let S := (reachable_markers f k).image (fun pos => marker_list k pos)
  use S
  constructor
  · intro l hl
    simp [S] at hl
    rcases hl with ⟨pos, h_pos, rfl⟩
    unfold reachable_markers at h_pos
    simp at h_pos
    rcases h_pos with ⟨h_range, h_pos_gt0, n, h_n_ge_k, h_fn⟩
    -- Construct suffix s
    let s_len := n - k
    let s : Word α := List.replicate s_len (default : α)
    use s
    dsimp [rel_repr]
    have h_len : (p ++ s).length = n := by
      simp [s, s_len]
      omega
    rw [from_len_marker_eq_marker_list f (p ++ s) pos]
    · rw [marker_list_take]
      · omega
    · rw [h_len]; exact h_fn
  · rw [Finset.card_image_of_injOn]
    unfold Set.InjOn
    intro pos1 h1 pos2 h2 h_eq
    unfold reachable_markers at h1 h2
    simp at h1 h2
    rcases h1 with ⟨h1_le, h1_pos, _⟩
    rcases h2 with ⟨h2_le, h2_pos, _⟩
    apply marker_list_inj
    · exact Nat.le_of_lt_succ h1_le
    · omega
    · exact h_eq

-- 3. The Middle Range Property
lemma middle_reachable_card (k : ℕ) :
  (reachable_markers (some ∘ middle_idx) (2 * k)).card ≥ k := by
  let target_set := Finset.Icc k (2 * k)
  cases k with
  | zero => simp
  | succ k' =>
    let subset_markers := (Finset.Icc (k' + 1) (2 * (k' + 1)))
    have h_subset : subset_markers ⊆ reachable_markers (some ∘ middle_idx) (2 * (k' + 1)) := by
      intro pos h_pos
      unfold reachable_markers
      simp
      rw [Finset.mem_Icc] at h_pos
      refine ⟨by omega, by omega, ?_⟩
      use 2 * pos
      constructor
      · omega
      · dsimp [middle_idx]; simp

    apply le_trans _ (Finset.card_le_card h_subset)
    rw [Nat.card_Icc]
    omega

-- 4. Conclusion
theorem middle_not_two_stage_advice : ¬ Advice.is_two_stage_advice (Advice.middle α) := by
  intro h
  rcases h with ⟨adv, h_eq⟩
  let Q := adv.M.Q
  let K := Fintype.card Q + 1
  let p_len := 2 * K
  let p : Word α := List.replicate p_len (default : α)

  -- From Lemma 2
  rcases distinct_prefixes_from_markers (some ∘ middle_idx) p with ⟨S, h_S_subset, h_S_card⟩

  -- From Lemma 3
  have h_markers_count : (reachable_markers (some ∘ middle_idx) p_len).card ≥ K := by
    have h_len : p.length = p_len := by simp [p]
    rw [h_len] at h_S_card
    -- The goal is about p_len, which is 2*K
    apply middle_reachable_card K

  -- From Lemma 1 (Bottleneck)
  have h_bottleneck : S.card ≤ Fintype.card Q := by
    -- S is a subset of generated prefixes
    -- generated prefixes are subset of possible_advice_prefixes
    have h_gen_sub : { l | ∃ s, l = rel_repr (Advice.middle α) p s } ⊆ possible_advice_prefixes adv p := by
      intro l hl
      rcases hl with ⟨s, rfl⟩
      rw [h_eq]
      apply two_stage_advice_in_possible

    have h_S_sub_possible : S ⊆ possible_advice_prefixes adv p := by
      apply Set.Subset.trans h_S_subset h_gen_sub

    apply le_trans (Finset.card_le_card h_S_sub_possible) (two_stage_restriction_cardinality adv p)

  -- Contradiction
  have h_len : p.length = p_len := by simp [p]
  rw [h_len] at h_S_card
  rw [h_S_card] at h_bottleneck
  have : K ≤ Fintype.card Q := le_trans h_markers_count h_bottleneck
  dsimp [K] at this
  omega
end middle_not_two_stage
