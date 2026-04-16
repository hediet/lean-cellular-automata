/-
  # Finite Language Recognition and Closure Properties for CA_rt

  This file proves that:
  1. Finite languages are recognizable by CA_rt
  2. ℒ(CA_rt α) is closed under finite symmetric difference
-/

import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.cart_fix_empty_word
import CellularAutomatas.proofs.dfa_to_left_indep_ca
import CellularAutomatas.proofs.finite_language_regular

namespace CellularAutomatas

open CellAutomaton

/-! ## Helper: Binary Union and Difference for CA_rt -/

/-- Binary union of two CA_rt languages, via product construction.
    Runs both CAs in parallel and outputs true iff either accepts. -/
private theorem ca_rt_union_two {α : Type} [Alphabet α]
    (L₁ L₂ : Language α)
    (h₁ : L₁ ∈ ℒ (CA_rt α)) (h₂ : L₂ ∈ ℒ (CA_rt α)) :
    (L₁ ∪ L₂ : Set (Word α)) ∈ ℒ (CA_rt α) := by
  rw [ℒ_CA_rt_iff] at h₁ h₂ ⊢
  obtain ⟨C₁, hC₁_L⟩ := h₁
  obtain ⟨C₂, hC₂_L⟩ := h₂
  let C' := toRtCa ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a || b))
  refine ⟨C', ?_⟩
  ext w
  rw [Set.mem_union, ← hC₁_L, ← hC₂_L]
  -- Show: w ∈ C'.L ↔ w ∈ C₁.L ∨ w ∈ C₂.L
  rw [CA_rt_L_iff (C := C'), CA_rt_L_iff (C := C₁), CA_rt_L_iff (C := C₂)]
  -- Goal: (C').comp ⦋w⦌ ... = true ↔ C₁.comp ... = true ∨ C₂.comp ... = true
  change ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a || b)).comp ⦋w⦌ (w.length - 1) 0 = true
    ↔ C₁.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true ∨ C₂.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true
  simp [comp_of_map_project, ca_zip_comp, Bool.or_eq_true]

/-- Binary set difference of a CA_rt language with another CA_rt language.
    Runs both CAs in parallel and outputs true iff first accepts and second rejects. -/
private theorem ca_rt_diff_two {α : Type} [Alphabet α]
    (L₁ L₂ : Language α)
    (h₁ : L₁ ∈ ℒ (CA_rt α)) (h₂ : L₂ ∈ ℒ (CA_rt α)) :
    L₁ \ L₂ ∈ ℒ (CA_rt α) := by
  rw [ℒ_CA_rt_iff] at h₁ h₂ ⊢
  obtain ⟨C₁, hC₁_L⟩ := h₁
  obtain ⟨C₂, hC₂_L⟩ := h₂
  let C' := toRtCa ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && !b))
  refine ⟨C', ?_⟩
  ext w
  rw [Set.mem_diff, ← hC₁_L, ← hC₂_L]
  -- Show: w ∈ C'.L ↔ w ∈ C₁.L ∧ w ∉ C₂.L
  rw [CA_rt_L_iff (C := C'), CA_rt_L_iff (C := C₁), CA_rt_L_iff (C := C₂)]
  -- Goal: C'.comp ... = true ↔ C₁.comp ... = true ∧ ¬(C₂.comp ... = true)
  change ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && !b)).comp ⦋w⦌ (w.length - 1) 0 = true
    ↔ C₁.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true ∧ ¬(C₂.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true)
  simp only [comp_of_map_project, ca_zip_comp, Bool.and_eq_true, Bool.not_eq_true']
  -- Goal: _ = true ∧ _ = false ↔ _ = true ∧ ¬(_ = true)
  simp only [Bool.eq_false_iff]

/-! ## Finite Language Recognition -/

/-- ℒ(OCA_rt α) ⊆ ℒ(CA_rt α): every OCA_rt language is a CA_rt language. -/
private theorem ℒ_OCA_rt_sub_CA_rt {α : Type} [Alphabet α] :
    ℒ (OCA_rt α) ⊆ ℒ (CA_rt α) := by
  intro L ⟨C, hL⟩
  exact ⟨C.1, hL⟩

/-- Any finite language is in ℒ(CA_rt α).

    Proof: finite → regular (DFA) → ℒ(OCA_rt α) → ℒ(CA_rt α). -/
theorem finite_language_in_ca_rt {α : Type} [Alphabet α]
    (F : Set (Word α)) (hF : F.Finite) :
    F ∈ ℒ (CA_rt α) := by
  -- Step 1: F is regular, so there exists a DFA recognizing F
  have hReg := Language.finite_isRegular hF
  obtain ⟨σ, hFin, M, hM⟩ := hReg
  -- Manufacture missing instances from classical logic and M.start
  letI : DecidableEq σ := Classical.typeDecidableEq σ
  haveI : Inhabited σ := ⟨M.start⟩
  haveI : DecidablePred (· ∈ M.accept) := Classical.decPred _
  -- Step 2: DFA language is in ℒ(OCA_rt α)
  have hOCA := dfa_language_in_OCA_rt M
  -- Step 3: ℒ(OCA_rt α) ⊆ ℒ(CA_rt α)
  have hCA := ℒ_OCA_rt_sub_CA_rt hOCA
  -- Step 4: Rewrite M.accepts = F
  rwa [hM] at hCA

/-! ## Closure Under Finite Operations -/

/-- ℒ(CA_rt α) is closed under union with a finite set. -/
theorem ca_rt_closed_union_finite {α : Type} [Alphabet α]
    (L : Language α) (F : Set (Word α))
    (hL : L ∈ ℒ (CA_rt α)) (hF : F.Finite) :
    (L ∪ F : Set (Word α)) ∈ ℒ (CA_rt α) :=
  ca_rt_union_two L F hL (finite_language_in_ca_rt F hF)

/-- ℒ(CA_rt α) is closed under difference with a finite set. -/
theorem ca_rt_closed_diff_finite {α : Type} [Alphabet α]
    (L : Language α) (F : Set (Word α))
    (hL : L ∈ ℒ (CA_rt α)) (hF : F.Finite) :
    L \ F ∈ ℒ (CA_rt α) :=
  ca_rt_diff_two L F hL (finite_language_in_ca_rt F hF)

/-! ## Main Closure Theorem -/

/-- ℒ(CA_rt α) is closed under finite symmetric difference.

    If L₁ ∈ ℒ(CA_rt α) and (L₁ ∆ L₂) is finite, then L₂ ∈ ℒ(CA_rt α).

    Proof: L₂ = (L₁ \ (L₁ \ L₂)) ∪ (L₂ \ L₁)
              = (L₁ \ (L₁ ∆ L₂ ∩ L₁)) ∪ (L₁ ∆ L₂ ∩ L₂)

    Since L₁ ∆ L₂ is finite, both (L₁ ∆ L₂ ∩ L₁) and (L₁ ∆ L₂ ∩ L₂) are finite.
    Apply ca_rt_closed_diff_finite and ca_rt_closed_union_finite. -/
theorem ca_rt_closed_finite_symmDiff {α : Type} [Alphabet α]
    (L₁ L₂ : Language α)
    (h₁ : L₁ ∈ ℒ (CA_rt α))
    (h_finite : (symmDiff L₁ L₂).Finite) :
    L₂ ∈ ℒ (CA_rt α) := by
  -- L₁ \ L₂ ⊆ symmDiff L₁ L₂, so (L₁ \ L₂).Finite
  have h_diff1 : (L₁ \ L₂).Finite := by
    apply h_finite.subset
    intro w hw
    simp only [symmDiff] at hw ⊢
    left; exact hw
  -- L₂ \ L₁ ⊆ symmDiff L₁ L₂, so (L₂ \ L₁).Finite
  have h_diff2 : (L₂ \ L₁).Finite := by
    apply h_finite.subset
    intro w hw
    simp only [symmDiff] at hw ⊢
    right; exact hw
  -- L₁ \ (L₁ \ L₂) ∈ ℒ(CA_rt α)
  have h_step1 : (L₁ \ (L₁ \ L₂) : Set (Word α)) ∈ ℒ (CA_rt α) :=
    ca_rt_closed_diff_finite L₁ (L₁ \ L₂) h₁ h_diff1
  -- L₂ = (L₁ \ (L₁ \ L₂)) ∪ (L₂ \ L₁)  (set identity)
  suffices h : ((L₁ \ (L₁ \ L₂)) ∪ (L₂ \ L₁) : Set (Word α)) ∈ ℒ (CA_rt α) by
    convert h using 1
    ext w
    constructor <;> intro hw
    · by_cases hw1 : w ∈ L₁
      · left; exact ⟨hw1, fun ⟨_, hnw⟩ => hnw hw⟩
      · right; exact ⟨hw, hw1⟩
    · rcases hw with ⟨hw1, hnot⟩ | ⟨hw2, _⟩
      · by_contra hn
        exact hnot ⟨hw1, hn⟩
      · exact hw2
  exact ca_rt_closed_union_finite _ _ h_step1 h_diff2

end CellularAutomatas
