import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.left_indep_from_regular
import CellularAutomatas.proofs.constructions.left_indep_to_regular

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

private def betaHead : BetaUnionSq Bool → Bool
  | .single answer => answer
  | .pair answer _ => answer

private def oca2nToCarRt (C : OCA_2n α) : CAr_rt α where
  toCellAutomaton :=
    (LeftIndepToRegular.mk C.1.toCellAutomaton C.2).C

private lemma oca2nToCarRt_L (C : OCA_2n α) :
    (oca2nToCarRt C).L = C.1.L := by
  ext w
  show (oca2nToCarRt C).accepts w = true ↔ C.1.accepts w = true
  change
    (LeftIndepToRegular.mk C.1.toCellAutomaton C.2).C.comp
        ⦋⟬w⟭⦌ (w.length - 1) ((w.length : ℤ) - 1) = true ↔
      C.1.toCellAutomaton.comp ⦋⟬w⟭⦌ (2 * (w.length - 1)) 0 = true
  rw [LeftIndepToRegular.spec]
  by_cases hw : w.length = 0
  · have hw_nil : w = [] := List.eq_nil_of_length_eq_zero hw
    subst w
    simp [CellAutomaton.comp_apply, CellAutomaton.embed_config_apply,
      word_to_config]
  · have h_position :
        (w.length : ℤ) - 1 - (w.length - 1 : ℕ) = 0 := by
      omega
    rw [h_position]

private def carRtToOca2n (C : CAr_rt α) : OCA_2n α :=
  let converted :=
    (RegularToLeftIndep.mk C.toCellAutomaton).C.map_project betaHead
  ⟨{ toCellAutomaton := converted },
    RegularToLeftIndep.C_left_independent _⟩

private lemma carRtToOca2n_L (C : CAr_rt α) :
    (carRtToOca2n C).1.L = C.L := by
  ext w
  show (carRtToOca2n C).1.accepts w = true ↔ C.accepts w = true
  change
    betaHead ((RegularToLeftIndep.mk C.toCellAutomaton).C.comp
      ⦋⟬w⟭⦌ (2 * (w.length - 1)) 0) = true ↔
      C.toCellAutomaton.comp
        ⦋⟬w⟭⦌ (w.length - 1) ((w.length : ℤ) - 1) = true
  rw [RegularToLeftIndep.spec_even]
  by_cases hw : w.length = 0
  · have hw_nil : w = [] := List.eq_nil_of_length_eq_zero hw
    subst w
    simp [betaHead, CellAutomaton.comp_apply,
      CellAutomaton.embed_config_apply, word_to_config]
  · have h_position : (0 : ℤ) + (w.length - 1 : ℕ) = (w.length : ℤ) - 1 := by
      omega
    rw [h_position]
    rfl

/-- A left-independent CA running for `2(n-1)` steps at cell `0` is exactly
    a general real-time CA read at cell `n-1`. -/
theorem oca_2n_eq_car_rt : ℒ (OCA_2n α) = ℒ (CAr_rt α) := by
  apply Set.Subset.antisymm
  · rintro L ⟨C, hL⟩
    exact ⟨oca2nToCarRt C, hL.trans (oca2nToCarRt_L C).symm⟩
  · rintro L ⟨C, hL⟩
    exact ⟨carRtToOca2n C, hL.trans (carRtToOca2n_L C).symm⟩

private def oca2nLeftNegNp1ToCaRt (C : OCA_2n_left_neg_np1 α) : CA_rt α where
  toCellAutomaton :=
    (LeftIndepToRegular.mk C.1.toCellAutomaton C.2).C

private lemma oca2nLeftNegNp1ToCaRt_L (C : OCA_2n_left_neg_np1 α) :
    (oca2nLeftNegNp1ToCaRt C).L = C.1.L := by
  ext w
  show (oca2nLeftNegNp1ToCaRt C).accepts w = true ↔ C.1.accepts w = true
  change
    (LeftIndepToRegular.mk C.1.toCellAutomaton C.2).C.comp
        ⦋⟬w⟭⦌ (w.length - 1) 0 = true ↔
      C.1.toCellAutomaton.comp ⦋⟬w⟭⦌ (2 * (w.length - 1))
        (-((w.length : ℤ) - 1)) = true
  rw [LeftIndepToRegular.spec]
  by_cases hw : w.length = 0
  · have hw_nil : w = [] := List.eq_nil_of_length_eq_zero hw
    subst w
    simp [CellAutomaton.comp_apply, CellAutomaton.embed_config_apply,
      word_to_config]
  · have h_position : -(w.length - 1 : ℕ) = -((w.length : ℤ) - 1) := by
      omega
    simp only [zero_sub]
    rw [h_position]

private def caRtToOca2nLeftNegNp1 (C : CA_rt α) : OCA_2n_left_neg_np1 α :=
  let converted :=
    (RegularToLeftIndep.mk C.toCellAutomaton).C.map_project betaHead
  ⟨{ toCellAutomaton := converted },
    RegularToLeftIndep.C_left_independent _⟩

private lemma caRtToOca2nLeftNegNp1_L (C : CA_rt α) :
    (caRtToOca2nLeftNegNp1 C).1.L = C.L := by
  ext w
  show (caRtToOca2nLeftNegNp1 C).1.accepts w = true ↔ C.accepts w = true
  change
    betaHead ((RegularToLeftIndep.mk C.toCellAutomaton).C.comp
      ⦋⟬w⟭⦌ (2 * (w.length - 1)) (-((w.length : ℤ) - 1))) = true ↔
      C.toCellAutomaton.comp ⦋⟬w⟭⦌ (w.length - 1) 0 = true
  rw [RegularToLeftIndep.spec_even]
  by_cases hw : w.length = 0
  · have hw_nil : w = [] := List.eq_nil_of_length_eq_zero hw
    subst w
    simp [betaHead, CellAutomaton.comp_apply,
      CellAutomaton.embed_config_apply, word_to_config]
  · have h_position :
        -((w.length : ℤ) - 1) + (w.length - 1 : ℕ) = 0 := by
      omega
    rw [h_position]
    rfl

/-- A left-independent CA running for `2(n-1)` steps at cell `-(n-1)` is
    exactly a left-reading real-time CA at cell `0`. -/
theorem oca_2n_left_neg_np1_eq_ca_rt :
  ℒ (OCA_2n_left_neg_np1 α) = ℒ (CA_rt α) := by
  apply Set.Subset.antisymm
  · rintro L ⟨C, hL⟩
    exact ⟨oca2nLeftNegNp1ToCaRt C,
      hL.trans (oca2nLeftNegNp1ToCaRt_L C).symm⟩
  · rintro L ⟨C, hL⟩
    exact ⟨caRtToOca2nLeftNegNp1 C,
      hL.trans (caRtToOca2nLeftNegNp1_L C).symm⟩

end CellularAutomatas
