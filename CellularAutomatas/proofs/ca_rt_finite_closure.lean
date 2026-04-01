/-
  # Finite Language Recognition and Closure Properties for CA_rt

  This file proves that:
  1. Finite languages are recognizable by CA_rt
  2. ℒ(CA_rt α) is closed under finite symmetric difference
-/

import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.cart_fix_empty_word

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
  obtain ⟨C₁, hC₁_rt, hC₁_L⟩ := h₁
  obtain ⟨C₂, hC₂_rt, hC₂_L⟩ := h₂
  let C' := toRtCa ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a || b))
  refine ⟨C'.val, C'.property, ?_⟩
  ext w
  rw [Set.mem_union, ← hC₁_L, ← hC₂_L]
  -- Show: w ∈ C'.val.L ↔ w ∈ C₁.L ∨ w ∈ C₂.L
  rw [CA_rt_L_iff (C := C'), CA_rt_L_iff2 hC₁_rt, CA_rt_L_iff2 hC₂_rt]
  -- Goal: (↑C').comp ⦋w⦌ ... = true ↔ C₁.comp ... = true ∨ C₂.comp ... = true
  -- C'.val.toCellAutomaton = (C₁ ⨂ C₂).map_project (λ (a,b) => a || b)
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
  obtain ⟨C₁, hC₁_rt, hC₁_L⟩ := h₁
  obtain ⟨C₂, hC₂_rt, hC₂_L⟩ := h₂
  let C' := toRtCa ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && !b))
  refine ⟨C'.val, C'.property, ?_⟩
  ext w
  rw [Set.mem_diff, ← hC₁_L, ← hC₂_L]
  -- Show: w ∈ C'.val.L ↔ w ∈ C₁.L ∧ w ∉ C₂.L
  rw [CA_rt_L_iff (C := C'), CA_rt_L_iff2 hC₁_rt, CA_rt_L_iff2 hC₂_rt]
  -- Goal: (↑C').comp ... = true ↔ C₁.comp ... = true ∧ ¬(C₂.comp ... = true)
  change ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && !b)).comp ⦋w⦌ (w.length - 1) 0 = true
    ↔ C₁.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true ∧ ¬(C₂.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true)
  simp only [comp_of_map_project, ca_zip_comp, Bool.and_eq_true, Bool.not_eq_true']
  -- Goal: _ = true ∧ _ = false ↔ _ = true ∧ ¬(_ = true)
  simp only [Bool.eq_false_iff]

/-! ## Finite Language Recognition -/

/-- The empty language is recognized by a constant-false CA.  -/
private theorem empty_language_in_ca_rt {α : Type} [Alphabet α] :
    (∅ : Set (Word α)) ∈ ℒ (CA_rt α) := by
  rw [ℒ_CA_rt_iff]
  let C : CellAutomaton α？ Bool := {
    Q := Unit
    δ := fun _ _ _ => ()
    embed := fun _ => ()
    project := fun _ => false
  }
  refine ⟨(toRtCa C).val, (toRtCa C).property, ?_⟩
  ext w
  rw [Set.mem_empty_iff_false, iff_false]
  intro hw
  -- `hw : w ∈ (toRtCa C).val.L` means `(toRtCa C).val.accepts w = true`
  -- which unfolds to `C.comp ... = true`, but C.project always returns false
  have h := (CA_rt_L_iff (C := toRtCa C)).mp hw
  -- h : (toRtCa C).val.comp ⦋w⦌ (w.length - 1) 0 = true
  -- In this CA: comp c t i = project (nextt c t i) = false
  -- So h is: false = true, which is a contradiction
  rw [CellAutomaton.comp, Function.comp_apply, CellAutomaton.project_config] at h
  -- h now has: (↑(toRtCa C)).project ... = true
  -- But (↑(toRtCa C)).project = C.project = fun _ => false
  -- So h is: false = true
  exact Bool.noConfusion h

/-- A singleton language {w} is recognized by CA_rt.

    Construction: Use fix_empty to handle the case w = [], otherwise
    the empty language CA suffices since we combine via union.

    TODO: This requires constructing a CA that compares input position-by-position
    with a fixed word w. The state tracks (match_status, distance_from_border).
    Key insight: cells at distance i from the border compare input[|input|-1-i] with w[|w|-1-i].
    If |input| ≠ |w| or any mismatch, reject. -/
private theorem singleton_in_ca_rt {α : Type} [Alphabet α]
    (w : Word α) : ({w} : Set (Word α)) ∈ ℒ (CA_rt α) := by
  sorry

/-- Any finite language is in ℒ(CA_rt α).

    Proved by finite induction: ∅ is in ℒ(CA_rt α), and if F is in ℒ(CA_rt α),
    then F ∪ {w} is also in ℒ(CA_rt α) (by binary union). -/
theorem finite_language_in_ca_rt {α : Type} [Alphabet α]
    (F : Set (Word α)) (hF : F.Finite) :
    F ∈ ℒ (CA_rt α) := by
  refine Set.Finite.induction_on (motive := fun S _ => S ∈ ℒ (CA_rt α)) F hF ?_ ?_
  · exact empty_language_in_ca_rt
  · intro w S _ _ hS_ca
    rw [Set.insert_eq]
    exact ca_rt_union_two {w} S (singleton_in_ca_rt w) hS_ca

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
