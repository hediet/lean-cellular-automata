import CellularAutomatas.proofs.constructions.speedup_right_border_oca
import CellularAutomatas.proofs.language.ca_rt_rev_eq_car_rt
import CellularAutomatas.proofs.language.oca_2n_diagonal_equivalences

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [Alphabet α]

omit [Alphabet α] in
private lemma flip_right_independent {C : CellAutomaton α Bool}
    (h : C.left_independent) : C.flip.right_independent := by
  intro left center right right'
  exact h right center left right'

omit [Alphabet α] in
private lemma flip_left_independent {C : CellAutomaton α Bool}
    (h : C.right_independent) : C.flip.left_independent := by
  intro left center right left'
  exact h right center left left'

private def ltLeftToRight {c : ℕ}
    (C : tCellAutomaton (.lt_left c) α) :
    tCellAutomaton (.lt_right c) α where
  toCellAutomaton := C.toCellAutomaton.flip

private def ltRightToLeft {c : ℕ}
    (C : tCellAutomaton (.lt_right c) α) :
    tCellAutomaton (.lt_left c) α where
  toCellAutomaton := C.toCellAutomaton.flip

omit [Alphabet α] in
private lemma ltLeftToRight_accepts_iff {c : ℕ}
    (C : tCellAutomaton (.lt_left c) α) (w : Word α) :
    (ltLeftToRight C).accepts w = C.accepts w.reverse := by
  simp only [tCellAutomaton.accepts, ltLeftToRight,
    AcceptanceSchema.lt_right, AcceptanceSchema.lt_left,
    List.length_reverse]
  rw [CellAutomaton.flip_comp, CellAutomaton.flip_embed_config']
  simp only [CellAutomaton.comp, Function.comp_apply,
    CellAutomaton.project_config]
  congr 1
  conv_lhs =>
    rw [show -((w.length : ℤ) - 1) = 0 + (1 - w.length) by ring]
  rw [nextt_shift]
  congr 1
  funext position
  simp only [CellAutomaton.embed_config]
  exact congrArg C.toCellAutomaton.embed
    (congrFun (word_to_config_flip_shift w) position)

omit [Alphabet α] in
private lemma ltRightToLeft_accepts_iff {c : ℕ}
    (C : tCellAutomaton (.lt_right c) α) (w : Word α) :
    (ltRightToLeft C).accepts w = C.accepts w.reverse := by
  have h := ltLeftToRight_accepts_iff (ltRightToLeft C) w.reverse
  simp only [List.reverse_reverse] at h
  have h_roundtrip :
      (ltLeftToRight (ltRightToLeft C)).accepts w.reverse =
        C.accepts w.reverse := by
    simp only [tCellAutomaton.accepts, ltLeftToRight, ltRightToLeft,
      AcceptanceSchema.lt_right, AcceptanceSchema.lt_left,
      CellAutomaton.flip, List.length_reverse]
  rw [h_roundtrip] at h
  exact h.symm

private def ocaLtToOcarLt (C : OCA_lt α) : OCAr_lt α :=
  ⟨C.1, ⟨ltLeftToRight C.2.1,
    flip_right_independent C.2.2⟩⟩

private def ocarLtToOcaLt (C : OCAr_lt α) : OCA_lt α :=
  ⟨C.1, ⟨ltRightToLeft C.2.1,
    flip_left_independent C.2.2⟩⟩

/-- Reversing the languages of left-reading linear-time OCAs gives exactly
    the languages of right-reading linear-time right-independent CAs. -/
theorem oca_lt_rev_eq_ocar_lt :
    ℒ_rev (OCA_lt α) = ℒ (OCAr_lt α) := by
  ext L
  simp only [ℒ_rev, LanguageClass.rev, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨C, rfl⟩, rfl⟩
    refine ⟨ocaLtToOcarLt C, ?_⟩
    ext w
    show C.2.1.accepts w.reverse = true ↔
      (ltLeftToRight C.2.1).accepts w = true
    rw [ltLeftToRight_accepts_iff]
  · rintro ⟨C, rfl⟩
    refine ⟨Language.rev C.2.1.L, ⟨ocarLtToOcaLt C, ?_⟩,
      Language.rev_rev C.2.1.L⟩
    ext w
    show C.2.1.accepts w.reverse = true ↔
      (ltRightToLeft C.2.1).accepts w = true
    rw [ltRightToLeft_accepts_iff]

/-- Reversed `2(n-1)`-time OCA languages are exactly real-time CA
    languages. -/
theorem ca_rt_eq_rev_oca_2n :
    ℒ (CA_rt α) = ℒ_rev (OCA_2n α) := by
  calc
    ℒ (CA_rt α) = LanguageClass.rev (ℒ (CAr_rt α)) := by
      rw [← ca_rt_rev_eq_car_rt]
      simp [ℒ_rev]
    _ = ℒ_rev (OCA_2n α) := by
      simp only [ℒ_rev]
      rw [oca_2n_eq_car_rt]

/-- With right-reading linear-time schemas, right-independent linear-time CAs
    recognize exactly the real-time CA languages. -/
theorem ocar_lt_eq_ca_rt : ℒ (OCAr_lt α) = ℒ (CA_rt α) := by
  have h_speedup_rev : ℒ_rev (OCA_2n α) = ℒ_rev (OCA_lt α) := by
    simpa only [ℒ_rev] using
      congrArg LanguageClass.rev (OCA_2n_eq_OCA_lt α)
  calc
    ℒ (OCAr_lt α) = ℒ_rev (OCA_lt α) := oca_lt_rev_eq_ocar_lt.symm
    _ = ℒ_rev (OCA_2n α) := h_speedup_rev.symm
    _ = ℒ (CA_rt α) := ca_rt_eq_rev_oca_2n.symm

/-- Real-time CA languages coincide with reversed linear-time and `2n`-time
  OCA languages, and with `2n`-time OCA languages observed at `-(n-1)`. -/
theorem ca_rt_eq_rev_oca :
    ℒ (CA_rt α) = ℒ_rev (OCA_2n α) ∧
    ℒ_rev (OCA_2n α) = ℒ_rev (OCA_lt α) ∧
  ℒ_rev (OCA_lt α) = ℒ (OCA_2n_left_neg_np1 α) := by
  have h_speedup_rev : ℒ_rev (OCA_2n α) = ℒ_rev (OCA_lt α) := by
    simpa only [ℒ_rev] using
      congrArg LanguageClass.rev (OCA_2n_eq_OCA_lt α)
  refine ⟨ca_rt_eq_rev_oca_2n, h_speedup_rev, ?_⟩
  calc
    ℒ_rev (OCA_lt α) = ℒ_rev (OCA_2n α) := h_speedup_rev.symm
    _ = ℒ (CA_rt α) := ca_rt_eq_rev_oca_2n.symm
    _ = ℒ (OCA_2n_left_neg_np1 α) := oca_2n_left_neg_np1_eq_ca_rt.symm

end CellularAutomatas
