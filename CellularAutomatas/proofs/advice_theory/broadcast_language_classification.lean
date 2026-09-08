import CellularAutomatas.proofs.advice_theory.two_stage_not_finite_future_index

/-!
# Classification of whole-word Boolean broadcasts

Broadcasting membership in a language to every input position has at most two
possible advice prefixes. It is two-stage exactly when the language is RT,
and exactly when the advice is weakly or uniformly RT-closed.
-/

namespace CellularAutomatas

open Classical

variable {α : Type} [Alphabet α]

/-- Broadcast one Boolean property of the complete word to every position. -/
noncomputable def Advice.broadcastLanguage (L : Language α) : Advice α Bool where
  f w := List.replicate w.length (decide (w ∈ L))
  len := by intro w; simp

omit [Alphabet α] in
lemma Advice.broadcastLanguage_last (L : Language α)
    (w : Word α) (hw : w ≠ []) :
    ((Advice.broadcastLanguage L) w).getLast? = some (decide (w ∈ L)) := by
  show (List.replicate w.length (decide (w ∈ L))).getLast? = _
  rw [List.getLast?_eq_getLast_of_ne_nil (by simpa using hw), List.getLast_eq_getElem]
  simp

omit [Alphabet α] in
/-- A whole-word broadcast still has only two possible prefixes, regardless of its oracle. -/
theorem Advice.broadcastLanguage_finite_future_variation
    (L : Language α) :
    (Advice.broadcastLanguage L).finite_future_variation := by
  classical
  refine ⟨2, fun p => ?_⟩
  have hsub : Set.univ.image (fun s : Word α => rel_repr (Advice.broadcastLanguage L) p s)
      ⊆ ({List.replicate p.length false, List.replicate p.length true} : Set (Word Bool)) := by
    rintro v ⟨s, _, rfl⟩
    show rel_repr (Advice.broadcastLanguage L) p s ∈ _
    by_cases h : p ++ s ∈ L <;> simp [rel_repr, Advice.broadcastLanguage, h]
  calc
    (Set.univ.image (fun s : Word α => rel_repr (Advice.broadcastLanguage L) p s)).encard
        ≤ ({List.replicate p.length false, List.replicate p.length true} :
            Set (Word Bool)).encard := Set.encard_mono hsub
    _ ≤ 2 := by
      calc
        ({List.replicate p.length false, List.replicate p.length true} :
            Set (Word Bool)).encard
            ≤ ({List.replicate p.length true} : Set (Word Bool)).encard + 1 :=
              Set.encard_insert_le _ _
        _ = 2 := by rw [Set.encard_singleton]; rfl

/-- Closure forces the broadcast bit to be an ordinary RT decision.
The empty word is handled separately because it has no advice symbol. -/
theorem Advice.broadcastLanguage_language_rt_of_weak_rt_closed
    (L : Language α)
    (hclosed : (Advice.broadcastLanguage L).weak_rt_closed) :
    L ∈ ℒ (CA_rt α) := by
  rw [ℒ_CA_rt_iff]
  refine ⟨fix_empty (decide ([] ∈ L)) (CA_L_c (Advice.broadcastLanguage L) hclosed true), ?_⟩
  ext w
  rw [fix_empty_spec]
  by_cases hw : w = []
  · simp [hw]
  · simp only [beq_iff_eq, hw, ↓reduceIte, decide_eq_true_eq,
      CA_L_c_spec]
    show ((Advice.broadcastLanguage L) w).getLast? = some true ↔ w ∈ L
    rw [Advice.broadcastLanguage_last L w hw]
    simp

/-- An RT language supplies the first-stage prefix answers; a reverse FST broadcasts
the final one. -/
noncomputable def Advice.broadcastLanguage_two_stage_of_language_rt
    (L : Language α) (hL : L ∈ ℒ (CA_rt α)) :
    (Advice.broadcastLanguage L).is_two_stage_advice := by
  let C := (ℒ_CA_rt_iff.mp hL).choose
  have hC : C.L = L := (ℒ_CA_rt_iff.mp hL).choose_spec
  refine ⟨RtMask.decision C, ?_⟩
  apply advice_eq_iff
  funext w
  by_cases hw : w = []
  · show (RtMask.decision C).advice w = Advice.broadcastLanguage L w
    subst w
    simp [Advice.broadcastLanguage]
  · show (RtMask.decision C).advice w = Advice.broadcastLanguage L w
    have hbit : C.accepts w = decide (w ∈ L) := by
      apply Bool.eq_iff_iff.mpr
      simpa [hC] using (show C.accepts w = true ↔ w ∈ C.L from Iff.rfl)
    calc
      (RtMask.decision C).advice w = List.replicate w.length (C.accepts w) :=
        RtMask.decision_spec C w hw
      _ = Advice.broadcastLanguage L w := by rw [hbit]; rfl

theorem Advice.broadcastLanguage_two_stage_iff
    (L : Language α) :
    Nonempty (Advice.broadcastLanguage L).is_two_stage_advice ↔ L ∈ ℒ (CA_rt α) :=
  ⟨fun ⟨h⟩ => Advice.broadcastLanguage_language_rt_of_weak_rt_closed L h.weak_rt_closed,
    fun h => ⟨Advice.broadcastLanguage_two_stage_of_language_rt L h⟩⟩

theorem Advice.broadcastLanguage_weak_rt_closed_iff
    (L : Language α) :
    Nonempty (Advice.broadcastLanguage L).weak_rt_closed ↔ L ∈ ℒ (CA_rt α) :=
  ⟨fun ⟨h⟩ => Advice.broadcastLanguage_language_rt_of_weak_rt_closed L h,
    fun h => ⟨(Advice.broadcastLanguage_two_stage_of_language_rt L h).weak_rt_closed⟩⟩

theorem Advice.broadcastLanguage_rt_closed_iff
    (L : Language α) :
    Nonempty (Advice.broadcastLanguage L).rt_closed ↔ L ∈ ℒ (CA_rt α) :=
  ⟨fun ⟨h⟩ => Advice.broadcastLanguage_language_rt_of_weak_rt_closed L
      (Advice.rt_closed_implies_weak_rt_closed h),
    fun h => ⟨(Advice.broadcastLanguage_two_stage_of_language_rt L h).rt_closed⟩⟩

end CellularAutomatas
