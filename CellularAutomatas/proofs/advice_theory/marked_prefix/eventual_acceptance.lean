import CellularAutomatas.proofs.ca_rt_finite_closure
import CellularAutomatas.proofs.ca_rt_utils

namespace CellularAutomatas.MarkedPrefix

variable {α Γ Δ : Type} [Alphabet α] [Alphabet Γ] [Alphabet Δ]

theorem finite_short_words (cutoff : ℕ) :
    {w : Word α | w.length < cutoff}.Finite := by
  classical
  let shortWords : Finset (Word α) :=
    (Finset.range cutoff).biUnion
      (fun n => (Finset.univ : Finset (Fin n → α)).image List.ofFn)
  apply shortWords.finite_toSet.subset
  intro w hw
  show w ∈ shortWords
  simp only [shortWords, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨w.length, hw, fun i => w[i], List.ofFn_getElem w⟩

/-- Correctness on all sufficiently long inputs suffices: the existing finite
symmetric-difference construction repairs the remaining inputs. -/
theorem ca_rt_of_eventual_agreement (C : CA_rt α) (L : Language α)
    (cutoff : ℕ)
    (hagrees : ∀ w, cutoff ≤ w.length → (w ∈ C.L ↔ w ∈ L)) :
    L ∈ ℒ (CA_rt α) := by
  apply ca_rt_closed_finite_symmDiff C.L L ⟨C, rfl⟩
  apply (finite_short_words (α := α) cutoff).subset
  intro w hw
  show w.length < cutoff
  by_contra hnot
  have heq := hagrees w (by omega)
  rcases hw with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
  · show False
    exact hright (heq.mp hleft)
  · show False
    exact hleft (heq.mpr hright)

/-- This interface deliberately asks only for final acceptance agreement,
not equality of the entire advised trace. -/
noncomputable def weakRtClosed_of_eventual_simulators
    (adv : Advice α Γ) (cutoff : ℕ)
    (simulate : CA_rt (α × Γ) → CA_rt α)
    (hsimulate : ∀ C w, cutoff ≤ w.length →
      ((simulate C).accepts w ↔ C.accepts (adv.annotate w))) :
    adv.weak_rt_closed :=
  .of_language_eq <| by
    rw [CArtWithAdvice_eq_CArt_iff]
    intro L hL
    rw [ℒ_oca_def] at hL
    obtain ⟨C, rfl⟩ := hL
    apply ca_rt_of_eventual_agreement (simulate C) _ cutoff
    intro w hw
    exact hsimulate C w hw

noncomputable def weakRtClosed_of_eventual_marked_simulators
    (adv : Advice α Γ) (marker : Advice α Δ)
    (hmarker : marker.weak_rt_closed) (cutoff : ℕ)
    (simulate : CA_rt (α × Γ) → CA_rt (α × Δ))
    (hsimulate : ∀ C w, cutoff ≤ w.length →
      ((simulate C).accepts (marker.annotate w) ↔
        C.accepts (adv.annotate w))) :
    adv.weak_rt_closed := by
  apply weakRtClosed_of_eventual_simulators adv cutoff
    (fun C => hmarker.map (simulate C))
  intro C w hw
  show w ∈ (hmarker.map (simulate C)).L ↔ C.accepts (adv.annotate w)
  rw [hmarker.spec, Set.mem_setOf_eq]
  exact hsimulate C w hw

/-- The lifted input alphabet is retained throughout the simulator contract;
this proves strong RT closure once those simulators have been constructed. -/
noncomputable def rtClosed_of_eventual_marked_simulators
    (adv : Advice α Γ) (marker : Advice α Δ)
    (hmarker : marker.rt_closed) (cutoff : ℕ)
    (simulate : ∀ β [Alphabet β], (β → α) →
      CA_rt (β × Γ) → CA_rt (β × Δ))
    (hsimulate : ∀ β [Alphabet β] (π : β → α) C w,
      cutoff ≤ w.length →
      ((simulate β π C).accepts ((marker.lift π).annotate w) ↔
        C.accepts ((adv.lift π).annotate w))) :
    adv.rt_closed := by
  intro β _ π
  show (adv.lift π).weak_rt_closed
  exact weakRtClosed_of_eventual_marked_simulators
    (adv.lift π) (marker.lift π) (hmarker β π) cutoff
    (simulate β π) (hsimulate β π)

end CellularAutomatas.MarkedPrefix
