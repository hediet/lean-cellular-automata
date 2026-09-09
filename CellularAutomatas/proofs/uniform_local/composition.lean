import CellularAutomatas.proofs.uniform_local.correctness

namespace CellularAutomatas.Advice

open CellAutomaton

variable {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]

/-- Preserve the original input while eliminating the second advice, then
eliminate the first. The final relabeling only discards the intermediate track. -/
theorem IsUniformlyLocallySimulatable.comp {A : Advice α β} {B : Advice β γ}
    (hA : A.IsUniformlyLocallySimulatable) (hB : B.IsUniformlyLocallySimulatable) :
    (A.compose B).IsUniformlyLocallySimulatable := by
  intro σ _ π output _
  obtain ⟨first, hfirst⟩ := hA σ π output
  obtain ⟨second, hsecond⟩ := hB (σ × β) Prod.snd output
  let discard : (σ × β) × γ → σ × γ := fun pair => (pair.1.1, pair.2)
  let relabel := UniformLocal.relabel output (Option.map discard)
  refine ⟨first.compose (second.compose relabel), ?_⟩
  intro target w _ hne
  let prepared := (A.lift π).retainInput w
  have hprepared : prepared ≠ [] := by
    apply List.ne_nil_of_length_pos
    simpa only [prepared, advice_len] using List.length_pos_of_ne_nil hne
  have hword :
      (((B.lift (β := σ × β) Prod.snd).retainInput prepared).map discard) =
        ((A.compose B).lift π).retainInput w := by
    have htrack : prepared.map Prod.snd = A (w.map π) := by
      exact retainInput_snd (A.lift π) w
    change (prepared ⨂ B (prepared.map Prod.snd)).map discard =
      w ⨂ B (A (w.map π))
    rw [htrack]
    apply List.ext_getElem (by simp [prepared])
    intro i hi hj
    simp [prepared, lift, discard]
  calc
    ((first.compose (second.compose relabel)).compile target).trace w (w.length - 1) =
        (second.compile (relabel.compile target)).trace prepared (w.length - 1) :=
      hfirst _ w trivial hne
    _ = (relabel.compile target).trace
        ((B.lift (β := σ × β) Prod.snd).retainInput prepared) (w.length - 1) := by
      simpa only [prepared, advice_len] using
        hsecond (relabel.compile target) prepared trivial hprepared
    _ = target.trace (((A.compose B).lift π).retainInput w) (w.length - 1) := by
      change (relabel.compile target).comp _ _ 0 = _
      rw [UniformLocal.relabel_word, hword]
      rfl

end CellularAutomatas.Advice
