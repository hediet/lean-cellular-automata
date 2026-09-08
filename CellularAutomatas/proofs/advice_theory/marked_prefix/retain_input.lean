import CellularAutomatas.proofs.advice_theory.rt_closed.of_compose

namespace CellularAutomatas.Advice

/-- Treat advice application as an input-retaining word transformation. -/
def retainInput {α Γ : Type} (adv : Advice α Γ) : Advice α (α × Γ) where
  f := adv.annotate
  len w := by simp [annotate]

@[simp] theorem retainInput_apply {α Γ : Type} (adv : Advice α Γ) (w : Word α) :
    adv.retainInput w = w ⨂ adv w := rfl

@[simp] theorem retainInput_fst {α Γ : Type} (adv : Advice α Γ) (w : Word α) :
    (adv.retainInput w).map Prod.fst = w := by
  apply List.map_fst_zip
  simp

@[simp] theorem retainInput_snd {α Γ : Type} (adv : Advice α Γ) (w : Word α) :
    (adv.retainInput w).map Prod.snd = adv w := by
  apply List.map_snd_zip
  simp

/-- The original input is already available to an advised consumer. Retaining
it as an explicit output track therefore preserves strong RT closure. -/
def rt_closed_retainInput {α Γ : Type} [Alphabet α] [Alphabet Γ]
    (adv : Advice α Γ) (hadv : adv.rt_closed) : adv.retainInput.rt_closed := by
  intro σ _ π
  refine {
    map := fun consumer => (hadv σ π).map
      (consumer.map_embed (fun pair : σ × Γ => (pair.1, (π pair.1, pair.2))))
    spec := ?_
  }
  intro consumer
  rw [(hadv σ π).spec]
  ext w
  change
    (adv.lift π).annotate w ∈
        (consumer.map_embed (fun pair : σ × Γ => (pair.1, (π pair.1, pair.2)))).L ↔
      (adv.retainInput.lift π).annotate w ∈ consumer.L
  rw [map_embed_L]
  have hword :
      ((adv.lift π).annotate w).map
          (fun pair : σ × Γ => (pair.1, (π pair.1, pair.2))) =
        (adv.retainInput.lift π).annotate w := by
    apply List.ext_getElem (by simp [annotate])
    intro i hi hj
    simp [retainInput, annotate, lift]
  rw [hword]

end CellularAutomatas.Advice
