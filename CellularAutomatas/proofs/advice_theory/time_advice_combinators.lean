import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.basic_ca_id
import CellularAutomatas.proofs.constructions.basic_product_ca

namespace CellularAutomatas

variable {α Γ Δ Θ : Type}
variable [Alphabet α] [Alphabet Γ] [Alphabet Δ] [Alphabet Θ]

namespace Advice

/-- An `n`-time advice is a spatial advice available at time `|w|`. -/
abbrev IsNTimeAdvice (adv : Advice α Γ) :=
  adv.IsTimeAdvice (fun n => n)

/-- The input word itself, regarded as advice. -/
def identity (α : Type) : Advice α α :=
  ⟨id, fun _ => rfl⟩

/-- Apply a symbol map pointwise to an advice. -/
def map (f : Γ → Δ) (adv : Advice α Γ) : Advice α Δ where
  f w := (adv w).map f
  len w := by simp

/-- Pair two equal-length advices pointwise. -/
def zip (left : Advice α Γ) (right : Advice α Δ) : Advice α (Γ × Δ) where
  f w := left w ⨂ right w
  len w := by simp

omit [Alphabet α] in
@[simp]
lemma identity_apply (w : Word α) : identity α w = w := rfl

omit [Alphabet α] [Alphabet Γ] [Alphabet Δ] in
@[simp]
lemma map_apply (f : Γ → Δ) (adv : Advice α Γ) (w : Word α) :
    map f adv w = (adv w).map f := rfl

omit [Alphabet α] [Alphabet Γ] [Alphabet Δ] in
@[simp]
lemma zip_apply (left : Advice α Γ) (right : Advice α Δ) (w : Word α) :
    zip left right w = left w ⨂ right w := rfl

omit [Alphabet α] [Alphabet Γ] in
/-- Zipping the identity advice with `adv` is its annotated input word. -/
lemma zip_identity_eq_annotate (adv : Advice α Γ) (w : Word α) :
    zip (identity α) adv w = adv.annotate w := rfl

/-- The identity advice is available at every time bound. -/
def identity_isTimeAdvice (t : ℕ → ℕ) :
    (identity α).IsTimeAdvice t where
  C := (CellAutomaton.idCA (Option α)).map_project (·.getD default)
  spec w := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp only [List.getElem_map, List.getElem_range]
      rw [comp_of_map_project, CellAutomaton.idCA.comp_spec]
      have hi_w : i < w.length := by simpa using hi
      change w[i] = (word_to_config w (i : ℤ)).getD default
      rw [word_to_config_natcast_eq hi_w]
      rfl

/-- A symbol map preserves the time at which advice is available. -/
def IsTimeAdvice.map {adv : Advice α Γ} {t : ℕ → ℕ}
    (h : adv.IsTimeAdvice t) (f : Γ → Δ) :
    (Advice.map f adv).IsTimeAdvice t where
  C := h.C.map_project f
  spec w := by
    show (adv w).map f = (List.range w.length).map
      (fun (i : ℕ) => (h.C.map_project f).comp ⟬w⟭ (t w.length) (i : ℤ))
    rw [h.spec]
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp only [List.getElem_map, List.getElem_range, comp_of_map_project]

/-- Pointwise zip preserves a common advice-computation time. -/
def IsTimeAdvice.zip {left : Advice α Γ} {right : Advice α Δ} {t : ℕ → ℕ}
    (hLeft : left.IsTimeAdvice t) (hRight : right.IsTimeAdvice t) :
    (Advice.zip left right).IsTimeAdvice t where
  C := hLeft.C ⨂ hRight.C
  spec w := by
    show left w ⨂ right w = (List.range w.length).map
      (fun (i : ℕ) => (hLeft.C ⨂ hRight.C).comp ⟬w⟭ (t w.length) (i : ℤ))
    rw [hLeft.spec, hRight.spec]
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
        ca_zip_comp]

end Advice

end CellularAutomatas
