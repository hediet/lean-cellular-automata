import CellularAutomatas.proofs.constructions.border_dead

namespace CellularAutomatas.MarkedPrefix.LT

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- Retain enough folded workspace for every output cell at the original LT
deadline, rather than only for the accepting cell at the origin. -/
def foldedTransform {F : Advice α Γ} (hF : F.IsLtAdvice) : DeadBorder where
  c := hF.c + 1
  C_orig := hF.witness.C

theorem foldedTransform_spec {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (p : ℤ) (hp : p ∈ w.range) :
    (foldedTransform hF).C.comp w (hF.c * (w.length - 1)) p =
      hF.witness.C.comp w (hF.c * (w.length - 1)) p := by
  apply (foldedTransform hF).spec_comp_row w _ _ p hp
  change hF.c * (w.length - 1) + w.length ≤ (hF.c + 1) * w.length
  calc
    hF.c * (w.length - 1) + w.length ≤ hF.c * w.length + w.length :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _
    _ = (hF.c + 1) * w.length := by simp [Nat.add_mul]

/-- The finite-strip transform computes the very same spatial advice at the
very same deadline as the original witness. -/
def foldedTransform_witness {F : Advice α Γ} (hF : F.IsLtAdvice) :
    F.IsTimeAdvice (fun n => hF.c * (n - 1)) where
  C := (foldedTransform hF).C
  spec w := by
    rw [hF.witness.spec w]
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    apply (foldedTransform_spec hF w i _).symm
    show 0 ≤ (i : ℤ) ∧ (i : ℤ) < w.length
    have hi' : i < w.length := by simpa using hi
    constructor <;> omega

theorem foldedTransform_border_dead {F : Advice α Γ} (hF : F.IsLtAdvice) :
    (foldedTransform hF).C.dead (foldedTransform hF).C.border :=
  (foldedTransform hF).spec_left_border_dead

end CellularAutomatas.MarkedPrefix.LT
