import CellularAutomatas.proofs.basic

namespace CellularAutomatas.Advice

variable {α σ Γ : Type} [Alphabet α] [Alphabet σ] [Alphabet Γ]

/-- Input alphabet lifts do not change a spatial transformation's deadline. -/
def IsTimeAdvice.lift {F : Advice α Γ} {time : ℕ → ℕ}
    (hF : F.IsTimeAdvice time) (π : σ → α) :
    (F.lift π).IsTimeAdvice time where
  C := hF.C.map_embed (Option.map π)
  spec w := by
    change F (w.map π) = _
    rw [hF.spec (w.map π)]
    simp only [List.length_map]
    apply List.map_congr_left
    intro i _
    change
      hF.C.project (hF.C.nextt ⦋w.map π⦌ (time w.length) i) =
        hF.C.project
          ((hF.C.map_embed (Option.map π)).nextt ⦋w⦌ (time w.length) i)
    rw [map_embed_nextt_word]

/-- Extra input tracks are retained by the consumer but may be ignored by the
LT advice producer, with exactly the same linear coefficient. -/
def IsLtAdvice.lift {F : Advice α Γ} (hF : F.IsLtAdvice) (π : σ → α) :
    (F.lift π).IsLtAdvice where
  c := hF.c
  witness := hF.witness.lift π

end CellularAutomatas.Advice
