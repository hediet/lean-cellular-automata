import CellularAutomatas.proofs.basic

namespace CellularAutomatas

/-- Output `i` stabilizes after input position `i + anticipation`. Taking a
prefix beyond the actual end leaves the word unchanged. -/
def Advice.HasAnticipation {α Γ : Type} (advice : Advice α Γ)
    (anticipation : ℕ) : Prop :=
  ∀ (w : Word α) (i : ℕ), i < w.length →
    (advice w)[i]? = (advice (w.take (i + anticipation + 1)))[i]?

def Advice.BoundedAnticipation {α Γ : Type} (advice : Advice α Γ) : Prop :=
  ∃ anticipation, advice.HasAnticipation anticipation

theorem Advice.HasAnticipation.eq_take_of_le {α Γ : Type} {advice : Advice α Γ}
    {anticipation : ℕ} (h : advice.HasAnticipation anticipation)
    (w : Word α) (i cutoff : ℕ) (hi : i < w.length)
    (hcutoff : i + anticipation + 1 ≤ cutoff) :
    (advice w)[i]? = (advice (w.take cutoff))[i]? := by
  have hprefix : i < (w.take cutoff).length := by
    simp only [List.length_take]
    omega
  have hshort := h (w.take cutoff) i hprefix
  have hnested : (w.take cutoff).take (i + anticipation + 1) =
      w.take (i + anticipation + 1) := by
    simp only [List.take_take, Nat.min_eq_left hcutoff]
  calc
    (advice w)[i]? = (advice (w.take (i + anticipation + 1)))[i]? := h w i hi
    _ = (advice (w.take cutoff))[i]? := by
      rw [hnested] at hshort
      exact hshort.symm

theorem Advice.HasAnticipation.mono {α Γ : Type} {advice : Advice α Γ}
    {a b : ℕ} (h : advice.HasAnticipation a) (hab : a ≤ b) :
    advice.HasAnticipation b := by
  intro w i hi
  show (advice w)[i]? = (advice (w.take (i + b + 1)))[i]?
  exact h.eq_take_of_le w i (i + b + 1) hi (by omega)

/-- A fixed-delay origin trace computes every occupied advice symbol.
Nothing is required before the delay or after the last output symbol. -/
structure Advice.DelayedTrace {α Γ : Type} (advice : Advice α Γ) (delay : ℕ) where
  C : CellAutomaton (Option α) Γ
  spec : ∀ (w : Word α) (i : ℕ) (hi : i < w.length),
    C.trace w (delay + i) = (advice w)[i]'(by simpa using hi)

end CellularAutomatas
