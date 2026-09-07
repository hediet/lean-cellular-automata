import CellularAutomatas.proofs.advice_theory.marked_prefix.async_driven

namespace CellularAutomatas.AsyncHalfLine

open CellAutomaton

namespace OriginPackets

variable {α ι : Type}
variable (P : CellAutomaton (Option α) (Option ι))

def boundary (c : Config (Option α)) (p : ℤ) : Bool :=
  (c p).isSome && !(c (p - 1)).isSome

/-- Preserve initial occupancy and compute its left boundary in one tick. -/
def C : CellAutomaton (Option α) (Bool × Option ι) where
  Q := P.Q × Bool × Bool
  δ := fun left center right =>
    (P.δ left.1 center.1 right.1,
      center.2.1, center.2.1 && !left.2.1)
  embed := fun a => (P.embed a, a.isSome, false)
  project := fun q => (q.2.2, P.project q.1)

lemma state_spec (c : Config (Option α)) (t : ℕ) (p : ℤ) :
    (C P).nextt ⦋c⦌ t p =
      (P.nextt ⦋c⦌ t p, (c p).isSome,
        if t = 0 then false else boundary c p) := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    rw [ih (p - 1), ih p, ih (p + 1)]
    rfl

lemma comp_spec (c : Config (Option α)) (t : ℕ) (p : ℤ) :
    (C P).comp ⦋c⦌ t p =
      (if t = 0 then false else boundary c p, P.comp ⦋c⦌ t p) := by
  change (C P).project ((C P).nextt ⦋c⦌ t p) = _
  rw [state_spec]
  rfl

lemma boundary_word (w : Word α) (hw : 0 < w.length) (p : ℕ) :
    boundary (word_to_config w) (p : ℤ) = decide (p = 0) := by
  by_cases hp : p = 0
  · subst p
    simp [boundary, word_to_config, hw]
  · by_cases hin : p < w.length
    · have hc :
          (p : ℤ) ≥ 0 ∧ (p : ℤ) < w.length := by omega
      have hl :
          (p : ℤ) - 1 ≥ 0 ∧ (p : ℤ) - 1 < w.length := by omega
      simp [boundary, word_to_config, hc, hl, hp]
      omega
    · simp [boundary, word_to_config, hin, hp]

lemma origin_word (w : Word α) (hw : 0 < w.length)
    (t p : ℕ) (ht : 0 < t) :
    ((C P).comp ⦋word_to_config w⦌ t (p : ℤ)).1 =
      decide (p = 0) := by
  rw [comp_spec]
  simp only [if_neg (Nat.ne_of_gt ht)]
  exact boundary_word w hw p

/-- Add origin detection to any packet producer without changing packet times. -/
def driven {β : Type}
    (S : CellAutomaton ι β) (dead : S.Q) (padding : β) : Driven where
  inner := S
  controller := C P
  dead := dead
  padding := padding

lemma controllerSpec {β : Type}
    (S : CellAutomaton ι β) (dead : S.Q) (padding : β)
    (w : Word α) (hw : 0 < w.length)
    (R : ℕ → ℕ) (input : ℕ → ι)
    (hP : ∀ t p : ℕ,
      P.comp ⦋word_to_config w⦌ t (p : ℤ) = packet R input t p) :
    (driven P S dead padding).ControllerSpec
      (word_to_config w) R input := by
  constructor
  · intro t p
    change ((C P).comp ⦋word_to_config w⦌ t (p : ℤ)).2 = _
    rw [comp_spec]
    exact hP t p
  · intro t p ht
    change ((C P).comp ⦋word_to_config w⦌ t (p : ℤ)).1 = _
    exact origin_word P w hw t p (by omega)

end OriginPackets
end CellularAutomatas.AsyncHalfLine
