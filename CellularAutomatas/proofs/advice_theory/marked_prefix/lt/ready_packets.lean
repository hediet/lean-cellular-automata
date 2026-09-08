import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_join

namespace CellularAutomatas.MarkedPrefix.LT

/-- A block is ready only when every one of its output slots is ready.
The outer option records completion, not a default value for missing output. -/
def readyBlock {q : ℕ} {Γ : Type} (block : Fin q → Option Γ) :
    Option (Fin q → Γ) :=
  if h : ∀ i, (block i).isSome then
    some (fun i => (block i).get (h i))
  else none

@[simp] theorem readyBlock_some {q : ℕ} {Γ : Type} (block : Fin q → Γ) :
    readyBlock (fun i => some (block i)) = some block := by
  simp [readyBlock]

@[simp] theorem readyBlock_none {q : ℕ} [NeZero q] {Γ : Type} :
    readyBlock (fun _ : Fin q => (none : Option Γ)) = none := by
  simp [readyBlock]

/-- A monotone local simulation clock supplies an actual first ready time,
not merely an upper bound on eventual completion. -/
theorem exists_ready_time (height : ℕ → ℕ) (release deadline generation : ℕ)
    (hmono : Monotone height) (hpositive : 0 < generation)
    (hbefore : ∀ t, t < release → height t = 0)
    (hdeadline : generation ≤ height deadline) :
    ∃ τ, release ≤ τ ∧ τ ≤ deadline ∧
      ∀ t, generation ≤ height t ↔ τ ≤ t := by
  have hready : ∃ t, generation ≤ height t := ⟨deadline, hdeadline⟩
  let τ := Nat.find hready
  have hτ : generation ≤ height τ := Nat.find_spec hready
  refine ⟨τ, ?_, Nat.find_le hdeadline, ?_⟩
  · show release ≤ τ
    by_contra hlt
    rw [hbefore τ (by omega)] at hτ
    omega
  · intro t
    show generation ≤ height t ↔ τ ≤ t
    constructor
    · exact fun ht => Nat.find_le ht
    · intro ht
      calc
        generation ≤ height τ := hτ
        _ ≤ height t := hmono ht

namespace FirstOutput

/-- Convert a persistent local completion signal to a single event, without
adding a tick of delay, including when the source is already ready at time zero. -/
def C {α β : Type} (source : CellAutomaton α (Option β)) :
    CellAutomaton α (Option β) where
  Q := source.Q × Bool
  δ := fun left center right =>
    (source.δ left.1 center.1 right.1,
      center.2 || (source.project center.1).isSome)
  embed := fun input => (source.embed input, false)
  project := fun state => if state.2 then none else source.project state.1

variable {α β : Type} (source : CellAutomaton α (Option β))

theorem controller_spec (input : Config α) (t : ℕ) (p : ℤ) :
    ((C source).nextt ⦋input⦌ t p).1 = source.nextt ⦋input⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ,
      CellAutomaton.next_apply, CellAutomaton.next_apply]
    change source.δ _ _ _ = source.δ _ _ _
    rw [ih, ih, ih]

private theorem seen_spec (input : Config α) (p : ℤ) (τ : ℕ) (value : β)
    (hsource : ∀ t, source.comp ⦋input⦌ t p =
      if τ ≤ t then some value else none) (t : ℕ) :
    ((C source).nextt ⦋input⦌ t p).2 = decide (τ < t) := by
  induction t with
  | zero => simp [CellAutomaton.nextt_zero, CellAutomaton.embed_config, C]
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    change
      (((C source).nextt ⦋input⦌ t p).2 ||
        (source.project ((C source).nextt ⦋input⦌ t p).1).isSome) = _
    rw [ih, controller_spec]
    change (decide (τ < t) || (source.comp ⦋input⦌ t p).isSome) = _
    rw [hsource]
    by_cases hready : τ ≤ t
    · simp [hready, show τ < t + 1 by omega]
    · simp [hready, show ¬τ < t by omega, show ¬τ < t + 1 by omega]

theorem comp_spec (input : Config α) (p : ℤ) (τ : ℕ) (value : β)
    (hsource : ∀ t, source.comp ⦋input⦌ t p =
      if τ ≤ t then some value else none) (t : ℕ) :
    (C source).comp ⦋input⦌ t p =
      if t = τ then some value else none := by
  change
    (if ((C source).nextt ⦋input⦌ t p).2 then none
      else source.project ((C source).nextt ⦋input⦌ t p).1) = _
  rw [seen_spec source input p τ value hsource, controller_spec]
  change (if decide (τ < t) then none else source.comp ⦋input⦌ t p) = _
  rw [hsource]
  by_cases hevent : t = τ
  · simp [hevent]
  · by_cases hpast : τ < t
    · simp [hpast, hevent]
    · simp [hpast, hevent, show ¬τ ≤ t by omega]

theorem comp_none (input : Config α) (t : ℕ) (p : ℤ)
    (hsource : source.comp ⦋input⦌ t p = none) :
    (C source).comp ⦋input⦌ t p = none := by
  change
    (if ((C source).nextt ⦋input⦌ t p).2 then none
      else source.project ((C source).nextt ⦋input⦌ t p).1) = none
  rw [controller_spec]
  change (if _ then none else source.comp ⦋input⦌ t p) = none
  rw [hsource]
  split <;> rfl

end FirstOutput
end CellularAutomatas.MarkedPrefix.LT
