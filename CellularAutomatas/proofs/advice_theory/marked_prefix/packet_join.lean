import CellularAutomatas.defs

namespace CellularAutomatas.MarkedPrefix.PacketJoin

open CellAutomaton

/-- A source emits one payload at each position, at the prescribed time. -/
def EmitsAt (source : CellAutomaton α (Option β)) (c : Config α)
    (τ : ℤ → ℕ) (value : ℤ → β) : Prop :=
  ∀ t p, source.comp ⦋c⦌ t p = if t = τ p then some (value p) else none

/-- State for two controllers, their first observed payloads, and the
one-tick output permission. The outer `Option`s are event markers; payloads
may themselves contain arbitrary `Option`s. -/
structure State (Q₁ Q₂ β γ : Type) where
  controller1 : Q₁
  controller2 : Q₂
  latch1 : Option β
  latch2 : Option γ
  fresh : Bool
deriving DecidableEq, Inhabited, Fintype

instance [Alphabet Q₁] [Alphabet Q₂] [Alphabet β] [Alphabet γ] :
    Alphabet (State Q₁ Q₂ β γ) where

/-- Keep the first observed event. -/
def retain (old next : Option β) : Option β :=
  match old with
  | some value => some value
  | none => next

/-- Run two one-shot producers in parallel, latch each first payload, and
emit their pair exactly once when both have become available. Initial
projections are latched so events at time zero are handled directly. -/
def C {α β γ : Type} [Alphabet β] [Alphabet γ]
    (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) :
    CellAutomaton α (Option (β × γ)) where
  Q := State C1.Q C2.Q β γ
  δ := fun left center right =>
    let next1 := C1.δ left.controller1 center.controller1 right.controller1
    let next2 := C2.δ left.controller2 center.controller2 right.controller2
    let latch1 := retain center.latch1 (C1.project next1)
    let latch2 := retain center.latch2 (C2.project next2)
    let fresh := !(center.latch1.isSome && center.latch2.isSome)
    ⟨next1, next2, latch1, latch2, fresh⟩
  embed := fun a =>
    let q1 := C1.embed a
    let q2 := C2.embed a
    ⟨q1, q2, C1.project q1, C2.project q2, true⟩
  project := fun state =>
    if state.fresh then
      state.latch1.bind fun value1 =>
        state.latch2.map fun value2 => (value1, value2)
    else none

variable {α β γ : Type} [Alphabet β] [Alphabet γ]

/-- The first controller is exactly the first source controller. -/
theorem controller1_spec (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α) (t : ℕ) (p : ℤ) :
    ((C C1 C2).nextt ⦋c⦌ t p).controller1 =
      C1.nextt ⦋c⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      change
        C1.δ
          ((C C1 C2).nextt ⦋c⦌ t (p - 1)).controller1
          ((C C1 C2).nextt ⦋c⦌ t p).controller1
          ((C C1 C2).nextt ⦋c⦌ t (p + 1)).controller1 =
        C1.δ
          (C1.nextt ⦋c⦌ t (p - 1))
          (C1.nextt ⦋c⦌ t p)
          (C1.nextt ⦋c⦌ t (p + 1))
      rw [ih (p - 1), ih p, ih (p + 1)]

/-- The second controller is exactly the second source controller. -/
theorem controller2_spec (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α) (t : ℕ) (p : ℤ) :
    ((C C1 C2).nextt ⦋c⦌ t p).controller2 =
      C2.nextt ⦋c⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      change
        C2.δ
          ((C C1 C2).nextt ⦋c⦌ t (p - 1)).controller2
          ((C C1 C2).nextt ⦋c⦌ t p).controller2
          ((C C1 C2).nextt ⦋c⦌ t (p + 1)).controller2 =
        C2.δ
          (C2.nextt ⦋c⦌ t (p - 1))
          (C2.nextt ⦋c⦌ t p)
          (C2.nextt ⦋c⦌ t (p + 1))
      rw [ih (p - 1), ih p, ih (p + 1)]

/-- One-step recurrence for the first latch. -/
private theorem latch1_succ (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α) (t : ℕ) (p : ℤ) :
    ((C C1 C2).nextt ⦋c⦌ (t + 1) p).latch1 =
      retain ((C C1 C2).nextt ⦋c⦌ t p).latch1
        (C1.comp ⦋c⦌ (t + 1) p) := by
  rw [CellAutomaton.nextt_succ]
  change
    retain ((C C1 C2).nextt ⦋c⦌ t p).latch1
      (C1.project (C1.δ
        ((C C1 C2).nextt ⦋c⦌ t (p - 1)).controller1
        ((C C1 C2).nextt ⦋c⦌ t p).controller1
        ((C C1 C2).nextt ⦋c⦌ t (p + 1)).controller1)) =
    retain ((C C1 C2).nextt ⦋c⦌ t p).latch1
      (C1.comp ⦋c⦌ (t + 1) p)
  congr 1
  rw [CellAutomaton.comp_apply, CellAutomaton.nextt_succ,
    CellAutomaton.next_apply]
  rw [controller1_spec C1 C2 c t (p - 1),
    controller1_spec C1 C2 c t p,
    controller1_spec C1 C2 c t (p + 1)]

/-- One-step recurrence for the second latch. -/
private theorem latch2_succ (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α) (t : ℕ) (p : ℤ) :
    ((C C1 C2).nextt ⦋c⦌ (t + 1) p).latch2 =
      retain ((C C1 C2).nextt ⦋c⦌ t p).latch2
        (C2.comp ⦋c⦌ (t + 1) p) := by
  rw [CellAutomaton.nextt_succ]
  change
    retain ((C C1 C2).nextt ⦋c⦌ t p).latch2
      (C2.project (C2.δ
        ((C C1 C2).nextt ⦋c⦌ t (p - 1)).controller2
        ((C C1 C2).nextt ⦋c⦌ t p).controller2
        ((C C1 C2).nextt ⦋c⦌ t (p + 1)).controller2)) =
    retain ((C C1 C2).nextt ⦋c⦌ t p).latch2
      (C2.comp ⦋c⦌ (t + 1) p)
  congr 1
  rw [CellAutomaton.comp_apply, CellAutomaton.nextt_succ,
    CellAutomaton.next_apply]
  rw [controller2_spec C1 C2 c t (p - 1),
    controller2_spec C1 C2 c t p,
    controller2_spec C1 C2 c t (p + 1)]

/-- Pointwise first-memory invariant. Only the source behavior at `p` is
needed once controller tracking has been established. -/
theorem latch1_spec_at (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (p : ℤ) (τ1 : ℕ) (value1 : β)
    (h1 : ∀ t, C1.comp ⦋c⦌ t p =
      if t = τ1 then some value1 else none)
    (t : ℕ) :
    ((C C1 C2).nextt ⦋c⦌ t p).latch1 =
      if τ1 ≤ t then some value1 else none := by
  induction t with
  | zero =>
      have hsource := h1 0
      change C1.project (C1.embed (c p)) =
        if τ1 ≤ 0 then some value1 else none
      simpa only [CellAutomaton.comp_apply, CellAutomaton.nextt_zero,
        CellAutomaton.embed_config_apply, Nat.le_zero, eq_comm] using hsource
  | succ t ih =>
      rw [latch1_succ, ih, h1 (t + 1)]
      by_cases hold : τ1 ≤ t
      · have hnow : τ1 ≤ t + 1 := by omega
        simp [retain, hold, hnow]
      · by_cases hevent : t + 1 = τ1
        · simp [retain, hold, hevent]
        · have hnow : ¬τ1 ≤ t + 1 := by omega
          simp [retain, hold, hevent, hnow]

/-- Global first-memory invariant retained as a corollary of the pointwise
form. -/
theorem latch1_spec (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (τ1 : ℤ → ℕ) (value1 : ℤ → β) (h1 : EmitsAt C1 c τ1 value1)
    (t : ℕ) (p : ℤ) :
    ((C C1 C2).nextt ⦋c⦌ t p).latch1 =
      if τ1 p ≤ t then some (value1 p) else none :=
  latch1_spec_at C1 C2 c p (τ1 p) (value1 p) (fun s => h1 s p) t

/-- Pointwise second-memory invariant. -/
theorem latch2_spec_at (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (p : ℤ) (τ2 : ℕ) (value2 : γ)
    (h2 : ∀ t, C2.comp ⦋c⦌ t p =
      if t = τ2 then some value2 else none)
    (t : ℕ) :
    ((C C1 C2).nextt ⦋c⦌ t p).latch2 =
      if τ2 ≤ t then some value2 else none := by
  induction t with
  | zero =>
      have hsource := h2 0
      change C2.project (C2.embed (c p)) =
        if τ2 ≤ 0 then some value2 else none
      simpa only [CellAutomaton.comp_apply, CellAutomaton.nextt_zero,
        CellAutomaton.embed_config_apply, Nat.le_zero, eq_comm] using hsource
  | succ t ih =>
      rw [latch2_succ, ih, h2 (t + 1)]
      by_cases hold : τ2 ≤ t
      · have hnow : τ2 ≤ t + 1 := by omega
        simp [retain, hold, hnow]
      · by_cases hevent : t + 1 = τ2
        · simp [retain, hold, hevent]
        · have hnow : ¬τ2 ≤ t + 1 := by omega
          simp [retain, hold, hevent, hnow]

/-- Global second-memory invariant retained as a corollary. -/
theorem latch2_spec (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (τ2 : ℤ → ℕ) (value2 : ℤ → γ) (h2 : EmitsAt C2 c τ2 value2)
    (t : ℕ) (p : ℤ) :
    ((C C1 C2).nextt ⦋c⦌ t p).latch2 =
      if τ2 p ≤ t then some (value2 p) else none :=
  latch2_spec_at C1 C2 c p (τ2 p) (value2 p) (fun s => h2 s p) t

/-- If the first source is permanently silent at a position, its latch stays
empty there. -/
theorem latch1_none_at (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α) (p : ℤ)
    (h1 : ∀ t, C1.comp ⦋c⦌ t p = none) (t : ℕ) :
    ((C C1 C2).nextt ⦋c⦌ t p).latch1 = none := by
  induction t with
  | zero =>
      have hsource := h1 0
      change C1.project (C1.embed (c p)) = none
      simpa only [CellAutomaton.comp_apply, CellAutomaton.nextt_zero,
        CellAutomaton.embed_config_apply] using hsource
  | succ t ih =>
      rw [latch1_succ, ih, h1 (t + 1)]
      rfl

/-- Permanent silence of the first source forces permanent silence of the
join, independently of the second source. -/
theorem comp_none_of_left_none_at (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α) (p : ℤ)
    (h1 : ∀ t, C1.comp ⦋c⦌ t p = none) (t : ℕ) :
    (C C1 C2).comp ⦋c⦌ t p = none := by
  rw [CellAutomaton.comp_apply]
  change
    (if ((C C1 C2).nextt ⦋c⦌ t p).fresh then
      ((C C1 C2).nextt ⦋c⦌ t p).latch1.bind fun first =>
        ((C C1 C2).nextt ⦋c⦌ t p).latch2.map fun second => (first, second)
    else none) = none
  rw [latch1_none_at C1 C2 c p h1 t]
  simp

/-- One-step recurrence for the one-shot permission bit. -/
private theorem fresh_succ (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α) (t : ℕ) (p : ℤ) :
    ((C C1 C2).nextt ⦋c⦌ (t + 1) p).fresh =
      !(((C C1 C2).nextt ⦋c⦌ t p).latch1.isSome &&
        ((C C1 C2).nextt ⦋c⦌ t p).latch2.isSome) := by
  rw [CellAutomaton.nextt_succ]
  rfl

/-- Pointwise permission-bit invariant. -/
theorem fresh_spec_at (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (p : ℤ) (τ1 τ2 : ℕ) (value1 : β) (value2 : γ)
    (h1 : ∀ t, C1.comp ⦋c⦌ t p =
      if t = τ1 then some value1 else none)
    (h2 : ∀ t, C2.comp ⦋c⦌ t p =
      if t = τ2 then some value2 else none)
    (t : ℕ) :
    ((C C1 C2).nextt ⦋c⦌ t p).fresh =
      decide (t ≤ max τ1 τ2) := by
  cases t with
  | zero =>
      change true = decide (0 ≤ max τ1 τ2)
      simp
  | succ t =>
      rw [fresh_succ,
        latch1_spec_at C1 C2 c p τ1 value1 h1 t,
        latch2_spec_at C1 C2 c p τ2 value2 h2 t]
      by_cases hleft : τ1 ≤ t
      · by_cases hright : τ2 ≤ t
        · have hmax : ¬t + 1 ≤ max τ1 τ2 := by
            have hbound : max τ1 τ2 ≤ t :=
              Nat.max_le.mpr ⟨hleft, hright⟩
            omega
          simp [hleft, hright, hmax]
        · have htau : t + 1 ≤ τ2 := by omega
          have hmax : t + 1 ≤ max τ1 τ2 :=
            le_trans htau (Nat.le_max_right _ _)
          simp [hleft, hright, hmax]
      · have htau : t + 1 ≤ τ1 := by omega
        have hmax : t + 1 ≤ max τ1 τ2 :=
          le_trans htau (Nat.le_max_left _ _)
        simp [hleft, hmax]

/-- The permission bit remains true through the join time and is false
afterward. -/
theorem fresh_spec (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (τ1 τ2 : ℤ → ℕ) (value1 : ℤ → β) (value2 : ℤ → γ)
    (h1 : EmitsAt C1 c τ1 value1) (h2 : EmitsAt C2 c τ2 value2)
    (t : ℕ) (p : ℤ) :
    ((C C1 C2).nextt ⦋c⦌ t p).fresh =
      decide (t ≤ max (τ1 p) (τ2 p)) :=
  fresh_spec_at C1 C2 c p (τ1 p) (τ2 p) (value1 p) (value2 p)
    (fun s => h1 s p) (fun s => h2 s p) t

/-- Pointwise one-shot join theorem. -/
theorem comp_spec_at (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (p : ℤ) (τ1 τ2 : ℕ) (value1 : β) (value2 : γ)
    (h1 : ∀ t, C1.comp ⦋c⦌ t p =
      if t = τ1 then some value1 else none)
    (h2 : ∀ t, C2.comp ⦋c⦌ t p =
      if t = τ2 then some value2 else none)
    (t : ℕ) :
    (C C1 C2).comp ⦋c⦌ t p =
      if t = max τ1 τ2 then
        some (value1, value2)
      else none := by
  rw [CellAutomaton.comp_apply]
  change
    (if ((C C1 C2).nextt ⦋c⦌ t p).fresh then
      ((C C1 C2).nextt ⦋c⦌ t p).latch1.bind fun first =>
        ((C C1 C2).nextt ⦋c⦌ t p).latch2.map fun second => (first, second)
    else none) = _
  rw [latch1_spec_at C1 C2 c p τ1 value1 h1 t,
    latch2_spec_at C1 C2 c p τ2 value2 h2 t,
    fresh_spec_at C1 C2 c p τ1 τ2 value1 value2 h1 h2 t]
  by_cases hevent : t = max τ1 τ2
  · simp [hevent]
  · by_cases hbefore : t < max τ1 τ2
    · have hfresh : t ≤ max τ1 τ2 := Nat.le_of_lt hbefore
      by_cases hleft : τ1 ≤ t
      · have hright : ¬τ2 ≤ t := by
          intro hright
          have : max τ1 τ2 ≤ t := Nat.max_le.mpr ⟨hleft, hright⟩
          omega
        simp [hevent, hfresh, hleft, hright]
      · simp [hevent, hfresh, hleft]
    · have hpast : ¬t ≤ max τ1 τ2 := by omega
      simp [hevent, hpast]

/-- The joined CA emits the pair exactly at the later source time and is
silent at every other time and position. -/
theorem comp_spec (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (τ1 τ2 : ℤ → ℕ) (value1 : ℤ → β) (value2 : ℤ → γ)
    (h1 : EmitsAt C1 c τ1 value1) (h2 : EmitsAt C2 c τ2 value2)
    (t : ℕ) (p : ℤ) :
    (C C1 C2).comp ⦋c⦌ t p =
      if t = max (τ1 p) (τ2 p) then
        some (value1 p, value2 p)
      else none :=
  comp_spec_at C1 C2 c p (τ1 p) (τ2 p) (value1 p) (value2 p)
    (fun s => h1 s p) (fun s => h2 s p) t

/-- Predicate-form composition theorem for downstream constructions. -/
theorem emitsAt (C1 : CellAutomaton α (Option β))
    (C2 : CellAutomaton α (Option γ)) (c : Config α)
    (τ1 τ2 : ℤ → ℕ) (value1 : ℤ → β) (value2 : ℤ → γ)
    (h1 : EmitsAt C1 c τ1 value1) (h2 : EmitsAt C2 c τ2 value2) :
    EmitsAt (C C1 C2) c
      (fun p => max (τ1 p) (τ2 p))
      (fun p => (value1 p, value2 p)) := by
  intro t p
  exact comp_spec C1 C2 c τ1 τ2 value1 value2 h1 h2 t p

end CellularAutomatas.MarkedPrefix.PacketJoin
