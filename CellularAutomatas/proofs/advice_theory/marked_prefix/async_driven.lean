import CellularAutomatas.proofs.advice_theory.marked_prefix.asynchronous_half_line

namespace CellularAutomatas.AsyncHalfLine

open CellAutomaton

lemma step_origin_left_independent {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (packet : Option Q) (left left' center right : State Q) :
    step δ dead true packet left center right =
      step δ dead true packet left' center right := by
  cases center with
  | none => rfl
  | some q =>
    rcases q with ⟨k, current, previous⟩
    rfl

lemma packet_map {Q A : Type} (f : Q → A)
    (R : ℕ → ℕ) (input : ℕ → Q) (t p : ℕ) :
    (packet R input t p).map f =
      packet R (fun q => f (input q)) t p := by
  unfold packet
  split <;> rfl

lemma run_before_release {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (R : ℕ → ℕ) (input : ℕ → Q) (t p : ℕ)
    (ht : t < R p) :
    run δ dead R input t p = none := by
  induction t with
  | zero =>
    simp only [run, packet,
      if_neg (by omega : ¬0 = R p), Option.map_none]
  | succ t ih =>
    rw [run, ih (by omega)]
    simp only [step, packet,
      if_neg (by omega : ¬t + 1 = R p), Option.map_none]

def output {Q B : Type}
    (project : Q → B) (padding : B) : State Q → B
  | none => padding
  | some (_, current, _) => project current

/-- A finite controller supplies an origin bit and inner-alphabet packets. -/
structure Driven where
  {α ι β : Type}
  inner : CellAutomaton ι β
  controller : CellAutomaton α (Bool × Option ι)
  dead : inner.Q
  padding : β

namespace Driven

variable (e : Driven)

def C : CellAutomaton e.α e.β where
  Q := e.controller.Q × State e.inner.Q
  δ := fun left center right =>
    let ctl := e.controller.δ left.1 center.1 right.1
    let signal := e.controller.project ctl
    (ctl, step e.inner.δ e.dead signal.1
      (signal.2.map e.inner.embed) left.2 center.2 right.2)
  embed := fun a =>
    let ctl := e.controller.embed a
    (ctl, ((e.controller.project ctl).2.map e.inner.embed).map
      (fun q => (0, q, q)))
  project := fun state =>
    output e.inner.project e.padding state.2

/-- Origin detection may be wrong before release: the inactive rule ignores it.
No controller behavior or clocks are prescribed at negative positions. -/
structure ControllerSpec
    (c : Config e.α) (R : ℕ → ℕ) (input : ℕ → e.ι) : Prop where
  packets : ∀ t p : ℕ,
    (e.controller.comp ⦋c⦌ t (p : ℤ)).2 = packet R input t p
  origin : ∀ t p : ℕ, R p < t →
    (e.controller.comp ⦋c⦌ t (p : ℤ)).1 = decide (p = 0)

lemma controller_track
    (c : Config e.α) (t : ℕ) (p : ℤ) :
    (e.C.nextt ⦋c⦌ t p).1 = e.controller.nextt ⦋c⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    change e.controller.δ
      ((e.C.nextt ⦋c⦌ t (p - 1)).1)
      ((e.C.nextt ⦋c⦌ t p).1)
      ((e.C.nextt ⦋c⦌ t (p + 1)).1) = _
    rw [ih (p - 1), ih p, ih (p + 1)]

lemma data_step
    (c : Config e.α) (t : ℕ) (p : ℤ) :
    (e.C.nextt ⦋c⦌ (t + 1) p).2 =
      step e.inner.δ e.dead
        (e.controller.comp ⦋c⦌ (t + 1) p).1
        ((e.controller.comp ⦋c⦌ (t + 1) p).2.map e.inner.embed)
        ((e.C.nextt ⦋c⦌ t (p - 1)).2)
        ((e.C.nextt ⦋c⦌ t p).2)
        ((e.C.nextt ⦋c⦌ t (p + 1)).2) := by
  rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
  change step e.inner.δ e.dead
    (e.controller.project (e.controller.δ
      ((e.C.nextt ⦋c⦌ t (p - 1)).1)
      ((e.C.nextt ⦋c⦌ t p).1)
      ((e.C.nextt ⦋c⦌ t (p + 1)).1))).1
    ((e.controller.project (e.controller.δ
      ((e.C.nextt ⦋c⦌ t (p - 1)).1)
      ((e.C.nextt ⦋c⦌ t p).1)
      ((e.C.nextt ⦋c⦌ t (p + 1)).1))).2.map e.inner.embed)
    _ _ _ = _
  rw [e.controller_track c t (p - 1),
    e.controller_track c t p,
    e.controller_track c t (p + 1)]
  simp only [CellAutomaton.comp_apply,
    CellAutomaton.nextt_succ, CellAutomaton.next_apply]

lemma data_track
    (c : Config e.α) (R : ℕ → ℕ) (input : ℕ → e.ι)
    (hs : e.ControllerSpec c R input) (t p : ℕ) :
    (e.C.nextt ⦋c⦌ t (p : ℤ)).2 =
      run e.inner.δ e.dead R
        (fun q => e.inner.embed (input q)) t p := by
  induction t generalizing p with
  | zero =>
    have h := hs.packets 0 p
    change
      (e.controller.project (e.controller.embed (c (p : ℤ)))).2 = _
      at h
    change
      ((e.controller.project (e.controller.embed (c (p : ℤ)))).2.map
        e.inner.embed).map (fun q => (0, q, q)) = _
    rw [h, packet_map]
    rfl
  | succ t ih =>
    rw [e.data_step, hs.packets (t + 1) p, packet_map]
    by_cases ha : R p < t + 1
    · rw [hs.origin (t + 1) p ha]
      by_cases hp : p = 0
      · subst p
        rw [show ((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) from by omega,
          ih 0, ih 1]
        rw [run]
        exact step_origin_left_independent _ _ _ _ _ _ _
      · have hleft :
            (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by omega
        have hright :
            (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ) := by omega
        rw [hleft, hright, ih (p - 1), ih p, ih (p + 1)]
        rfl
    · have ht : t < R p := by omega
      rw [ih p, run_before_release _ _ _ _ t p ht]
      rw [run, run_before_release _ _ _ _ t p ht]
      rfl

lemma comp_eq_output
    (c : Config e.α) (R : ℕ → ℕ) (input : ℕ → e.ι)
    (hs : e.ControllerSpec c R input) (t p : ℕ) :
    e.C.comp ⦋c⦌ t (p : ℤ) =
      output e.inner.project e.padding
        (run e.inner.δ e.dead R
          (fun q => e.inner.embed (input q)) t p) := by
  change
    output e.inner.project e.padding
      ((e.C.nextt ⦋c⦌ t (p : ℤ)).2) = _
  rw [e.data_track c R input hs]

lemma comp_of_run
    (c : Config e.α) (R : ℕ → ℕ) (input : ℕ → e.ι)
    (hs : e.ControllerSpec c R input) (t p : ℕ)
    (k : Fin 3) (current previous : e.inner.Q)
    (h : run e.inner.δ e.dead R
        (fun q => e.inner.embed (input q)) t p =
      some (k, current, previous)) :
    e.C.comp ⦋c⦌ t (p : ℤ) = e.inner.project current := by
  rw [e.comp_eq_output c R input hs, h]
  rfl

end Driven
end CellularAutomatas.AsyncHalfLine
