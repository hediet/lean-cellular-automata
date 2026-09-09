import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.async_full_line

namespace CellularAutomatas.AsyncFullLine.Driven

open CellAutomaton
open AsyncHalfLine (State tag encode)

variable {α β ι : Type} (target : CellAutomaton α β)
    (source : CellAutomaton ι (Option target.Q))

/-- A finite CA product. The newly computed source output is consumed in the
same transition, so an initialization at source time `t` is visible at time `t`.
Neither absolute positions nor release times occur in the local rule. -/
def C : CellAutomaton ι (State target.Q) where
  Q := source.Q × State target.Q
  δ := fun left center right =>
    let producer := source.δ left.1 center.1 right.1
    (producer, step target.δ (source.project producer) left.2 center.2 right.2)
  embed := fun a =>
    let producer := source.embed a
    (producer, (source.project producer).map (fun q => (0, q, q)))
  project := Prod.snd

/-- At each integer position the source emits the initial target state exactly
once, at its arbitrary release time; this includes releases at time zero. -/
def SourceSpec (input : Config ι) (R : ℤ → ℕ)
    (initial : Config target.Q) : Prop :=
  ∀ (t : ℕ) (p : ℤ), source.comp ⦋input⦌ t p = packet R initial t p

lemma source_track (input : Config ι) (t : ℕ) (p : ℤ) :
    ((C target source).nextt ⦋input⦌ t p).1 = source.nextt ⦋input⦌ t p := by
  induction t generalizing p with
  | zero =>
    show source.embed (input p) = source.embed (input p)
    rfl
  | succ t ih =>
    show ((C target source).nextt ⦋input⦌ (t + 1) p).1 = _
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    change source.δ
      (((C target source).nextt ⦋input⦌ t (p - 1)).1)
      (((C target source).nextt ⦋input⦌ t p).1)
      (((C target source).nextt ⦋input⦌ t (p + 1)).1) = _
    rw [ih (p - 1), ih p, ih (p + 1)]

lemma data_step (input : Config ι) (t : ℕ) (p : ℤ) :
    ((C target source).nextt ⦋input⦌ (t + 1) p).2 =
      step target.δ (source.comp ⦋input⦌ (t + 1) p)
        (((C target source).nextt ⦋input⦌ t (p - 1)).2)
        (((C target source).nextt ⦋input⦌ t p).2)
        (((C target source).nextt ⦋input⦌ t (p + 1)).2) := by
  rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
  change step target.δ
    (source.project (source.δ
      (((C target source).nextt ⦋input⦌ t (p - 1)).1)
      (((C target source).nextt ⦋input⦌ t p).1)
      (((C target source).nextt ⦋input⦌ t (p + 1)).1))) _ _ _ = _
  rw [source_track target source input t (p - 1),
    source_track target source input t p,
    source_track target source input t (p + 1)]
  simp only [CellAutomaton.comp_apply,
    CellAutomaton.nextt_succ, CellAutomaton.next_apply]

lemma data_track (input : Config ι) (R : ℤ → ℕ)
    (initial : Config target.Q) (hs : SourceSpec target source input R initial)
    (t : ℕ) (p : ℤ) :
    ((C target source).nextt ⦋input⦌ t p).2 = run target.δ R initial t p := by
  induction t generalizing p with
  | zero =>
    show (source.project (source.embed (input p))).map (fun q => (0, q, q)) = _
    have hp := hs 0 p
    change source.project (source.embed (input p)) = _ at hp
    rw [hp]
    rfl
  | succ t ih =>
    show ((C target source).nextt ⦋input⦌ (t + 1) p).2 = _
    rw [data_step, hs, ih, ih, ih]
    rfl

/-- The actual finite CA output is the full-line synchronous target state,
encoded at the asynchronous height, for every time and every integer position. -/
theorem comp_encode (input : Config ι) (R : ℤ → ℕ)
    (initial : Config target.Q) (hs : SourceSpec target source input R initial)
    (t : ℕ) (p : ℤ) :
    (C target source).comp ⦋input⦌ t p =
      encode (height R t p) (fun k => target.nextt initial k p) := by
  change ((C target source).nextt ⦋input⦌ t p).2 = _
  calc
    ((C target source).nextt ⦋input⦌ t p).2 = run target.δ R initial t p :=
      data_track target source input R initial hs t p
    _ = encode (height R t p) (fun k => target.nextt initial k p) :=
      run_encode target R initial t p

/-- Expose the target output while distinguishing uninitialized ghost cells. -/
def readout : State target.Q → Option β
  | none => none
  | some (_, current, _) => some (target.project current)

lemma readout_encode (g : ℕ) (states : ℕ → target.Q) :
    readout target (encode g states) =
      if g = 0 then none else some (target.project (states (g - 1))) := by
  by_cases hg : g = 0
  · show readout target (encode g states) = _
    simp [encode, readout, hg]
  · show readout target (encode g states) = _
    simp [encode, readout, hg]

/-- Readout changes only the projection, not the finite simulation or its timing. -/
def projected : CellAutomaton ι (Option β) :=
  (C target source).map_project (readout target)

theorem projected_comp_encode (input : Config ι) (R : ℤ → ℕ)
    (initial : Config target.Q) (hs : SourceSpec target source input R initial)
    (t : ℕ) (p : ℤ) :
    (projected target source).comp ⦋input⦌ t p =
      if height R t p = 0 then none
      else some (target.project (target.nextt initial (height R t p - 1) p)) := by
  change readout target ((C target source).comp ⦋input⦌ t p) = _
  calc
    readout target ((C target source).comp ⦋input⦌ t p) =
        readout target (encode (height R t p) (fun k => target.nextt initial k p)) := by
      rw [comp_encode target source input R initial hs]
    _ = if height R t p = 0 then none
        else some (target.project (target.nextt initial (height R t p - 1) p)) :=
      readout_encode target _ _

theorem projected_comp_at_height (input : Config ι) (R : ℤ → ℕ)
    (initial : Config target.Q) (hs : SourceSpec target source input R initial)
    (t g : ℕ) (p : ℤ) (hg : height R t p = g) :
    (projected target source).comp ⦋input⦌ t p =
      if g = 0 then none
      else some (target.project (target.nextt initial (g - 1) p)) := by
  rw [projected_comp_encode target source input R initial hs, hg]

theorem comp_at_generation (input : Config ι) (R : ℤ → ℕ)
    (initial : Config target.Q) (hs : SourceSpec target source input R initial)
    (t k : ℕ) (p : ℤ) (h : height R t p = k + 1) :
    (C target source).comp ⦋input⦌ t p =
      some (tag k, target.nextt initial k p, target.nextt initial (k - 1) p) := by
  change ((C target source).nextt ⦋input⦌ t p).2 = _
  rw [data_track target source input R initial hs]
  exact run_at_generation target R initial t k p h

theorem comp_at_release (input : Config ι) (R : ℤ → ℕ)
    (initial : Config target.Q) (hs : SourceSpec target source input R initial)
    (p : ℤ) :
    (C target source).comp ⦋input⦌ (R p) p = some (0, initial p, initial p) := by
  have h := comp_at_generation target source input R initial hs (R p) 0 p
    (height_at_release R p)
  simpa only [tag, Nat.zero_mod, Nat.zero_sub, CellAutomaton.nextt_zero] using h

theorem comp_eventually_generation (input : Config ι) (R : ℤ → ℕ)
    (initial : Config target.Q) (hs : SourceSpec target source input R initial)
    (p : ℤ) (k : ℕ) :
    ∃ t : ℕ, (C target source).comp ⦋input⦌ t p =
      some (tag k, target.nextt initial k p, target.nextt initial (k - 1) p) := by
  obtain ⟨t, ht⟩ := height_hits R p k
  exact ⟨t, comp_at_generation target source input R initial hs t k p ht⟩

/-- A source emitting target input symbols can be adapted without any latency. -/
def stateSource (producer : CellAutomaton ι (Option α)) :
    CellAutomaton ι (Option target.Q) :=
  producer.map_project (Option.map target.embed)

lemma stateSource_spec (producer : CellAutomaton ι (Option α))
    (input : Config ι) (R : ℤ → ℕ) (initial : Config α)
    (hs : ∀ (t : ℕ) (p : ℤ),
      producer.comp ⦋input⦌ t p = packet R initial t p) :
    SourceSpec target (stateSource target producer) input R
      (fun p => target.embed (initial p)) := by
  intro t p
  change (producer.comp ⦋input⦌ t p).map target.embed = _
  rw [hs]
  unfold packet
  split <;> rfl

end CellularAutomatas.AsyncFullLine.Driven
