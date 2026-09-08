import CellularAutomatas.defs

/-!
# Causal simulation and advice elimination

`Advice.WeakRtClosed.Natural` (see `natural_weak_rt_closed.lean`) fails because it is a
*naturality* condition: it relates `map C` to `map D`. Any such condition is vacuous, since
a homomorphism `C ⟶ D` already forces `C.L = D.L`, and every semantically-defined `map`
then returns literally the same automaton on both sides.

A **causal simulation** condition escapes that argument, because it relates `map C` to `C`
itself rather than to `map D`. It is not reflexive and it is not implied by any language
equality, so there is real content to check.

## What "preserves direct causality" should mean

In a radius-1 cellular automaton the state at spacetime point `x` is computed from exactly
the three points `DirectlyCauses · x` one step earlier (`next_eq_of_directlyCauses`). A
simulation preserves direct causality if the simulator's spacetime points carry the
simulated automaton's spacetime points along a *schedule*, in such a way that direct causes
correspond to direct causes.

## Main result: the strict form is impossible

`ExactCausalSimulation` is the strictest version — schedule = identity, so cell `p` at time
`t` of `S` decodes to cell `p` at time `t` of `C`. `ExactCausalSimulation.advice_letterwise`
shows this collapses: at time `0` the decoder must already produce `C.embed (wₚ, adv(w)ₚ)`,
while `S`'s cell `p` at time `0` has seen nothing but `wₚ`. So the advice symbol at `p` is a
function of the letter at `p` alone — a relabelling, which is trivially two-stage. None of
`Advice.middle`, `Advice.compress2` or `Advice.exp` is letterwise.

So, unlike the naturality attempt, the condition is not too weak — it is **too strong**, and
the theorem below locates exactly where slack has to be inserted: the time-`0` row.

## Why the obvious relaxation does not help either

The natural repair is a nonidentity schedule `σ`, e.g. `σ (p, t) = (p, t - p)`, giving `S`'s
cell `p` an extra `p` steps to synthesise `adv(w)ₚ` (at time `p` it has seen `w` up to
position `2p`). But for the real-time schema the acceptance point is `(0, n - 1)`, whose past
cone is *exactly* the input: there is no slack at cell `0`. Anchoring `σ` at the acceptance
point and propagating the causality lifting condition backwards forces `σ` to be a
level-preserving permutation of each past-cone row, hence the identity in time, hence the
situation of the theorem below.

This explains a structural feature of the repository: `two_stage_is_weak_rt_closed` does not
simulate `C` cell-by-cell at all. It converts `C` into a `CArtTransducer` and *composes*
transducers, which reorganises the spacetime layout in a length-dependent way. Any usable
causal condition must therefore allow the schedule to depend on `w.length`, at which point
it is no longer a purely local notion — which is the same difficulty `docs/simulation.md`
runs into from the other side.
-/

namespace CellularAutomatas

variable {α β Γ : Type}

/-! ## Direct causality -/

/-- A point of a spacetime diagram: a cell and a time step. -/
abbrev SpaceTime := ℤ × ℕ

/-- `y` is a **direct cause** of `x`: one step earlier and at most one cell away.
This is precisely the dependency relation induced by a radius-1 local rule. -/
def DirectlyCauses (y x : SpaceTime) : Prop := y.2 + 1 = x.2 ∧ (y.1 - x.1).natAbs ≤ 1

/-- The local rule reads exactly the direct causes: two configurations agreeing on the
direct causes of `(p, 1)` give the same state there. This grounds the name. -/
lemma next_eq_of_directlyCauses (M : CellAutomaton α β) {c c' : Config M.Q} (p : ℤ)
    (h : ∀ q, DirectlyCauses (q, 0) (p, 1) → c q = c' q) : M.next c p = M.next c' p := by
  show M.δ (c (p - 1)) (c p) (c (p + 1)) = M.δ (c' (p - 1)) (c' p) (c' (p + 1))
  rw [h (p - 1) ⟨rfl, by simp⟩, h p ⟨rfl, by simp⟩, h (p + 1) ⟨rfl, by simp⟩]

/-! ## Running an automaton on a word -/

/-- The state of cell `p` of `M` at time `t`, started from the word `w`. -/
def CellAutomaton.stateAt (M : CellAutomaton α？ β) (w : Word α) (t : ℕ) (p : ℤ) : M.Q :=
  M.nextt (embed_config ⟬w⟭) t p

@[simp]
lemma CellAutomaton.stateAt_zero (M : CellAutomaton α？ β) (w : Word α) (p : ℤ) :
    M.stateAt w 0 p = M.embed (⟬w⟭ p) := rfl

/-! ## Exact causal simulation -/

/-- `S` **exactly causally simulates** `C` along `adv`: a single decoder reads, off the state
of cell `p` of `S` at time `t` on input `w`, the state of cell `p` of `C` at time `t` on the
annotated input. The schedule is the identity, so direct causes correspond to direct causes
on the nose.

Note that `decode` may not depend on `w`; that uniformity is the whole point. -/
structure Advice.ExactCausalSimulation (adv : Advice α Γ)
    (S : CellAutomaton α？ β) (C : CellAutomaton (α × Γ)？ β) where
  /-- Reads `C`'s state off `S`'s state. -/
  decode : S.Q → C.Q
  /-- Every cell of every spacetime diagram is simulated. -/
  sound : ∀ (w : Word α) (t : ℕ) (p : ℤ),
    decode (S.stateAt w t p) = C.stateAt (adv.annotate w) t p

namespace Advice.ExactCausalSimulation

variable {adv : Advice α Γ} {S : CellAutomaton α？ β} {C : CellAutomaton (α × Γ)？ β}

/-- **The time-`0` row is the obstruction.** `S`'s initial cell knows only its own letter, so
whatever `C` puts into its initial cell must be a function of that letter alone. -/
theorem embed_annotate_eq (sim : adv.ExactCausalSimulation S C) (w w' : Word α) (p : ℤ)
    (h : ⟬w⟭ p = ⟬w'⟭ p) :
    C.embed (⟬adv.annotate w⟭ p) = C.embed (⟬adv.annotate w'⟭ p) := by
  calc C.embed (⟬adv.annotate w⟭ p)
      = sim.decode (S.embed (⟬w⟭ p)) := (sim.sound w 0 p).symm
    _ = sim.decode (S.embed (⟬w'⟭ p)) := by rw [h]
    _ = C.embed (⟬adv.annotate w'⟭ p) := sim.sound w' 0 p

/-- Reading the annotated word out of its embedded configuration. -/
private lemma annotate_config_apply (adv : Advice α Γ) (w : Word α) {p : ℕ} (hp : p < w.length) :
    ⟬ adv.annotate w⟭ (p : ℤ) = some (w[p], (adv w)[p]'(by simpa using hp)) := by
  have hlen : ((p : ℤ) ≥ 0 ∧ (p : ℤ) < ((adv.annotate w).length : ℤ)) := by
    simp only [Advice.annotate, List.length_zip, adv.len, min_self]
    omega
  rw [word_to_config_apply, dif_pos hlen]
  simp [Advice.annotate, List.getElem_zip]

private lemma config_apply (w : Word α) {p : ℕ} (hp : p < w.length) :
    ⟬ w⟭ (p : ℤ) = some w[p] := by
  have hlen : ((p : ℤ) ≥ 0 ∧ (p : ℤ) < (w.length : ℤ)) := by omega
  rw [word_to_config_apply, dif_pos hlen]
  simp

/-- **An exactly simulable advice is a letterwise relabelling.** The advice symbol at
position `p` depends on nothing but the input letter at position `p`.

Together with `embed_annotate_eq` this says the strict causal condition has no room for any
genuine advice: it is satisfiable only in the trivial case. -/
theorem advice_letterwise (sim : adv.ExactCausalSimulation S C)
    (hinj : Function.Injective C.embed) {w w' : Word α} {p : ℕ}
    (hp : p < w.length) (hp' : p < w'.length) (hw : w[p] = w'[p]) :
    (adv w)[p]'(by simpa using hp) = (adv w')[p]'(by simpa using hp') := by
  have hcfg : ⟬w⟭ (p : ℤ) = ⟬w'⟭ (p : ℤ) := by
    rw [config_apply w hp, config_apply w' hp', hw]
  have := hinj (sim.embed_annotate_eq w w' p hcfg)
  rw [annotate_config_apply adv w hp, annotate_config_apply adv w' hp'] at this
  simpa [hw] using this

end Advice.ExactCausalSimulation

/-! ## The converse: letterwise advices are exactly simulable -/

/-- The letterwise advice `a ↦ g a`. -/
def Advice.letterwise (g : α → Γ) : Advice α Γ := ⟨fun w => w.map g, by simp⟩

/-- `C` with a letterwise annotation folded into its initialisation. Nothing else changes:
the state set and the local rule are literally those of `C`. -/
def relabelCA (g : α → Γ) (C : CellAutomaton (α × Γ)？ β) : CellAutomaton α？ β where
  Q := C.Q
  alphabetQ := C.alphabetQ
  δ := C.δ
  embed o := C.embed (o.map fun a => (a, g a))
  project := C.project

lemma annotate_letterwise (g : α → Γ) (w : Word α) :
    (Advice.letterwise g).annotate w = w.map fun a => (a, g a) := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [Advice.annotate, Advice.letterwise] using ih

lemma word_to_config_letterwise (g : α → Γ) (w : Word α) (p : ℤ) :
    ⟬(Advice.letterwise g).annotate w⟭ p = (⟬w⟭ p).map fun a => (a, g a) := by
  rw [annotate_letterwise, word_to_config_apply, word_to_config_apply]
  by_cases h : p ≥ 0 ∧ p < w.length
  · rw [dif_pos h, dif_pos (by simpa using h)]
    simp
  · rw [dif_neg h, dif_neg (by simpa using h)]
    rfl

/-- **A letterwise advice is exactly causally simulable, uniformly in `C`.** So the
condition is satisfiable, and `Advice.ExactCausalSimulation.advice_letterwise` really
characterises the trivial advices rather than being vacuously unsatisfiable. -/
def letterwise_exactCausalSimulation (g : α → Γ) (C : CellAutomaton (α × Γ)？ β) :
    (Advice.letterwise g).ExactCausalSimulation (relabelCA g C) C where
  decode := _root_.id
  sound w t p := by
    -- `relabelCA g C` has the same states and the same local rule as `C`, so it suffices
    -- to see that the two initial configurations agree.
    show C.nextt (CellAutomaton.embed_config (C := relabelCA g C) ⟬w⟭) t p
        = C.nextt (CellAutomaton.embed_config (C := C) ⟬_⟭) t p
    congr 1
    funext q
    show C.embed ((⟬w⟭ q).map fun a => (a, g a)) = C.embed (⟬_⟭ q)
    rw [word_to_config_letterwise]

end CellularAutomatas
