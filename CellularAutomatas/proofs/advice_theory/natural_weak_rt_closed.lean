import CellularAutomatas.proofs.hom
import CellularAutomatas.proofs.ca_rt_utils

/-!
# Uniformity of advice elimination

`Advice.WeakRtClosed` is already *data*: it carries a map `C ↦ map C` eliminating the
advice, not merely a language equality. Every explicit witness in this repository builds
`map C` by a fixed algebraic recipe (product, composition, relabelling, `fix_empty`) that
uses `C` as a black box. The single exception is `Advice.WeakRtClosed.of_language_eq`,
which extracts `map C` by choice from a language equality — and it is used exactly where
the `rt` vs `lt` question hides.

This file asks whether that difference can be captured formally, so that
`open_question_1` splits into

* **Conjecture U** — a *uniform* weakly RT-closed advice is two-stage, and
* `weak_rt_closed → uniform`, which is where the difficulty then lives.

## Main result: the naive definition is vacuous

The obvious attempt is naturality with respect to `CellAutomaton.Hom`: homomorphic inputs
should give homomorphic outputs. `naturality_vacuous` shows this has no content.
A homomorphism forces `C.L = D.L` (`CellAutomaton.Hom.L_eq`), and *any* `map` that depends
on `C` only through the advised language sends such a pair to the **same** automaton,
for which the identity is a homomorphism. `of_language_eq_natural` confirms that the
choice-based witness is natural in this sense.

This is the same trap as a cardinality bound: over a fixed alphabet there are only finitely
many automata with `q` states up to isomorphism, so an isomorphism-invariant `map` always
obeys some state blowup bound. Neither "few states" nor "respects homomorphisms" says
anything, because both are implied by being semantically determined.

## The corrected definition

Content appears only once the condition relates the *state space of the output* to the
*state space of the input*: `Advice.NaturalWeakRtClosed` requires a fixed `StateFunctor F`
with `(map C).Q ≃ F.obj C.Q`, transporting homomorphisms via `F.map`. `of_language_eq`
cannot satisfy this: its output depends on `C.L`, and two automata sharing a state space
`Q` can have different languages, hence different outputs, while `F.obj Q` is fixed.
-/

namespace CellularAutomatas

variable {α Γ : Type} [Alphabet α] [Alphabet Γ] {adv : Advice α Γ}

/-! ## The naive notion and its vacuity -/

/-- Naturality of an advice-elimination construction with respect to CA homomorphisms:
homomorphic machines are sent to homomorphic machines. -/
def Advice.WeakRtClosed.Natural (h : adv.WeakRtClosed) : Prop :=
  ∀ {C D : CA_rt (α × Γ)}, tCellAutomaton.Hom C D →
    Nonempty (tCellAutomaton.Hom (h.map C) (h.map D))

omit [Alphabet α] in
/-- A homomorphism of the advised machines induces equality of the *advised* languages,
because it already forces equality of the underlying languages. -/
lemma advised_L_eq_of_hom {C D : CA_rt (α × Γ)} (f : tCellAutomaton.Hom C D) :
    (C + adv).L = (D + adv).L := by
  ext w
  show C.accepts (adv.annotate w) = true ↔ D.accepts (adv.annotate w) = true
  rw [f.accepts_eq]

/-- **Naturality is vacuous.** Any elimination map that is determined by the advised
language — which every *semantic* witness is — is automatically natural, since a
homomorphism `C ⟶ D` already implies `(C + adv).L = (D + adv).L`. -/
theorem naturality_vacuous (h : adv.WeakRtClosed)
    (hdet : ∀ C D : CA_rt (α × Γ), (C + adv).L = (D + adv).L → h.map C = h.map D) :
    h.Natural := by
  intro C D f
  rw [hdet C D (advised_L_eq_of_hom f)]
  exact ⟨CellAutomaton.Hom.refl _⟩

/-- Choosing a witness only depends on the *predicate*, not on the proof of existence. -/
private lemma indefiniteDescription_val_congr {ι : Type*} {p q : ι → Prop} (hpq : p = q)
    (hp : ∃ x, p x) (hq : ∃ x, q x) :
    (Classical.indefiniteDescription p hp).val = (Classical.indefiniteDescription q hq).val := by
  subst hpq; rfl

/-- The choice-based witness is determined by the advised language. -/
theorem of_language_eq_map_congr (h : ℒ (CA_rt (α × Γ) + adv) = ℒ (CA_rt α))
    (C D : CA_rt (α × Γ)) (hCD : (C + adv).L = (D + adv).L) :
    (Advice.WeakRtClosed.of_language_eq h).map C
      = (Advice.WeakRtClosed.of_language_eq h).map D := by
  show (Classical.indefiniteDescription (fun C' : CA_rt α => C'.L = (C + adv).L) _).val
      = (Classical.indefiniteDescription (fun C' : CA_rt α => C'.L = (D + adv).L) _).val
  exact indefiniteDescription_val_congr (by rw [hCD]) _ _

/-- **The counterexample witness passes the naive test.** `of_language_eq` is the one
construction this theory is meant to exclude, and it is natural. Hence
`Advice.WeakRtClosed.Natural` cannot distinguish uniform from semantic witnesses. -/
theorem of_language_eq_natural (h : ℒ (CA_rt (α × Γ) + adv) = ℒ (CA_rt α)) :
    (Advice.WeakRtClosed.of_language_eq h).Natural :=
  naturality_vacuous _ (of_language_eq_map_congr h)

/-! ## The corrected notion -/

/-- A construction on state spaces together with its action on maps.

No functor laws are imposed: the point is only that `obj` and `map` are fixed *before*
any automaton is seen, so the recipe cannot inspect an automaton's internals. -/
structure StateFunctor where
  /-- The state space of the result, as a function of the state space of the input. -/
  obj : Type → Type
  /-- The action on state maps. -/
  map : ∀ {X Y : Type}, (X → Y) → obj X → obj Y

/-- Weak RT closure witnessed **uniformly in the state space**: the eliminating automaton
is built on top of `C.Q` by a recipe `F` fixed in advance, and homomorphisms are
transported by `F`'s action on maps.

Unlike `Advice.WeakRtClosed.Natural` this is not implied by being semantically determined:
`states` pins `(map C).Q` to `F.obj C.Q`, so two automata with the same state space but
different languages must still yield the same state space. -/
structure Advice.NaturalWeakRtClosed (adv : Advice α Γ) extends adv.WeakRtClosed where
  /-- The fixed recipe for the state space of the eliminating automaton. -/
  F : StateFunctor
  /-- The eliminating automaton is built on top of `C`'s state space. -/
  states : ∀ C : CA_rt (α × Γ), (map C).Q ≃ F.obj C.Q
  /-- Homomorphisms are transported by the recipe's action on maps. -/
  natural : ∀ {C D : CA_rt (α × Γ)} (f : tCellAutomaton.Hom C D),
    ∃ g : tCellAutomaton.Hom (map C) (map D),
      ∀ q, states D (g.onStates q) = F.map f.onStates (states C q)

/-- A uniform witness is in particular a witness. -/
def Advice.NaturalWeakRtClosed.weak_rt_closed (h : adv.NaturalWeakRtClosed) :
    adv.weak_rt_closed := h.toWeakRtClosed

end CellularAutomatas
