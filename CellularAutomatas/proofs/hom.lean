import CellularAutomatas.defs

/-!
# Homomorphisms of cellular automata

A homomorphism `C ⟶ D` is a map on state sets commuting with the local transition
function, the initialisation and the output projection. Its point is not to compare
automata — a homomorphism forces them to have the *same* language — but to express
that a construction treats an automaton as a **black box**.

A construction `F : CellAutomaton α β → CellAutomaton α' β'` that maps homomorphic
inputs to homomorphic outputs cannot inspect the internal structure of `Q`; it may
only call `δ`, `embed` and `project`. This is the uniformity axis needed to state
`Advice.NaturalWeakRtClosed`: every explicit witness of weak RT closure in this
repository builds the eliminating automaton by a fixed product/composition applied
to `C` as a black box, whereas `Advice.WeakRtClosed.of_language_eq` extracts it by
choice from a language equality and has no reason to be natural.

Cardinality bounds cannot substitute for naturality: over a fixed alphabet there are
only finitely many automata with a given number of states up to isomorphism, so any
isomorphism-invariant `map` automatically obeys some state blowup bound.

## Main results

* `CellAutomaton.Hom.comp_eq` — a homomorphism preserves the whole spacetime diagram.
* `CellAutomaton.Hom.trace_eq`, `CellAutomaton.Hom.trace_rt_eq` — hence all traces.
* `CellAutomaton.Hom.accepts_eq`, `CellAutomaton.Hom.L_eq` — hence the language.
-/

namespace CellularAutomatas

variable {α β : Type}

/-- A homomorphism of cellular automata over the same input and output alphabets. -/
structure CellAutomaton.Hom (C D : CellAutomaton α β) where
  /-- The underlying map on state sets. -/
  onStates : C.Q → D.Q
  /-- It commutes with the local transition function. -/
  map_δ : ∀ l m r, onStates (C.δ l m r) = D.δ (onStates l) (onStates m) (onStates r)
  /-- It respects the initialisation. -/
  map_embed : ∀ a, onStates (C.embed a) = D.embed a
  /-- It preserves the output projection. -/
  map_project : ∀ q, D.project (onStates q) = C.project q

namespace CellAutomaton.Hom

variable {C D E : CellAutomaton α β}

/-! ## Category structure -/

/-- The identity homomorphism. -/
def refl (C : CellAutomaton α β) : C.Hom C where
  onStates := _root_.id
  map_δ _ _ _ := rfl
  map_embed _ := rfl
  map_project _ := rfl

/-- Homomorphisms compose. -/
def trans (f : C.Hom D) (g : D.Hom E) : C.Hom E where
  onStates := g.onStates ∘ f.onStates
  map_δ l m r := by
    show g.onStates (f.onStates (C.δ l m r)) = _
    rw [f.map_δ, g.map_δ]
    rfl
  map_embed a := by
    show g.onStates (f.onStates (C.embed a)) = _
    rw [f.map_embed, g.map_embed]
  map_project q := by
    show E.project (g.onStates (f.onStates q)) = C.project q
    rw [g.map_project, f.map_project]

/-! ## Transport of configurations -/

/-- A homomorphism transports configurations. -/
def onConfig (f : C.Hom D) (c : Config C.Q) : Config D.Q := fun p => f.onStates (c p)

/-- Transport commutes with one global step. -/
lemma onConfig_next (f : C.Hom D) (c : Config C.Q) :
    f.onConfig (C.next c) = D.next (f.onConfig c) := by
  funext p
  show f.onStates (C.δ (c (p - 1)) (c p) (c (p + 1)))
      = D.δ (f.onStates (c (p - 1))) (f.onStates (c p)) (f.onStates (c (p + 1)))
  exact f.map_δ _ _ _

/-- Transport commutes with iterated steps. -/
lemma onConfig_nextt (f : C.Hom D) (c : Config C.Q) (t : ℕ) :
    f.onConfig (C.nextt c t) = D.nextt (f.onConfig c) t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ, f.onConfig_next, ih]

/-- Transport of an initial configuration is the initial configuration. -/
lemma onConfig_embed (f : C.Hom D) (c : Config α) :
    f.onConfig (@CellAutomaton.embed_config α β C c)
      = @CellAutomaton.embed_config α β D c := by
  funext p
  show f.onStates (C.embed (c p)) = D.embed (c p)
  exact f.map_embed _

/-! ## Preservation of the observable behaviour -/

/-- **A homomorphism preserves the entire projected spacetime diagram.** Both automata,
started from the same input configuration, show the same output at every cell and time. -/
theorem comp_eq (f : C.Hom D) (c : Config α) (t : ℕ) :
    D.comp (@CellAutomaton.embed_config α β D c) t
      = C.comp (@CellAutomaton.embed_config α β C c) t := by
  funext p
  show D.project (D.nextt _ t p) = C.project (C.nextt _ t p)
  rw [← f.onConfig_embed c, ← f.onConfig_nextt]
  exact f.map_project _

/-- Homomorphic automata have the same cell-0 trace. -/
theorem trace_eq (f : C.Hom D) (c : Config α) : D.trace c = C.trace c := by
  funext t
  exact congrFun (f.comp_eq c t) 0

/-- Homomorphic automata have the same real-time trace word. -/
theorem trace_rt_eq {C D : CellAutomaton α？ β} (f : C.Hom D) (w : Word α) :
    D.trace_rt w = C.trace_rt w := by
  show (List.range w.length).map (D.trace ⟬w⟭) = (List.range w.length).map (C.trace ⟬w⟭)
  rw [f.trace_eq ⟬w⟭]

/-- Homomorphic automata accept the same words, for every acceptance schema. -/
theorem accepts_eq {schema : AcceptanceSchema} {C D : tCellAutomaton schema α}
    (f : C.toCellAutomaton.Hom D.toCellAutomaton) (w : Word α) :
    D.accepts w = C.accepts w :=
  congrFun (f.comp_eq ⟬w⟭ (schema.t w.length)) (schema.p w.length)

/-- Homomorphic automata recognize the same language. -/
theorem L_eq [Alphabet α] {schema : AcceptanceSchema} {C D : tCellAutomaton schema α}
    (f : C.toCellAutomaton.Hom D.toCellAutomaton) : D.L = C.L := by
  ext w
  show D.accepts w = true ↔ C.accepts w = true
  rw [f.accepts_eq]

end CellAutomaton.Hom

/-- A homomorphism of automata carrying an acceptance schema. -/
abbrev tCellAutomaton.Hom {schema : AcceptanceSchema} (C D : tCellAutomaton schema α) :=
  C.toCellAutomaton.Hom D.toCellAutomaton

end CellularAutomatas
