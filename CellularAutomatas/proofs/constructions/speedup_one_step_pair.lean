import CellularAutomatas.proofs.constructions.speedup_k_step

namespace CellularAutomatas
namespace OneStepSpeedupPair

variable {α β : Type}

/-- Represent two consecutive states by the state/function representation used by `Sp`. -/
def phi (C : CellAutomaton (Option α) β) (pair : C.Q × C.Q) : (Sp C).Q :=
  (pair.1, fun left => C.δ left pair.1 pair.2)

/-- The one-step speedup whose states are just pairs of states of the original machine. -/
def C (target : CellAutomaton (Option α) β) : CellAutomaton (Option α) β where
  Q := target.Q × target.Q
  δ := fun left center right =>
    (target.δ left.1 center.1 right.1, target.δ center.1 right.1 right.2)
  embed := fun symbol => (target.embed symbol, target.border)
  project := fun pair => target.project (target.δ target.border pair.1 pair.2)

lemma phi_embed (target : CellAutomaton (Option α) β) (symbol : Option α) :
    phi target ((C target).embed symbol) = (SpB target).embed symbol := by
  rfl

lemma phi_transition (target : CellAutomaton (Option α) β)
    (left center right : (C target).Q) :
    phi target ((C target).δ left center right) =
      (SpB target).δ (phi target left) (phi target center) (phi target right) := by
  rfl

lemma phi_project (target : CellAutomaton (Option α) β) (pair : (C target).Q) :
    (C target).project pair = (SpB target).project (phi target pair) := by
  rfl

/-- Applying `phi` pointwise commutes with one global transition. -/
lemma representation_next (target : CellAutomaton (Option α) β)
    (config : Config (C target).Q) :
    (fun position => phi target ((C target).next config position)) =
      (SpB target).next (fun position => phi target (config position)) := by
  funext position
  show
    phi target
        ((C target).δ (config (position - 1)) (config position) (config (position + 1))) =
      (SpB target).δ
        (phi target (config (position - 1)))
        (phi target (config position))
        (phi target (config (position + 1)))
  exact phi_transition target _ _ _

/-- The representation is preserved at every time and position, for any initial configuration. -/
theorem representation_invariant (target : CellAutomaton (Option α) β)
    (config : Config (C target).Q) (time : ℕ) (position : ℤ) :
    phi target ((C target).nextt config time position) =
      (SpB target).nextt (fun p => phi target (config p)) time position := by
  induction time generalizing position with
  | zero =>
      show phi target (config position) = phi target (config position)
      rfl
  | succ time ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      calc
        phi target ((C target).next ((C target).nextt config time) position) =
            (SpB target).next
              (fun p => phi target ((C target).nextt config time p)) position := by
              exact congrFun (representation_next target _) position
        _ = (SpB target).next
              ((SpB target).nextt (fun p => phi target (config p)) time) position := by
              congr 1
              funext p
              exact ih p

/-- Embedded input configurations agree under the representation. -/
lemma representation_initial (target : CellAutomaton (Option α) β)
    (input : Config (Option α)) :
    (fun position => phi target ((C target).embed_config input position)) =
      (SpB target).embed_config input := by
  funext position
  show phi target ((C target).embed (input position)) = (SpB target).embed (input position)
  exact phi_embed target _

/-- The pair machine is behaviorally equivalent to the existing `SpB` construction. -/
theorem trace_eq_spb (target : CellAutomaton (Option α) β)
    (word : Word α) (time : ℕ) :
    (C target).trace word time = (SpB target).trace word time := by
  unfold CellAutomaton.trace CellAutomaton.comp
  simp only [Function.comp_apply, CellAutomaton.project_config_apply]
  calc
    (C target).project ((C target).nextt ((C target).embed_config word) time 0) =
        (SpB target).project
          (phi target ((C target).nextt ((C target).embed_config word) time 0)) := by
          exact phi_project target _
    _ = (SpB target).project
          ((SpB target).nextt
            (fun p => phi target ((C target).embed_config word p)) time 0) := by
          rw [representation_invariant]
    _ = (SpB target).project
          ((SpB target).nextt ((SpB target).embed_config word) time 0) := by
          rw [representation_initial]

/-- Under the same hypotheses as `SpB_trace_eq`, the pair machine saves one step. -/
theorem trace_eq (target : CellAutomaton (Option α) β)
    (hleft : target.left_dead target.border) (word : Word α) (time : ℕ)
    (hready : time + 1 ≥ word.length) :
    (C target).trace word time = target.trace word (time + 1) := by
  calc
    (C target).trace word time = (SpB target).trace word time :=
      trace_eq_spb target word time
    _ = target.trace word (time + 1) :=
      SpB_trace_eq hleft word time hready

end OneStepSpeedupPair
end CellularAutomatas
