import CellularAutomatas.proofs.uniform_local.expressions

namespace CellularAutomatas.UniformLocal

/-- A radius-one wrapper with finite control and finitely many opaque target
registers per cell. Initialization cannot read any target-state register. -/
structure LocalRule (source input output : Type) where
  Control : Type
  [controlAlphabet : Alphabet Control]
  registers : ℕ
  initialControl : source → Control
  initialState : Fin registers → StateExpr input output Empty source
  nextControl :
    ValueExpr input output (Fin 3 × Fin registers) (Fin 3 → Control) Control
  nextState : Fin registers →
    StateExpr input output (Fin 3 × Fin registers) (Fin 3 → Control)
  project : ValueExpr input output (Fin registers) Control output

attribute [instance] LocalRule.controlAlphabet

def LocalRule.compile {source input output : Type}
    (rule : LocalRule source input output) (target : CellAutomaton input output) :
    CellAutomaton source output where
  Q := rule.Control × (Fin rule.registers → target.Q)
  embed symbol :=
    (rule.initialControl symbol,
      fun i => (rule.initialState i).eval target Empty.elim symbol)
  δ left center right :=
    let neighbors := fun i : Fin 3 =>
      if i.val = 0 then left else if i.val = 1 then center else right
    let controls := fun i => (neighbors i).1
    let states := fun i => (neighbors i.1).2 i.2
    (rule.nextControl.eval target states controls,
      fun i => (rule.nextState i).eval target states controls)
  project state := rule.project.eval target state.2 state.1

/-- Finite local programs are closed under static instantiation. `compose`
wraps the inner compiled CA; it does not run two sequential time phases or
introduce a nonlocal operation. Each resulting step is still radius one. -/
inductive Program : Type → Type → Type → Type 1
  | target {input output : Type} : Program input input output
  | localRule {source input output : Type}
      (rule : LocalRule source input output) : Program source input output
  | compose {source middle input output : Type}
      (outer : Program source middle output)
      (inner : Program middle input output) : Program source input output

def Program.compile {source input output : Type}
    (program : Program source input output) :
    CellAutomaton input output → CellAutomaton source output :=
  match program with
  | .target => id
  | .localRule rule => rule.compile
  | .compose outer inner => fun target => outer.compile (inner.compile target)

theorem Program.compile_compose {source middle input output : Type}
    (outer : Program source middle output) (inner : Program middle input output) :
    (outer.compose inner).compile = outer.compile ∘ inner.compile := rfl

/-- Input relabeling uses one opaque register and no nontrivial control state. -/
def relabel {source input : Type} (output : Type) (g : source → input) :
    Program source input output :=
  .localRule {
    Control := Unit
    registers := 1
    initialControl := fun _ => ()
    initialState := fun _ => .embed (.read g)
    nextControl := .read (fun _ => ())
    nextState := fun _ => .transition
      (.register (0, 0)) (.register (1, 0)) (.register (2, 0))
    project := .project (.register 0)
  }

def identity (input output : Type) : Program input input output :=
  .target

end UniformLocal

namespace CellAutomaton

/-- A CA transformer has a fixed finite opaque-state local implementation.
This is a syntactic implementation property, not a correctness assertion. -/
def IsUniformlyLocal {source input output : Type}
    (f : CellAutomaton input output → CellAutomaton source output) : Prop :=
  ∃ program : UniformLocal.Program source input output, program.compile = f

theorem IsUniformlyLocal.comp {source middle input output : Type}
    {f : CellAutomaton middle output → CellAutomaton source output}
    {g : CellAutomaton input output → CellAutomaton middle output}
    (hf : IsUniformlyLocal f) (hg : IsUniformlyLocal g) :
    IsUniformlyLocal (f ∘ g) := by
  obtain ⟨outer, rfl⟩ := hf
  obtain ⟨inner, rfl⟩ := hg
  show ∃ program : UniformLocal.Program source input output,
    program.compile = outer.compile ∘ inner.compile
  exact ⟨outer.compose inner, rfl⟩

theorem isUniformlyLocal_compile {source input output : Type}
    (program : UniformLocal.Program source input output) :
    IsUniformlyLocal program.compile :=
  ⟨program, rfl⟩

theorem isUniformlyLocal_id (input output : Type) :
    IsUniformlyLocal (id : CellAutomaton input output → CellAutomaton input output) :=
  ⟨.target, rfl⟩

end CellAutomaton
end CellularAutomatas
