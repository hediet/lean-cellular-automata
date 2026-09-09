import CellularAutomatas.proofs.uniform_local.composition

namespace CellularAutomatas.UniformLocal

open CellAutomaton

example {input output : Type} :
    IsUniformlyLocal (id : CellAutomaton input output → CellAutomaton input output) :=
  isUniformlyLocal_id input output

example {source middle input output : Type}
    (outer : Program source middle output) (inner : Program middle input output) :
    IsUniformlyLocal (outer.compile ∘ inner.compile) :=
  (isUniformlyLocal_compile outer).comp (isUniformlyLocal_compile inner)

theorem identity_simulation (α output : Type) :
    IsUniformRtSimulationOn (⟨id, fun _ => rfl⟩ : Advice α α)
      (fun _ => True) (identity (Option α) output).compile := by
  refine ⟨isUniformlyLocal_compile _, ?_⟩
  intro target w _ _
  rfl

/-- Observing a projected Boolean can select opaque states without inspecting them. -/
example {input : Type} (target : CellAutomaton input Bool)
    (states : Fin 2 → target.Q) :
    (StateExpr.branch (.project (.register 0)) (.register 0) (.register 1) :
      StateExpr input Bool (Fin 2) Unit).eval target states () =
      if target.project (states 0) then states 0 else states 1 := rfl

private def constantFalse : Program (Option Unit) (Option Unit) Bool :=
  .localRule {
    Control := Unit
    registers := 0
    initialControl := fun _ => ()
    initialState := Fin.elim0
    nextControl := .read (fun _ => ())
    nextState := Fin.elim0
    project := .read (fun _ => false)
  }

/-- Local implementability alone says nothing about endpoint correctness. -/
example : IsUniformlyLocal constantFalse.compile :=
  isUniformlyLocal_compile _

example : ¬IsUniformRtSimulationOn (⟨id, fun _ => rfl⟩ : Advice Unit Unit)
    (fun _ => True) constantFalse.compile := by
  intro h
  let target : CellAutomaton (Option Unit) Bool := {
    Q := Unit
    embed := fun _ => ()
    δ := fun _ _ _ => ()
    project := fun _ => true
  }
  have hwrong := h.2 target [()] trivial (by simp)
  change false = true at hwrong
  contradiction

/-- A genuine advice instance, uniform under arbitrary alphabet lifts.
The simulator is obtained solely by changing the target's embedding. -/
theorem letterwise_simulatable {α Γ : Type} [Alphabet α] [Alphabet Γ]
    (g : α → Γ) :
    (⟨fun w => w.map g, by simp⟩ : Advice α Γ).IsUniformlyLocallySimulatable := by
  intro σ _ π output _
  let annotate := fun symbol : σ => (symbol, g (π symbol))
  refine ⟨relabel output (Option.map annotate), ?_⟩
  intro target w _ _
  change ((relabel output (Option.map annotate)).compile target).comp w _ 0 = _
  rw [relabel_word]
  have hword : w.map annotate =
      (((⟨fun w => w.map g, by simp⟩ : Advice α Γ).lift π).retainInput w) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp [Advice.retainInput, Advice.annotate, Advice.lift, annotate]
  rw [hword]
  rfl

example {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (f : α → β) (g : β → γ) :
    ((⟨fun w => w.map f, by simp⟩ : Advice α β).compose
      (⟨fun w => w.map g, by simp⟩ : Advice β γ)).IsUniformlyLocallySimulatable :=
  (letterwise_simulatable f).comp (letterwise_simulatable g)

end CellularAutomatas.UniformLocal
