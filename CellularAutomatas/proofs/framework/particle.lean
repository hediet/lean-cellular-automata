/-
# Particle Framework for Cellular Automata

Particles are point-like entities that move left/right/stay.
The framework provides:
- Declarative particle definitions via `Movable` typeclass
- Automatic CA construction from particle specs
- Reusable particle types (DeadSignal, SlowSignal)
-/

import CellularAutomatas.defs

namespace CellularAutomatas

/-! ## Particle Framework -/

inductive Direction | left | stay | right
  deriving DecidableEq, Repr, Inhabited

class Movable (S : Type) where
  move : S → S × Direction

namespace Movable

def Option.move [Movable S] (o : Option S) : Option (S × Direction) :=
  o.map Movable.move

end Movable

structure ParticleCA (α : Type) (P : Type) [DecidableEq P] [Fintype P] where
  State : P → Type
  [state_dec : ∀ p, DecidableEq (State p)]
  [state_fin : ∀ p, Fintype (State p)]
  [state_inh : ∀ p, Inhabited (State p)]
  embed : α → ((p : P) → Option (State p))
  move : (p : P) → ((p : P) → Option (State p)) → Option (State p × Direction)
  resolve : (p : P) →
            (from_left from_center from_right : (p : P) → Option (State p)) →
            Option (State p)

attribute [instance] ParticleCA.state_dec ParticleCA.state_fin ParticleCA.state_inh

namespace ParticleCA

variable {α P : Type} [DecidableEq P] [Fintype P] (spec : ParticleCA α P)

abbrev CellState := (p : P) → Option (spec.State p)

def δ (left center right : spec.CellState) : spec.CellState := fun p =>
  let from_left : spec.CellState := fun q =>
    match spec.move q left with
    | some (s, .right) => some s
    | _ => none
  let from_center : spec.CellState := fun q =>
    match spec.move q center with
    | some (s, .stay) => some s
    | _ => none
  let from_right : spec.CellState := fun q =>
    match spec.move q right with
    | some (s, .left) => some s
    | _ => none
  spec.resolve p from_left from_center from_right

def toCA [Alphabet spec.CellState] (project : spec.CellState → β) : CellAutomaton α β := {
  Q := spec.CellState
  δ := spec.δ
  embed := spec.embed
  project := project
}

end ParticleCA

/-! ## DeadSignal -/

structure DeadSignal where
  deriving DecidableEq, Repr, Fintype, Inhabited

instance : Movable DeadSignal where
  move := fun s => (s, .stay)

/-! ## SlowSignal -/

structure SlowSignal (n : ℕ) (dir : Direction) where
  phase : Fin n
  deriving DecidableEq, Repr

instance {n : ℕ} {dir : Direction} [NeZero n] : Fintype (SlowSignal n dir) :=
  Fintype.ofEquiv (Fin n) ⟨SlowSignal.mk, SlowSignal.phase, fun _ => rfl, fun _ => rfl⟩

instance {n : ℕ} {dir : Direction} [NeZero n] : Inhabited (SlowSignal n dir) :=
  ⟨⟨0, NeZero.pos n⟩⟩

instance {n : ℕ} {dir : Direction} [NeZero n] : Movable (SlowSignal n dir) where
  move := fun s =>
    if _h : s.phase.val + 1 = n
    then (⟨⟨0, NeZero.pos n⟩⟩, dir)
    else (⟨⟨s.phase.val + 1, by have := s.phase.isLt; omega⟩⟩, .stay)

/-! ## Exponential Time CA -/

inductive ExpParticle | origin | mirror | signal
  deriving DecidableEq, Repr, Fintype

inductive SignalDir | SR | SL
  deriving DecidableEq, Repr, Fintype, Inhabited

@[reducible] def ExpState : ExpParticle → Type
  | .origin => DeadSignal
  | .mirror => SlowSignal 3 .right
  | .signal => SignalDir

instance : DecidableEq (ExpState .origin) := inferInstance
instance : DecidableEq (ExpState .mirror) := inferInstance
instance : DecidableEq (ExpState .signal) := inferInstance

instance : Fintype (ExpState .origin) := inferInstance
instance : Fintype (ExpState .mirror) := inferInstance
instance : Fintype (ExpState .signal) := inferInstance

instance : Inhabited (ExpState .origin) := inferInstance
instance : Inhabited (ExpState .mirror) := inferInstance
instance : Inhabited (ExpState .signal) := inferInstance

instance : Movable (ExpState .origin) := inferInstance
instance : Movable (ExpState .mirror) := inferInstance

abbrev ExpCellState := (p : ExpParticle) → Option (ExpState p)

instance : Inhabited ExpCellState := ⟨fun _ => none⟩

def move_state (p : ExpParticle) [Movable (ExpState p)] (center : ExpCellState) :
    Option (ExpState p × Direction) :=
  (center p).map Movable.move

def expParticleCA : ParticleCA Unit？ ExpParticle where
  State := ExpState
  state_dec := fun | .origin => inferInstance | .mirror => inferInstance | .signal => inferInstance
  state_fin := fun | .origin => inferInstance | .mirror => inferInstance | .signal => inferInstance
  state_inh := fun | .origin => inferInstance | .mirror => inferInstance | .signal => inferInstance

  embed := fun
    | none => fun _ => none
    | some () => fun
      | .origin => some ⟨⟩
      | .mirror => some ⟨⟨0, by omega⟩⟩
      | .signal => some .SR

  move := fun
    | .origin => fun center => (center .origin).map Movable.move
    | .mirror => fun center => (center .mirror).map Movable.move
    | .signal => fun center =>
        (center .signal).map fun state =>
          let mirror_at_M2 := center .mirror == some ⟨⟨1, by omega⟩⟩
          match (state, mirror_at_M2, center .origin) with
            | (.SR, true, _)   => (.SL, .right)
            | (.SL, _, some _) => (.SR, .left)
            | (.SR, _, _)      => (.SR, .right)
            | (.SL, _, _)      => (.SL, .left)

  resolve := fun p from_left from_center from_right =>
      from_left p <|> from_center p <|> from_right p

def exp_core : CellAutomaton Unit？ Bool :=
  expParticleCA.toCA (project := fun cell => (cell .signal).isSome)

end CellularAutomatas
