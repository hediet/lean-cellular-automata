import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import CellularAutomatas.defs
import CellularAutomatas.proofs.scan_lemmas

variable {α: Type u} [Alphabet α]
variable {Γ: Type u} [Alphabet Γ]



inductive ExpState
| Init
| FirstStep
| Empty
| Empty_Pos1
| SignalRight
| SignalLeft
| Wall_S0
| Wall_S1
| Wall_S2
| Wall_S3
| Wall_S4
| Collision
| Collision_Pos1
| Dead
deriving DecidableEq, Repr, Fintype

instance : Inhabited ExpState := ⟨ ExpState.Init ⟩

def exp_ca : tCellAutomaton Unit := {
  Q := ExpState,
  δ := fun left center right =>
    match center with
    | ExpState.Init =>
      match left with
      | ExpState.Dead => ExpState.FirstStep
      | ExpState.FirstStep => ExpState.Collision_Pos1
      | ExpState.Wall_S0 => ExpState.Wall_S1
      | ExpState.Collision => ExpState.Wall_S1
      | ExpState.Collision_Pos1 => ExpState.Wall_S1
      | _ => ExpState.Init
    | ExpState.FirstStep => ExpState.Empty
    | ExpState.Empty =>
      if left == ExpState.SignalRight then ExpState.SignalRight
      else if right == ExpState.SignalLeft || right == ExpState.Collision || right == ExpState.Collision_Pos1 then ExpState.SignalLeft
      else if left == ExpState.Wall_S0 || left == ExpState.Collision then ExpState.Wall_S1
      else ExpState.Empty
    | ExpState.Empty_Pos1 =>
      if left == ExpState.SignalLeft then ExpState.SignalRight
      else if left == ExpState.SignalRight then ExpState.SignalRight
      else if right == ExpState.SignalLeft || right == ExpState.Collision then ExpState.SignalLeft
      else ExpState.Empty_Pos1
    | ExpState.SignalRight => ExpState.Empty
    | ExpState.SignalLeft =>
      if left == ExpState.Dead then ExpState.Empty
      else ExpState.Empty
    | ExpState.Wall_S0 => ExpState.Empty
    | ExpState.Wall_S1 =>
      if left == ExpState.SignalRight then ExpState.Collision
      else ExpState.Wall_S2
    | ExpState.Wall_S2 =>
      if left == ExpState.SignalRight then ExpState.Collision
      else ExpState.Wall_S3
    | ExpState.Wall_S3 =>
      if left == ExpState.SignalRight then ExpState.Collision
      else ExpState.Wall_S4
    | ExpState.Wall_S4 =>
      if left == ExpState.SignalRight then ExpState.Collision
      else ExpState.Wall_S0
    | ExpState.Collision => ExpState.Empty
    | ExpState.Collision_Pos1 => ExpState.Empty_Pos1
    | ExpState.Dead => ExpState.Dead,
  border := ExpState.Dead,
  p := fun n => 0,
  t := fun n => n - 1,
  embed := fun _ => ExpState.Init,
  F_pos := fun q =>
    match q with
    | ExpState.Init => true
    | ExpState.FirstStep => true
    | ExpState.SignalLeft => true
    | _ => false
}


#eval ((List.range 12).map (fun i => List.replicate i ())).map (fun w => decide (exp_ca.L w))
  = [false, true, true, false, true, false, false, false, true, false, false, false]

theorem exp_word_length_rt: ∃ C: CA_rt Unit, C.val.L = { w | ∃ n, w.length = 2 ^ n } := by
  use ⟨ exp_ca, by simp [CA_rt, t_rt, CA, exp_ca, tCellAutomatons] ⟩
  unfold tCellAutomaton.L
  ext w
  simp
  sorry
