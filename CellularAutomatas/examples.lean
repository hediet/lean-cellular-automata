import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import CellularAutomatas.defs



section myexample
  def char : Alphabet where
    α := Char
    fin := sorry

  abbrev exL: Language Char := fun w => (w.filter (· = 'a')).length % 2 = 0
  def exA := @advice_prefixes_in_L char exL
  #eval! exA.annotate "abaca".toList
end myexample

-- cellular automata that recognizes 1^(2^n) in real-time



def unary : Alphabet := ⟨ Unit ⟩

inductive Exp2State
| Border
| Cell
| Init1
| Init2
| Running (bouncer: Bool) (boundary: Fin 3)
deriving DecidableEq, Repr, Fintype


def exp: @tCellAutomaton 𝒰 := {
  Q := Exp2State,
  δ := fun left center right =>
    sorry,
  border := Exp2State.Border,
  p := fun n => 0,
  t := fun n => n,
  embed := sorry,
  F_pos := sorry,
}





instance i {A: Alphabet} (C: tCellAutomaton) (w: Word) : Decidable (w ∈ C.L) := by
    unfold tCellAutomaton.L
    unfold Membership.mem
    unfold Language.instMembershipList
    simp [Set.Mem]
    infer_instance


-- #eval! ((List.range 12).map (fun i => List.replicate i ())).map (fun w => decide (exp.L w))
