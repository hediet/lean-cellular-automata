import CellularAutomatas.defs

namespace CellularAutomatas

section FSSP

def fssp_left_side (n : ℕ) : Word Bool := [true] ++ List.replicate (n - 1) false

structure SolvesFSSP (C : CellAutomaton Bool？ Bool)
    (input : ℕ → Word Bool) (time : ℕ → ℕ) : Prop where
  quiescent_set : C.quiescent_set { C.border, C.inner false }
  fire_iff : ∀ n : ℕ, n ≥ 1 →
    let w := input n
    ∀ t : ℕ, t ≤ time n →
      ∀ p : ℤ, 0 ≤ p ∧ p < w.length →
        C.comp ⟬w⟭ t p = true ↔ t = time n

def SolvesFSSPOptimal (C : CellAutomaton Bool？ Bool) := SolvesFSSP C fssp_left_side (fun n => 2 * n - 2)

def fssp_both_sides (n : ℕ) : Word Bool :=
  if n = 0 then []
  else if n = 1 then [true]
  else [true] ++ List.replicate (n - 2) false ++ [true]

def SolvesTwoSidedFSSPOptimal (C : CellAutomaton Bool？ Bool) := SolvesFSSP C fssp_both_sides (fun n => n - 1)


theorem SolvesFSSPOptimal_exists:
  ∃ C : CellAutomaton Bool？ Bool, SolvesFSSPOptimal C := by
  sorry


theorem SolvesTwoSidedFSSPOptimal_of_SolvesFSSPOptimal (C : CellAutomaton Bool？ Bool) (h : SolvesFSSPOptimal C):
    ∃ C': CellAutomaton Bool？ Bool, SolvesTwoSidedFSSPOptimal C' := by
  sorry


end FSSP

end CellularAutomatas
