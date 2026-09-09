import CellularAutomatas.defs

namespace CellularAutomatas.UniformLocal

/-!
The syntax is chosen before the target CA. Only `StateExpr` contains opaque
target states; ordinary values can observe them only through `project`.
-/

mutual
  inductive StateExpr (input output registers context : Type) : Type 1
    | register (index : registers)
    | embed (value : ValueExpr input output registers context input)
    | transition (left center right : StateExpr input output registers context)
    | branch (test : ValueExpr input output registers context Bool)
        (yes no : StateExpr input output registers context)

  inductive ValueExpr (input output registers context : Type) : Type → Type 1
    | read {value : Type} (f : context → value) :
        ValueExpr input output registers context value
    | map {value result : Type} (f : value → result)
        (arg : ValueExpr input output registers context value) :
        ValueExpr input output registers context result
    | pair {left right : Type}
        (a : ValueExpr input output registers context left)
        (b : ValueExpr input output registers context right) :
        ValueExpr input output registers context (left × right)
    | project (state : StateExpr input output registers context) :
        ValueExpr input output registers context output
end

mutual
  def StateExpr.eval {input output registers context : Type}
      (target : CellAutomaton input output) (values : registers → target.Q)
      (environment : context) : StateExpr input output registers context → target.Q
    | .register index => values index
    | .embed value => target.embed (value.eval target values environment)
    | .transition left center right =>
        target.δ (left.eval target values environment) (center.eval target values environment)
          (right.eval target values environment)
    | .branch test yes no =>
        if test.eval target values environment then yes.eval target values environment
        else no.eval target values environment

  def ValueExpr.eval {input output registers context value : Type}
      (target : CellAutomaton input output) (values : registers → target.Q)
      (environment : context) : ValueExpr input output registers context value → value
    | .read f => f environment
    | .map f arg => f (arg.eval target values environment)
    | .pair a b => (a.eval target values environment, b.eval target values environment)
    | .project state => target.project (state.eval target values environment)
end

end CellularAutomatas.UniformLocal
