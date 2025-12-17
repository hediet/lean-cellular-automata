import CellularAutomatas.defs

namespace CellularAutomatas
@[simp]
lemma apply_iterated_zero {α: Type u} {m: α} {f: α -> α}: apply_iterated f m 0 = m := by
  simp [apply_iterated]

lemma apply_iterated_succ_apply' {α: Type u} {m: α} {f: α -> α}: apply_iterated f m (n+1) = f (apply_iterated f m n) := by
  simp [apply_iterated, Function.iterate_succ_apply']
