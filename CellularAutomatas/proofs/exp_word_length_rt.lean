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


theorem exp_word_length_rt: ∃ C: CA_rt Unit, C.val.L = { w | ∃ n, w.length = 2 ^ n } := by
  sorry
