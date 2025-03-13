import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Find


open Set List Nat

structure Indexed (α: Type) where
  val: α
  idx: ℕ

noncomputable def find_some_idxd { α } (f: ℕ → Option α): Option (Indexed α) :=
  let _dec := Classical.dec;
  if h: ∃ n, (f n).isSome = true
  then let idx := Nat.find h; some ⟨ (f idx).get (Nat.find_spec h), idx ⟩
  else none

noncomputable def find_some { α } (f: ℕ → Option α) := Option.map Indexed.val (find_some_idxd f)
noncomputable def find_some_idx { α } (f: ℕ → Option α) := Option.map Indexed.idx (find_some_idxd f)

namespace find_some

protected def find_some_bounded_acc { α } (f: ℕ → Option α) (idx: ℕ): ℕ -> Option (Indexed α)
| 0 => none
| n + 1 =>
  match f idx with
  | some val => some ⟨ val, idx ⟩
  | none => find_some.find_some_bounded_acc f (idx + 1) n

end find_some

def find_some_bounded_idx { α } (f: ℕ → Option α) (k: ℕ) := find_some.find_some_bounded_acc f 0 k

def find_some_bounded { α } (f: ℕ → Option α) := Option.map Indexed.val ∘ find_some_bounded_idx f
