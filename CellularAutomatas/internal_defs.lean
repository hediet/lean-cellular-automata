import CellularAutomatas.defs

namespace CellularAutomatas

inductive BetaUnionSq (β : Type)
  | single : β → BetaUnionSq β
  | pair : β → β → BetaUnionSq β
  deriving DecidableEq

instance {β : Type} [Inhabited β] : Inhabited (BetaUnionSq β) := ⟨.single default⟩

instance {β : Type} [Fintype β] : Fintype (BetaUnionSq β) :=
  Fintype.ofEquiv (β ⊕ (β × β))
    { toFun := fun
        | .inl q => .single q
        | .inr (q1, q2) => .pair q1 q2
      invFun := fun
        | .single q => .inl q
        | .pair q1 q2 => .inr (q1, q2)
      left_inv := fun x => by rcases x with _ | _ <;> rfl
      right_inv := fun x => by cases x <;> rfl }


notation:max x "³"  => Fin 3 → x

def triple_at {Q} (c: ℕ → Q) (i: ℕ): Q³ := fun o => c (i + o)

end CellularAutomatas
