import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.basic_mark_border

namespace CellularAutomatas

open CellAutomaton

section fix_empty

variable {α: Type} [Alphabet α]


def fix_empty (contains_empty: Bool) (C: CA_rt α): CA_rt α :=
    toRtCa ((C.toCellAutomaton ⨂ c_is_border α).map_project (fun (a, b) => if b then contains_empty else a))

@[simp]
lemma fix_empty_spec (contains_empty: Bool) (C: CA_rt α)  (w: Word α):
    w ∈ (fix_empty contains_empty C).L ↔ if w == [] then contains_empty else w ∈ C.L := by
  rw [CA_rt_L_iff]
  erw [comp_of_map_project]
  rw [ca_zip_comp]
  simp [CA_rt_L_iff]

end fix_empty

end CellularAutomatas
