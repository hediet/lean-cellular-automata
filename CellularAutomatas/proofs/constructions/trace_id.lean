import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

section id

  def ca_trace_id (α : Type) [Alphabet α] : CellAutomaton α α := {
    Q := α
    δ := fun _ _ r => r
    embed := id
    project := id
  }


  @[simp]
  lemma ca_trace_id_trace_eq {α : Type} [Alphabet α]:
    (ca_trace_id α).trace = config_to_trace := by
    unfold trace
    funext t
    conv in comp _ => change nextt _

    have shift_next c : (ca_trace_id α).next c = fun i => c (i + 1) := by
      funext i
      simp [CellAutomaton.next, ca_trace_id]

    have shift_nextt k c i: ((ca_trace_id α).nextt c k) i = c (i + k) := by
      induction k generalizing c i with
      | zero =>
        simp
      | succ k ih =>
        rw [CellAutomaton.nextt_succ]
        rw [shift_next]
        simp
        rw [ih]
        grind
    funext t
    rw [shift_nextt]
    conv in embed_config => change id
    simp [config_to_trace]



  def ca_trace_id_word (α: Type) [Alphabet α] : CellAutomaton α？ α := (ca_trace_id α？).map_project (·.getD default)

  @[simp]
  lemma ca_trace_id_scan_temporal [Alphabet α]: (ca_trace_id_word α).trace_rt = id := by
    funext w
    rw [id_eq, ca_trace_id_word, trace_rt_of_map_project]
    apply List.ext_getElem (by simp)
    intro i h_i h_len
    unfold trace_rt
    simp [ca_trace_id_trace_eq]
    grind [ca_trace_id_trace_eq, config_to_trace]

end id

end CellularAutomatas
