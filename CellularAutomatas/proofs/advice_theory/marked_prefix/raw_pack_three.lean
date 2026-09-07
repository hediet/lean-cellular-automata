import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compress_to_diag
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.diag
import CellularAutomatas.proofs.constructions.speedup_compressed
import CellularAutomatas.proofs.constructions.trace_id

namespace CellularAutomatas.MarkedPrefix.RawPackThree

open CellAutomaton

variable {α : Type} [Alphabet α]

/-- The left-shifting identity CA, accelerated into packets on the right
diagonal. -/
def dataSource (α : Type) [Alphabet α] : CompressToDiag where
  α := α
  β := Option α
  C_orig := ca_trace_id (Option α)

/-- Emit a raw three-cell input packet exactly when the right-diagonal pulse
arrives. -/
def C (α : Type) [Alphabet α] :
    CellAutomaton (Option α) (Option (Fin 3 → Option α)) :=
  ((dataSource α).C ⨂
      (DiagLeftRight.diag_right : CellAutomaton (Option α) Bool)).map_project
    (fun (packet, pulse) => if pulse then packet else none)

/-- Complete space-time specification, including absence off the right
diagonal. -/
theorem comp_spec (w : Word α) (hw : w ≠ []) (t : ℕ) (p : ℤ) :
    (C α).comp w t p =
      if 0 ≤ p ∧ t = 3 + 2 * p.natAbs then
        some (fun r : Fin 3 =>
          word_to_config w (3 * p + (r.val : ℤ)))
      else none := by
  unfold C
  simp only [comp_of_map_project, ca_zip_comp]
  rw [DiagLeftRight.diag_right_spec w hw]
  simp only [hw, ne_eq, not_false_eq_true, true_and]
  by_cases hpulse : 0 ≤ p ∧ t = 3 + 2 * p.natAbs
  · rw [if_pos hpulse]
    have hp : p ≥ 0 := hpulse.1
    have ht : t = 3 + 2 * p.natAbs := hpulse.2
    simp only [hp, ht, and_self, decide_true, if_true]
    lift p to ℕ using hp
    simp only [Int.natAbs_natCast] at ht ⊢
    have h := (dataSource α).spec w (List.length_pos_of_ne_nil hw) p
    rw [show 3 + 2 * p = 2 * p + 3 by omega]
    rw [h]
    congr 1
    funext r
    simp only [dataSource, triple_at, ca_trace_id_trace_eq, config_to_trace]
    congr 1
  · rw [if_neg hpulse]
    have hsignal :
        decide (0 ≤ p ∧ t = 3 + 2 * p.natAbs) = false := by
      simp [hpulse]
    rw [hsignal]
    rfl

/-- At a natural position, the pulse carries exactly the corresponding raw
three-cell packet. -/
theorem positive_spec (w : Word α) (hw : w ≠ []) (p : ℕ) :
    (C α).comp w (3 + 2 * p) (p : ℤ) =
      some (fun r : Fin 3 =>
        word_to_config w (3 * (p : ℤ) + (r.val : ℤ))) := by
  rw [comp_spec w hw]
  simp

omit [Alphabet α] in
/-- The explicit packet above is precisely the standard spatial compression,
including packets beyond the word's right border. -/
theorem packet_eq_compress (w : Word α) (p : ℕ) :
    (fun r : Fin 3 =>
      word_to_config w (3 * (p : ℤ) + (r.val : ℤ))) =
      SpeedupKx.compress 3 (word_to_config w) (p : ℤ) := by
  funext r
  unfold SpeedupKx.compress
  congr 1
  omega

/-- Positive-position specification stated directly with the standard
compressed configuration. -/
theorem positive_compress_spec (w : Word α) (hw : w ≠ []) (p : ℕ) :
    (C α).comp w (3 + 2 * p) (p : ℤ) =
      some (SpeedupKx.compress 3 (word_to_config w) (p : ℤ)) := by
  rw [positive_spec w hw p, packet_eq_compress]

/-- The initial pulse is exact: at time three it contains input cells
`0,1,2`, with `none` for every index already beyond the word. -/
theorem init_pulse (w : Word α) (hw : w ≠ []) :
    (C α).comp w 3 0 =
      some (fun r : Fin 3 => word_to_config w (r.val : ℤ)) := by
  simpa using positive_spec w hw 0

end CellularAutomatas.MarkedPrefix.RawPackThree
