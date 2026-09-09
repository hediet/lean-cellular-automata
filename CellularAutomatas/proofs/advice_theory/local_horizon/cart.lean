import CellularAutomatas.proofs.advice_theory.local_horizon.producer
import CellularAutomatas.proofs.advice_theory.local_horizon.machine
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_cart

namespace CellularAutomatas.LocalHorizon

open CellAutomaton

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- CART uses the fixed diagonal horizon after the existing geometric
compression. The source also marks the finite trace's genuine border. -/
def cartProducer (C : CArtTransducer α Γ) :
    PacketProducer 3 3 (fun _ => True) C.advice where
  source := ({ C_orig := ({ C_orig := C } : TraceToTraceRtAndBorder).C } :
    CompressToΛ).C
  release := fun _ p => 3 + 2 * p
  width_ge_two := by decide
  startup_pos := by decide
  emits := by
    intro w _ hne t p
    let compressed : CompressToΛ :=
      { C_orig := ({ C_orig := C } : TraceToTraceRtAndBorder).C }
    show compressed.C.comp w t p = _
    rw [compressed.spec w hne]
    simp only [Int.natAbs_natCast]
    congr 1
    unfold CompressToΛ.decode_cfg
    simp only [Int.natCast_nonneg, if_true]
    rw [TraceToTraceRtAndBorder.spec]
    apply congrArg some
    funext i
    show config_to_trace (word_to_config (C.trace_rt w))
        ((3 * (p : ℤ)).natAbs + i) =
      word_to_config (C.trace_rt w) ((p : ℤ) * 3 + (i : ℤ))
    simp only [config_to_trace, Int.natAbs_mul, show (3 : ℤ).natAbs = 3 from rfl,
      Int.natAbs_natCast, Nat.cast_add, Nat.cast_mul]
    congr 1
    ring
  lower := by
    intro w _ _ p
    show 3 + (3 - 1) * p ≤ 3 + 2 * p
    rfl
  deadline := by
    intro w _ _ p hp
    show 3 + 2 * p ≤ 3 + (3 - 1) * packetCount 3 w.length
    omega

theorem cart_readout_eq (C : CArtTransducer α Γ) (w : Word α) :
    readout 3 (cartProducer C).horizon (cartProducer C).data w =
      C.trace_rt w :=
  (cartProducer C).readout_eq w trivial

theorem cart_horizon_admissible (C : CArtTransducer α Γ) :
    RTAdmissibleHorizon 3 3 (cartProducer C).horizon :=
  (cartProducer C).admissible (by decide)

theorem cart_isGlobalPacketReadout (C : CArtTransducer α Γ) :
    C.advice.IsGlobalPacketReadout := by
  refine ⟨PacketReadoutMachine.ofProducer (cartProducer C),
    PacketReadoutMachine.contractOfProducer (cartProducer C) (by decide), ?_⟩
  intro w hw
  exact PacketReadoutMachine.producer_readout_eq (cartProducer C) (by decide) w hw

/-- CART's full composition law follows from the generic final readout
theorem plus causality; it does not need a second simulation proof. -/
theorem cart_composition {β : Type} [Alphabet β]
    (C : CArtTransducer α Γ) (target : CellAutomaton (Option Γ) β) :
    ((cartProducer C).consumer target).trace_rt = target.trace_rt ∘ C.trace_rt :=
  (cartProducer C).trace_rt_eq target C.trace_rt_is_causal

end CellularAutomatas.LocalHorizon
