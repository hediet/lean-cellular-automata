import CellularAutomatas.defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Linarith
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.speedup_k_step
import CellularAutomatas.proofs.constructions.speedup_compressed
import CellularAutomatas.proofs.constructions.trace_kx
import CellularAutomatas.proofs.constructions.composition.sim_from_lambda
import CellularAutomatas.proofs.constructions.composition.decompress_triple
import CellularAutomatas.proofs.constructions.composition.compress_to_diag
import CellularAutomatas.proofs.constructions.composition.diag

namespace CellularAutomatas

open CellAutomaton

structure CompressToΛ where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α？ β？

attribute [instance] CompressToΛ._inst_α
attribute [instance] CompressToΛ._inst_β

namespace CompressToΛ
  variable (e: CompressToΛ)

  def data_source : CompressToDiag := {
    α := e.α
    β := e.β？
    C_orig := e.C_orig
  }

  -- diag_right fires (true) at p >= 0 at correct diagonal time
  -- diag_left fires (true) at p < 0 at correct diagonal time
  -- data_source.C provides the actual triple values (but always outputs some)
  def C: CellAutomaton e.α？ ((e.β？)³)？ :=
    (e.data_source.C ⨂ (DiagLeftRight.diag_right : CellAutomaton e.α？ Bool) ⨂ (DiagLeftRight.diag_left : CellAutomaton e.α？ Bool)).map_project
      (fun (triple, (signal_right, signal_left)) =>
        if signal_right then triple              -- p >= 0 on diagonal: use computed triple
        else if signal_left then some (fun _ => none)  -- p < 0 on diagonal: placeholder
        else none)                                -- not on diagonal


  def decode_cfg (w: Word e.α): Config ((e.β？)³) :=
    fun p =>
      if p ≥ 0
      then triple_at (e.C_orig.trace w) (3 * p).natAbs
      else (fun _ => none)

  @[simp]
  lemma map_project_comp2 {α β γ: Type} (C: CellAutomaton α？ β) (f: β → γ) (w: Word α) (t: ℕ):
    (C.map_project f).comp w t p = f (C.comp w t p) := by rfl


  theorem spec (w: Word e.α) (hw: w ≠ []) (t: ℕ) (p: ℤ):
      e.C.comp w t p =
        if t = 3 + 2 * p.natAbs
        then some (e.decode_cfg w p)
        else none
        := by
    -- Step 1: Unfold C and use composition lemmas
    unfold C
    simp only [map_project_comp2, ca_zip_comp]

    -- Step 2: Get the specs for diag signals
    rw [DiagLeftRight.diag_right_spec w hw, DiagLeftRight.diag_left_spec2 w hw]
    simp only [hw, ne_eq, not_false_eq_true, true_and]

    -- Step 3: Case split on diagonal timing
    by_cases ht : t = 3 + 2 * p.natAbs
    case pos =>
      -- On diagonal
      simp only [ht, and_true, decide_eq_true_eq]
      by_cases hp : p ≥ 0
      case pos =>
        -- p ≥ 0: diag_right fires, use data_source.C output
        simp only [hp, ↓reduceIte]
        -- Need: data_source.C.comp w t p = some (decode_cfg w p)
        unfold decode_cfg
        simp only [hp, ↓reduceIte]
        -- data_source.C.comp gives triple_at via CompressToDiag.spec
        have hw' : w.length > 0 := List.length_pos_of_ne_nil hw
        -- Convert p to ℕ since p ≥ 0
        lift p to ℕ using hp
        simp only [Int.natAbs_natCast] at ht ⊢
        have h := e.data_source.spec w hw' p
        simp only [mul_comm 2 p] at h ⊢
        convert h using 1
        ring_nf
      case neg =>
        -- p < 0: diag_left fires, diag_right doesn't
        push_neg at hp
        have hp' : p ≤ 0 := le_of_lt hp
        simp only [hp', ↓reduceIte]
        -- Output is some (fun _ => none) which matches decode_cfg for p < 0
        unfold decode_cfg
        simp only [show ¬(p ≥ 0) by linarith, ↓reduceIte]
    case neg =>
      -- Off diagonal: both diag signals are false
      simp only [ht, and_false, decide_false]
      rfl

end CompressToΛ

structure TraceToTraceRtAndBorder where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α？ β

attribute [instance] TraceToTraceRtAndBorder._inst_α
attribute [instance] TraceToTraceRtAndBorder._inst_β

namespace TraceToTraceRtAndBorder
  variable (e: TraceToTraceRtAndBorder)

  def b := e.C_orig.embed none

  def C_mark_border: CellAutomaton e.α？ Bool := {
    Q := Bool
    δ := fun _a _b c => c
    embed := fun
      | some _a => false
      | none => true
    project := id
  }

  theorem spec_mark_border (w: Word e.α) (t: ℕ) (p: ℤ):
      e.C_mark_border.comp w t p = (p + t < 0 || p + t ≥ w.length) := by
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply]
    have next_val : ∀ (c: Config e.C_mark_border.Q) (p: ℤ), e.C_mark_border.next c p = c (p+1) := by
      intro c p
      unfold CellAutomaton.next
      simp [C_mark_border]
    have h_nextt: ∀ t p, e.C_mark_border.nextt w t p = (embed_config (word_to_config w)) (p + t) := by
      intro t
      induction t with
      | zero =>
        intro p
        simp
      | succ t ih =>
        intro p
        rw [CellAutomaton.nextt_succ]
        rw [next_val]
        rw [ih]
        apply congrArg
        grind
    rw [h_nextt]
    dsimp [word_to_config, CellAutomaton.embed_config]
    dsimp [C_mark_border]
    split_ifs with h
    · simp_all
    · simp
      rcases lt_or_ge (p+t) 0 with h_neg | h_pos
      · left; exact h_neg
      · right; simp_all

  @[simp]
  theorem spec_mark_border2 (w: Word e.α) (t: ℕ):
      e.C_mark_border.trace w t = (t < 0 || t ≥ w.length) := by
    unfold trace
    rw [spec_mark_border]
    simp

  def C := (e.C_orig ⨂ e.C_mark_border).map_project (fun (v1, v2) =>
    if v2 then none else (some v1)
  )

  theorem spec (w: Word e.α): e.C.trace w = config_to_trace (e.C_orig.trace_rt w) := by
    funext t
    unfold C
    unfold config_to_trace
    unfold trace_rt
    simp [word_to_config]
    grind

end TraceToTraceRtAndBorder



structure Composition where
  {α: Type}
  {β: Type}
  {γ: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [_inst_γ: Alphabet γ]
  C2: CellAutomaton β？ γ
  C1: CellAutomaton α？ β

attribute [instance] Composition._inst_α
attribute [instance] Composition._inst_β
attribute [instance] Composition._inst_γ


namespace Composition
  variable (e: Composition)

  def C1': TraceToTraceRtAndBorder := { C_orig := e.C1 }
  example : (CellAutomaton e.α？ e.β？) := e.C1'.C

  abbrev C1_Λ: CompressToΛ := {
    α := e.α
    β := e.β
    C_orig := e.C1'.C
  }
  example : (CellAutomaton e.α？ e.β？³？) := e.C1_Λ.C

  abbrev C2_3x: SpeedupAndTraceKx := {
    k := 3
    α := e.β？
    β := e.γ
    C_orig := e.C2
  }
  example : (CellAutomaton e.β？³ e.γ³) := e.C2_3x.C

  abbrev C_sim: SimFromΛ := {
    α := e.α？
    β := e.β？³
    γ := e.γ³
    C_ctl := e.C1_Λ.C
    C_inr := e.C2_3x.C
  }
  example : (CellAutomaton e.α？ e.γ³？) := e.C_sim.C

  abbrev C_decomp: DecompressTriple := {
    C_orig := e.C_sim.C
  }
  example : (CellAutomaton e.α？ e.γ) := e.C_decomp.C

  abbrev C_exact: SpeedupKSteps := {
    C_orig := e.C_decomp.C
    k := 6
    c := 7
  }

  def C : (CellAutomaton e.α？ e.γ) := e.C_exact.C


  theorem spec: e.C.trace_rt = e.C2.trace_rt ∘ e.C1.trace_rt := by
    rw [IsCausal.eq_iff _ _ (by simp) (by simp)]

    intro w

    by_cases hw: w = []
    case pos => simp [hw]

    let c_inr: Config e.β？³ := SpeedupKx.compress 3 (word_to_config (e.C1.trace_rt w))
    have x: e.C_sim.c_ctl_computes_c_inr ⟬w⟭ c_inr := by
      unfold SimFromΛ.c_ctl_computes_c_inr
      intro t p
      simp
      rw [CompressToΛ.spec _ _ hw]
      congr
      unfold CompressToΛ.decode_cfg
      dsimp [C1_Λ]
      rw [TraceToTraceRtAndBorder.spec]
      dsimp [C1']
      dsimp [c_inr]

      have {α} (w: Word α) : (if p ≥ 0 then triple_at (config_to_trace ⟬w⟭) (3 * p).natAbs else fun x => none) =
          SpeedupKx.compress 3 ⟬w⟭ p := by

        unfold SpeedupKx.compress
        funext j
        by_cases hp: p >= 0
        case neg =>
          simp [hp]
          unfold word_to_config
          simp_all
          omega
        case pos =>
          simp [hp]
          unfold word_to_config triple_at config_to_trace
          grind

      simp [this]

    suffices (e.C.trace_rt w)[w.length - 1]'(by simp [List.length_pos_of_ne_nil hw])
      = (e.C2.trace_rt (e.C1.trace_rt w))[w.length - 1]'(by simp [List.length_pos_of_ne_nil hw]) by
      simp [List.getLast?_eq_getElem?]
      grind

    set t := w.length - 1 with t_h
    have t_len : t < w.length := by simp [t_h, List.length_pos_of_ne_nil hw]

    obtain ⟨t₁, t₂, ht⟩: ∃ t1: ℕ, ∃ t2: Fin 3, t = 3 * t1 + t2 := by
      use t / 3
      use ⟨t % 3, Nat.mod_lt _ (by decide)⟩
      simp [Nat.div_add_mod]

    calc (e.C.trace_rt w)[t]'(by simp_all)
      = (e.C.trace w) t := by simp [trace_rt]
      _ = e.C_exact.C.trace ⟬w⟭ t := by rfl
      _ = e.C_decomp.C.trace ⟬w⟭ (t + 6) := by
        rw [SpeedupKSteps.spec (h_len := by simp_all) (h_bound := by simp; omega)]

      _ = e.C_decomp.C.trace ⟬w⟭ (t + 3 + 3) := by simp
      _ = e.C_decomp.C.trace ⟬w⟭ (3 * t₁ + t₂ + 3 + 3) := by rw [ht]
      _ = e.C_decomp.C.trace ⟬w⟭ (3 * (t₁ + 1) + t₂ + 3) := by ring_nf
      _ = (e.C_sim.C.trace ⟬w⟭ (3 * (t₁ + 1) + 3)).get (by
          rw [e.C_sim.spec ⟬w⟭ c_inr x]
          simp) t₂ := by
        rw [DecompressTriple.spec2]
        exact e.C_sim.h_cond_form ⟬w⟭ c_inr x 3 rfl
        simp

      _ = (some (e.C2_3x.C.trace c_inr (t₁ + 1))).get (by trivial) t₂ := by
        have h := e.C_sim.spec ⟬w⟭ c_inr x (t₁ + 1)
        have h2 : (e.C_sim.C.trace ⟬w⟭ (3 * (t₁ + 1) + 3)) =
                  some (e.C2_3x.C.trace c_inr (t₁ + 1)) := h
        rw [show (e.C_sim.C.trace ⟬w⟭ (3 * (t₁ + 1) + 3)).get _ =
               (some (e.C2_3x.C.trace c_inr (t₁ + 1))).get (by trivial)
            from by simp only [h2, Option.get_some]]
      _ = e.C2_3x.C.trace c_inr (t₁ + 1) t₂ := by rfl
      _ = e.C2.trace ⟬e.C1.trace_rt w⟭ (3 * t₁ + t₂) := by
          rw [SpeedupAndTraceKx.spec1]

      _ = e.C2.trace ⟬e.C1.trace_rt w⟭ t := by rw [ht]
      _ = (e.C2.trace_rt (e.C1.trace_rt w))[t]'(by simp_all) := by simp [trace_rt]


end Composition


def CellAutomaton.compose_trace_rt {α β γ} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C2: CArtTransducer β γ) (C1: CArtTransducer α β): CArtTransducer α γ :=
  (Composition.mk C2 C1).C

infixr:90 "⊚"  => CellAutomaton.compose_trace_rt

@[simp]
theorem CellAutomaton.compose_trace_rt_spec {α β γ} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C2: CArtTransducer β γ) (C1: CArtTransducer α β):
    (C2.compose_trace_rt C1).trace_rt = C2.trace_rt ∘ C1.trace_rt := by
  rw [compose_trace_rt, Composition.spec]

@[simp]
theorem CArtTransducer.compose_trace_rt_advice_spec {α β γ} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C2: CArtTransducer β γ) (C1: CArtTransducer α β):
    (C2.compose_trace_rt C1).advice.f = C2.advice.f ∘ C1.advice.f := by
  simp [CArtTransducer.advice]

end CellularAutomatas
