import CellularAutomatas.proofs.advice_theory.finite_future_variation_not_future_index
import CellularAutomatas.proofs.advice_theory.rt_closed.broadcast_last
import CellularAutomatas.proofs.constructions.basic_exp_word

/-!
# Two-stage advice need not have finite future index

An RT recognizer can control a whole-word mask: its prefix answers form a CART
trace, and a reverse FST broadcasts the final answer before masking the input.
Applying this to powers-of-two lengths gives a uniformly RT-closed two-stage
advice with infinite future index.

Conversely, every causal advice has a one-state future index. Prefix advice
for a non-RT language therefore shows why finite index alone is insufficient.
-/

namespace CellularAutomatas

open CellAutomaton
open FiniteStateTransducer

variable {α : Type} [Alphabet α]

/-- Keep the input exactly when its RT recognizer accepts it. -/
def Advice.rtMask (C : CA_rt α) (blank : α) : Advice α α where
  f w := if C.accepts w then w else List.replicate w.length blank
  len := by intro w; split <;> simp

namespace RtMask

def decision (C : CA_rt α) : TwoStageAdvice α Bool :=
  TwoStageAdvice.from_transducers (fst_broadcast_last Bool) C.toCellAutomaton

lemma decision_spec (C : CA_rt α) (w : Word α) (hw : w ≠ []) :
    (decision C).advice w = List.replicate w.length (C.accepts w) := by
  have hlast : (C.trace_rt w).getLast?.getD false = C.accepts w := by
    rw [List.getLast?_eq_getLast_of_ne_nil (by simpa using hw)]
    simp only [Option.getD_some, List.getLast_eq_getElem, CellAutomaton.trace_rt,
      List.length_map, List.length_range, List.getElem_map, List.getElem_range]
    rfl
  calc
    (decision C).advice w
        = Advice.broadcast_last Bool (C.trace_rt w) := by
            simp [decision, TwoStageAdvice.from_transducers, TwoStageAdvice.advice,
              Advice.broadcast_last, fst_broadcast_last_scanr_eq]
    _ = List.replicate w.length (C.accepts w) := by
          simp [Advice.broadcast_last, hlast]

def combined (C : CA_rt α) : TwoStageAdvice α (α × Bool) :=
  zip_two_stage (ca_to_two_stage (ca_trace_id_word α)) (decision C)

def presentation (C : CA_rt α) (blank : α) : TwoStageAdvice α α where
  β := (combined C).β
  C := (combined C).C
  M := (combined C).M.map_output (fun (a, keep) => if keep then a else blank)

lemma presentation_spec (C : CA_rt α) (blank : α) :
    (presentation C blank).advice = Advice.rtMask C blank := by
  apply advice_eq_iff
  funext w
  by_cases hw : w = []
  · show (presentation C blank).advice w = Advice.rtMask C blank w
    subst w
    simp [Advice.rtMask]
  · show (presentation C blank).advice w = Advice.rtMask C blank w
    have hcombined : (combined C).advice w =
        w ⨂ List.replicate w.length (C.accepts w) := by
      simp [combined, decision_spec C w hw]
    calc
      (presentation C blank).advice w
          = List.map (fun (a, keep) => if keep then a else blank)
              ((combined C).advice w) := by
                simp [presentation, TwoStageAdvice.advice]
      _ = Advice.rtMask C blank w := by
            rw [hcombined]
            apply List.ext_getElem
            · simp
            · intro i hleft hright
              show (List.map (fun (a, keep) => if keep then a else blank)
                  (w ⨂ List.replicate w.length (C.accepts w)))[i] =
                (Advice.rtMask C blank w)[i]
              by_cases haccepts : C.accepts w = true <;>
                simp [Advice.rtMask, haccepts]

end RtMask

def Advice.rtMask_is_two_stage (C : CA_rt α) (blank : α) :
    (Advice.rtMask C blank).is_two_stage_advice :=
  ⟨RtMask.presentation C blank, RtMask.presentation_spec C blank⟩

def Advice.rtMask_rt_closed (C : CA_rt α) (blank : α) :
    (Advice.rtMask C blank).rt_closed :=
  (Advice.rtMask_is_two_stage C blank).rt_closed

/-- The existing length mask is an instance of the general RT-controlled mask. -/
lemma lengthPow2Mask_eq_rtMask :
    lengthPow2Mask = Advice.rtMask (exp_word_ca.map_embed (fun _ : Bool => ())) false := by
  classical
  apply advice_eq_iff
  funext w
  have haccepts :
      (exp_word_ca.map_embed (fun _ : Bool => ())).accepts w = true ↔ isPow2 w.length := by
    change w ∈ (exp_word_ca.map_embed (fun _ : Bool => ())).L ↔ _
    rw [map_embed_L]
    simpa [isPow2] using exp_word_ca_correct (w.map (fun _ => ()))
  change (if isPow2 w.length then w else List.replicate w.length false) =
    (if (exp_word_ca.map_embed (fun _ : Bool => ())).accepts w = true then w
      else List.replicate w.length false)
  simp only [haccepts]

def lengthPow2Mask_is_two_stage : lengthPow2Mask.is_two_stage_advice := by
  rw [lengthPow2Mask_eq_rtMask]
  exact Advice.rtMask_is_two_stage _ false

noncomputable def lengthPow2Mask_rt_closed : lengthPow2Mask.rt_closed :=
  lengthPow2Mask_is_two_stage.rt_closed

/-- Finite future index is not necessary even for uniformly RT-closed advice. -/
theorem exists_two_stage_rt_closed_without_finite_future_index :
    ∃ adv : Advice Bool Bool,
      Nonempty adv.is_two_stage_advice ∧ Nonempty adv.rt_closed ∧
        IsEmpty adv.finite_future_index :=
  ⟨lengthPow2Mask, ⟨lengthPow2Mask_is_two_stage⟩, ⟨lengthPow2Mask_rt_closed⟩,
    lengthPow2Mask_not_finite_future_index⟩

variable {Γ : Type} [Alphabet Γ]

omit [Alphabet α] [Alphabet Γ] in
/-- Causality is exactly the case where all suffixes are future-equivalent. -/
theorem Advice.all_future_equivalent_iff_causal (adv : Advice α Γ) :
    (∀ z z', adv.future_equivalent z z') ↔ adv.causal := by
  constructor
  · intro h
    show IsCausal adv.f
    intro w
    refine ⟨adv.len w, ?_⟩
    intro i
    have hcut := h (w.drop i) [] (w.take i)
    have hleft : (adv (w.take i)).take (w.take i).length = adv (w.take i) := by
      rw [← adv.len (w.take i), List.take_length]
    change (adv (w.take i ++ w.drop i)).take (w.take i).length =
      (adv (w.take i ++ [])).take (w.take i).length at hcut
    rw [List.take_append_drop, List.append_nil, hleft, List.length_take] at hcut
    by_cases hi : i ≤ w.length
    · show adv.f (w.take i) = (adv.f w).take i
      simpa [Nat.min_eq_left hi] using hcut.symm
    · show adv.f (w.take i) = (adv.f w).take i
      have hle : w.length ≤ i := by omega
      rw [List.take_of_length_le hle, List.take_of_length_le (by simpa using hle)]
  · intro h z z' p
    show (adv (p ++ z)).take p.length = (adv (p ++ z')).take p.length
    calc
      (adv (p ++ z)).take p.length = adv p := h.take_of_concat p z
      _ = (adv (p ++ z')).take p.length := (h.take_of_concat p z').symm

/-- The unique future class of a causal advice is represented by the empty suffix. -/
def Advice.finite_future_index_of_causal (adv : Advice α Γ) (h : adv.causal) :
    adv.finite_future_index where
  S := Unit
  index := fun _ => ()
  representative := fun _ => []
  representative_index := by intro s; cases s; rfl
  index_eq_iff := by
    intro z z'
    show (() = ()) ↔ adv.future_equivalent z z'
    exact ⟨fun _ => (adv.all_future_equivalent_iff_causal.mpr h) z z', fun _ => rfl⟩

/-- Even index one cannot make prefix advice for a non-RT language two-stage. -/
theorem prefix_mem_finite_future_index_not_two_stage
    (L : Language α) [DecidablePred L]
    (h_empty : [] ∉ L) (h_not_rt : L ∉ ℒ (CA_rt α)) :
    Nonempty (Advice.prefix_mem L).finite_future_index ∧
      IsEmpty (Advice.prefix_mem L).is_two_stage_advice :=
  ⟨⟨Advice.finite_future_index_of_causal _ (Advice.prefix_mem_causal L)⟩,
    Advice.prefix_mem_not_two_stage L h_empty h_not_rt⟩

end CellularAutomatas
