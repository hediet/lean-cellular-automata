import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import CellularAutomatas.defs
import CellularAutomatas.proofs.composition
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.advice_prefix_mem_rt_closed
import CellularAutomatas.proofs.two_stage_is_rt_closed

namespace CellularAutomatas


open Classical


variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]


lemma tCellAutomatonWithAdvice.elem_L_iff {α} {C: tCellAutomaton (α × Γ)} {adv: Advice α Γ} (w: Word α):
    w ∈ (C + adv).L ↔ adv.annotate w ∈ C.L := by rfl


def L_c (adv: Advice α Γ) (c: Γ) : Language α :=
  { w | (adv.f w).getLast? = some c }


def CA_adv_L_c (α) [Alphabet α] (c : Γ) : CA_rt (α × Γ) :=
  fix_empty false (toRtCa ((ca_id_word (α × Γ)).map_project (fun (_, g) => g == c)))


lemma CA_adv_L_c_spec (adv : Advice α Γ) (c : Γ) : ((CA_adv_L_c α c).val + adv).L = L_c adv c := by
  ext w
  rw [tCellAutomatonWithAdvice.elem_L_iff]
  rw [L_c]
  rw [prop_of_elem_prop_set]


  by_cases h: w = []
  · simp [h, CA_adv_L_c]

  unfold CA_adv_L_c
  rw [fix_empty_spec]
  simp [h]

  rw [←trace_rt_L (by simp_all)]

  convert_to (((List.getLast ((adv.annotate w).map Prod.snd) (by simp_all))) = c ↔ List.getLast? (adv.f w) = some c)
  · simp

  unfold Advice.annotate
  simp only [←Word.snd.eq_1]
  simp
  grind



lemma L_c_in_rt (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) :
    ∃ C : CA_rt α, C.val.L = L_c adv c := by
  have := tCellAutomatonWithAdvice.exists_CA_rt_of_rt_closed h (CA_adv_L_c α c)
  rw [CA_adv_L_c_spec] at this
  exact this


noncomputable def CA_L_c (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) : CA_rt α :=
  Classical.choose (L_c_in_rt adv h c)

@[simp]
lemma CA_L_c_spec (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) :
    (CA_L_c adv h c).val.L = L_c adv c :=
  Classical.choose_spec (L_c_in_rt adv h c)



namespace PrefixStableProof

  variable (adv: Advice α Γ) (h1: adv.rt_closed)


  noncomputable def first_true_or_default (q: Γ → Bool) : Γ :=
    let valid_c := Finset.univ.filter (fun c => q c)
    valid_c.toList.head?.getD default

  lemma first_true_or_default_spec (x: Γ): first_true_or_default (fun c => decide (x = c)) = x := by
    unfold first_true_or_default
    have : (Finset.univ.filter (fun c => decide (x = c))) = {x} := by
      ext
      simp [eq_comm]
    rw [this]
    simp

  noncomputable def ts_adv : TwoStageAdvice α Γ := {
    C := (ProdCA (fun c => (CA_L_c adv h1 c).val.toCellAutomaton)).map_project first_true_or_default
    β := Γ
    M := FiniteStateTransducer.M_id Γ
  }

  lemma getLastOfTake (h: i < w.length): (List.take (i + 1) w).getLast? = w[i]? := by
    grind

  lemma f (h2: adv.prefix_stable): (ts_adv adv h1).advice = adv := by
    apply advice_eq_iff
    funext w
    apply List.ext_getElem
    · simp
    intro i h_i1 h_i2

    have w_len: i < w.length := by simp_all

    calc ((ts_adv adv h1).advice.f w)[i]
      _ = (first_true_or_default fun b => decide (List.take (i + 1) w ∈ L_c adv b)) := by
        simp [TwoStageAdvice.advice, ts_adv, w_len, trace_rt_getElem_i_iff2]

      _ = (first_true_or_default fun b => (adv.f w)[i] = b) := by
        congr
        ext b
        congr
        unfold L_c
        rw [prop_of_elem_prop_set]
        unfold Advice.prefix_stable at h2
        rw [h2]
        simp [List.getLast?_take, w_len]

      _ = (adv.f w)[i] := by
        rw [first_true_or_default_spec]


end PrefixStableProof



theorem is_two_stage_of_rt_closed_and_prefix_stable (adv: Advice α Γ) (h1: adv.rt_closed) (h2: adv.prefix_stable):
    adv.is_two_stage_advice := by

    unfold Advice.is_two_stage_advice
    use PrefixStableProof.ts_adv adv h1
    simp [PrefixStableProof.f adv h1 h2]
