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
import CellularAutomatas.proofs.constructions.composition.compose_cart
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.trace_id
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.advice_prefix_mem_rt_closed
import CellularAutomatas.proofs.two_stage_is_rt_closed

namespace CellularAutomatas


open Classical


variable {α: Type} [Alphabet α]
variable {Γ: Type} [Alphabet Γ]


lemma tCellAutomatonWithAdvice.elem_L_iff {schema : AcceptanceSchema} {α} {C: tCellAutomaton schema (α × Γ)} {adv: Advice α Γ} (w: Word α):
    w ∈ (C + adv).L ↔ adv.annotate w ∈ C.L := by rfl


def L_c (adv: Advice α Γ) (c: Γ) : Language α :=
  { w | (adv w).getLast? = some c }


def CA_adv_L_c (α) [Alphabet α] (c : Γ) : CA_rt (α × Γ) :=
  fix_empty false (toRtCa ((ca_trace_id_word (α × Γ)).map_project (fun (_, g) => g == c)))


lemma CA_adv_L_c_spec (adv : Advice α Γ) (c : Γ) : ((CA_adv_L_c α c) + adv).L = L_c adv c := by
  ext w
  rw [tCellAutomatonWithAdvice.elem_L_iff]
  rw [L_c]
  rw [Set.mem_setOf_eq]


  by_cases h: w = []
  · simp [h, CA_adv_L_c]

  unfold CA_adv_L_c
  rw [fix_empty_spec]
  simp [h]

  rw [←trace_rt_L (by simp_all)]

  convert_to (((List.getLast ((adv.annotate w).map Prod.snd) (by simp_all))) = c ↔ List.getLast? (adv w) = some c)
  · simp

  unfold Advice.annotate
  simp only [←Word.snd.eq_1]
  simp
  grind



lemma L_c_in_rt (adv: Advice α Γ) (h: adv.weak_rt_closed) (c: Γ) :
    ∃ C : CA_rt α, C.L = L_c adv c := by
  have := tCellAutomatonWithAdvice.exists_CA_rt_of_weak_rt_closed h (CA_adv_L_c α c)
  rw [CA_adv_L_c_spec] at this
  exact this


def CA_L_c (adv: Advice α Γ) (h: adv.weak_rt_closed) (c: Γ) : CA_rt α :=
  h.map (CA_adv_L_c α c)

@[simp]
lemma CA_L_c_spec (adv: Advice α Γ) (h: adv.weak_rt_closed) (c: Γ) :
    (CA_L_c adv h c).L = L_c adv c := by
  show (h.map (CA_adv_L_c α c)).L = L_c adv c
  rw [h.spec (CA_adv_L_c α c)]
  exact CA_adv_L_c_spec adv c



namespace PrefixStableProof

  variable (adv: Advice α Γ) (h1: adv.weak_rt_closed)

  -- Computably select the unique element where q returns true, or default if none.
  -- When the filter has exactly one element, Finset.choose extracts it computably
  -- via Quot.recOnSubsingleton (result is the same regardless of list representative).
  def first_true_or_default (q: Γ → Bool) : Γ :=
    let filtered := Finset.univ.filter (fun c => q c)
    if h : filtered.card = 1
    then
      -- card = 1 implies ∃! a, a ∈ filtered ∧ True
      have h_unique : ∃! a, a ∈ filtered ∧ True := by
        rw [Finset.card_eq_one] at h
        obtain ⟨a, ha⟩ := h
        exact ⟨a, ⟨by simp [ha], trivial⟩, fun b ⟨hb, _⟩ => by simp [ha] at hb; exact hb⟩
      filtered.choose (fun _ => True) h_unique
    else default

  lemma first_true_or_default_spec (x: Γ): first_true_or_default (fun c => decide (x = c)) = x := by
    unfold first_true_or_default
    simp only
    have h_card : (Finset.univ.filter (fun c => decide (x = c))).card = 1 := by
      have : Finset.univ.filter (fun c => decide (x = c)) = {x} := by ext c; simp [eq_comm]
      rw [this]; simp
    rw [dif_pos h_card]
    generalize_proofs hp
    have h_spec := Finset.choose_spec (fun (_ : Γ) => True)
      (Finset.univ.filter (fun c => decide (x = c))) hp
    have h_mem := h_spec.1
    rw [Finset.mem_filter] at h_mem
    have h_eq : decide (x = Finset.choose _ _ hp) = true := h_mem.2
    rw [decide_eq_true_eq] at h_eq
    exact h_eq.symm

  def cart_adv : CArtTransducer α Γ :=
    (ProdCA (fun c => (CA_L_c adv h1 c).toCellAutomaton)).map_project first_true_or_default

  lemma getLastOfTake (h: i < w.length): (List.take (i + 1) w).getLast? = w[i]? := by
    grind

  lemma cart_adv_spec (h2: adv.causal): (cart_adv adv h1).advice = adv := by
    apply advice_eq_iff
    funext w
    apply List.ext_getElem
    · simp [CArtTransducer.advice]
    intro i h_i1 h_i2

    have w_len: i < w.length := by simp [CArtTransducer.advice] at h_i1; exact h_i1

    calc ((cart_adv adv h1).advice w)[i]
      _ = (first_true_or_default fun b => decide (List.take (i + 1) w ∈ L_c adv b)) := by
        simp [CArtTransducer.advice, cart_adv, w_len, trace_rt_getElem_i_iff2]

      _ = (first_true_or_default fun b => (adv w)[i] = b) := by
        congr
        ext b
        congr
        unfold L_c
        rw [Set.mem_setOf_eq]
        rw [(h2 w).2]
        simp [List.getLast?_take, w_len]

      _ = (adv w)[i] := by
        rw [first_true_or_default_spec]


end PrefixStableProof



def is_cart_advice_of_rt_closed_and_causal (adv: Advice α Γ) (h1: adv.weak_rt_closed) (h2: adv.causal):
    adv.is_cart_advice :=
  ⟨_, PrefixStableProof.cart_adv_spec adv h1 h2⟩

def is_two_stage_of_rt_closed_and_causal (adv: Advice α Γ) (h1: adv.weak_rt_closed) (h2: adv.causal):
    adv.is_two_stage_advice :=
  (is_cart_advice_of_rt_closed_and_causal adv h1 h2).is_two_stage

def rt_closed_of_weak_rt_closed_and_causal (adv: Advice α Γ) (h1: adv.weak_rt_closed) (h2: adv.causal):
    adv.rt_closed :=
  PrefixStableProof.cart_adv_spec adv h1 h2 ▸ cart_is_rt_closed (PrefixStableProof.cart_adv adv h1)
