import CellularAutomatas.defs
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.constructions.basic_flip
import CellularAutomatas.proofs.word_ops
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring

namespace CellularAutomatas








lemma nextt_congr {α β} (C: CellAutomaton α β) (c1 c2: Config C.Q) (t: ℕ) (i: ℤ):
    (∀ j, i - t ≤ j ∧ j ≤ i + t → c1 j = c2 j) →
    (C.nextt c1 t) i = (C.nextt c2 t) i := by
  induction t generalizing i c1 c2 with
  | zero =>
    intro h
    simp [CellAutomaton.nextt]
    apply h
    constructor <;> omega
  | succ t ih =>
    intro h
    simp [CellAutomaton.nextt]
    -- The goal is now nextt (next c1) t i = nextt (next c2) t i
    apply ih
    intro j hj
    simp only [CellAutomaton.next_apply]
    congr 1
    · apply h
      constructor <;> omega
    · apply h
      constructor <;> omega
    · apply h
      constructor <;> omega

lemma LCellAutomaton.scan_temporal_independence_at_0 {β} [Alphabet β] (C: CellAutomaton α？ β) (p s: Word α) (t: ℕ) (ht: t < p.length):
  (C.nextt ⦋⟬p ++ s⟭⦌ t) 0 = (C.nextt ⦋⟬p⟭⦌ t) 0 := by
  apply nextt_congr
  intro j hj
  simp only [zero_sub, zero_add] at hj
  unfold CellAutomaton.embed_config word_to_config
  by_cases h_if : j ≥ 0 ∧ j < ↑(List.length (p ++ s))
  · have h_if_p : j ≥ 0 ∧ j < ↑(List.length p) := by
      constructor
      · exact h_if.1
      · have : j ≤ t := hj.2
        have : t < p.length := ht
        omega
    grind
  · have h_if_p : ¬(j ≥ 0 ∧ j < ↑(List.length p)) := by
      intro h
      apply h_if
      constructor
      · exact h.1
      · apply lt_of_lt_of_le h.2
        simp
    grind

@[simp]
lemma CellAutomaton.trace_rt_is_causal {α β: Type} [Alphabet β] (C: CellAutomaton α？ β): IsCausal C.trace_rt := by
  intro w
  refine ⟨trace_rt_len C w, fun i => ?_⟩
  apply List.ext_getElem (by simp)
  intro t h1 h2
  simp only [CellAutomaton.trace_rt, List.getElem_map, List.getElem_range, List.getElem_take]
  unfold CellAutomaton.trace
  simp only [comp_apply, Function.comp_apply]
  congr 1
  have ht : t < (w.take i).length := by simpa using h1
  conv_rhs => rw [show w = (w.take i) ++ (w.drop i) from (List.take_append_drop i w).symm]
  exact (LCellAutomaton.scan_temporal_independence_at_0 C (w.take i) (w.drop i) t ht).symm

@[simp]
theorem LCellAutomaton.scan_temporal_independence {β} [Alphabet β] (C: CellAutomaton α？ β) (p s: Word α):
  (C.trace_rt (p ++ s)).take p.length = C.trace_rt p := by
  rw [← (CellAutomaton.trace_rt_is_causal C (p ++ s)).2 p.length]
  simp

@[simp]
theorem CArtTransducer.scan_temporal_independence [Alphabet α] [Alphabet Γ] (C: CArtTransducer α Γ) (p s: Word α):
  (C.advice.f (p ++ s)).take p.length = C.advice.f p := by
  unfold CArtTransducer.advice
  simp



open CellAutomaton


@[simp]
lemma trace_rt_length {α β: Type} {C: CellAutomaton α？ β} {w: Word α}:
  (C.trace_rt w).length = w.length := by simp [trace_rt]

@[simp]
lemma trace_rt_empty {α β: Type} {C: CellAutomaton α？ β}:
  (C.trace_rt []) = [] := by simp [trace_rt]

@[simp]
lemma map_embed_trace_rt {α β γ: Type} (C: CellAutomaton β？ γ) (f: α → β) (w: Word α):
    (C.map_embed (Option.map f)).trace_rt w = C.trace_rt (w.map f) := by
  apply List.ext_getElem
  · simp
  intro i hi1 hi2
  simp only [trace_rt, List.getElem_map, List.getElem_range, trace_eq_comp, comp_apply]
  -- Show that nextt is the same for all positions
  have h_embed_eq : ∀ p : ℤ, @embed_config _ _ (C.map_embed (Option.map f)) (word_to_config w) p =
                            @embed_config _ _ C (word_to_config (w.map f)) p := by
    intro p
    simp [embed_config, word_to_config_apply, map_embed]
  -- The nextt values are the same because δ is the same and embed_config is the same
  have h_nextt_eq : ∀ t : ℕ, ∀ p : ℤ,
      (C.map_embed (Option.map f)).nextt ⦋w⦌ t p = C.nextt ⦋w.map f⦌ t p := by
    intro t
    induction t with
    | zero => intro p; exact h_embed_eq p
    | succ t ih =>
      intro p
      simp only [nextt_succ, next_apply, map_embed]
      congr 1 <;> exact ih _
  -- project is the same for map_embed
  simp only [map_embed]
  exact congrArg C.project (h_nextt_eq i 0)



@[grind =]
lemma word_to_config_natcast_eq {w: Word α} {t: ℕ} (h: t < w.length): ⟬w⟭ ↑t = some w[t] := by simp [word_to_config, h]






lemma tCellAutomaton.elem_L_iff {C: tCellAutomaton α}:
  w ∈ C.L ↔ ((C.comp w (C.t w.length)) (C.p w.length)) := by rfl


@[simp]
lemma CA_rt_t (C: CA_rt α) (n: Nat) :
  C.val.t n = n - 1 := by
  unfold CA_rt t_rt at C
  grind

@[simp]
lemma CA_rt_p (C: CA_rt α) (n: Nat) :
  C.val.p n = 0 := by
  unfold CA_rt CA t_rt at C
  grind



def toRtCa {α} [Alphabet α] (C: CellAutomaton α？ Bool): CA_rt α :=
  ⟨{
    toCellAutomaton := C
    t n := n - 1
    p _ := 0
  }, by simp [CA_rt, t_rt, CA, tCellAutomata]⟩

@[simp]
lemma toRtCa_spec {α} [Alphabet α] (C: CellAutomaton α？ Bool) (w: Word α):
    (toRtCa C).val.trace_rt w = C.trace_rt w := by
  rfl



lemma CA_rt_L_iff {C: CA_rt α}:
  w ∈ C.val.L ↔ (C.val.comp w (w.length - 1)) 0 = true := by
  simp [tCellAutomaton.elem_L_iff, CA_rt_t, CA_rt_p]

lemma CA_rt_L_iff2 {C: tCellAutomaton α} (h: C ∈ CA_rt α):
  w ∈ C.L ↔ (C.comp w (w.length - 1)) 0 = true := by
  rw [CA_rt_L_iff (C := ⟨_, h⟩)]

lemma trace_L {C: CA_rt α} {w: Word α}: C.val.trace w (w.length - 1) = true ↔ w ∈ C.val.L := by
  simp [CellAutomaton.trace, CA_rt_L_iff]

@[simp]
lemma trace_rt_neq_empty {C: CellAutomaton (Option α) β} {w: Word α}: (C.trace_rt w) ≠ [] ↔ w ≠ [] := by
  simp [←List.length_eq_zero_iff]

lemma trace_rt_L {C: CA_rt α} {w: Word α} (h: w ≠ []):
  (C.val.trace_rt w).getLast (by simp [h]) = true ↔ w ∈ C.val.L := by
  rw [List.getLast_eq_getElem]
  simp only [CellAutomaton.trace_rt, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  exact trace_L




lemma trace_rt_getElem_i_iff2 {C: CA_rt α} {w: Word α} (i: Nat) (h: i < (C.val.trace_rt w).length ):
    (C.val.trace_rt w)[i] = decide (w.take (i+1) ∈ C.val.L) := by
  have h_len : i < w.length := by simpa using h
  simp only [CellAutomaton.trace_rt, List.getElem_map, List.getElem_range]
  unfold CellAutomaton.trace
  simp only [comp_apply, CA_rt_L_iff]
  simp only [List.length_take]
  rw [min_eq_left (by omega)]
  simp only [Nat.add_sub_cancel]
  simp only [Bool.decide_eq_true]

  let p := w.take (i+1)
  let s := w.drop (i+1)
  have hw : w = p ++ s := (List.take_append_drop (i + 1) w).symm

  conv =>
    lhs
    rw [hw]
    rw [LCellAutomaton.scan_temporal_independence_at_0 (t := i) (ht := by simp [p]; omega)]

lemma trace_rt_getElem_i_iff {C: CA_rt α} {w: Word α} (i: Nat) (h: i < (C.val.trace_rt w).length ):
    (C.val.trace_rt w)[i] = true ↔ w.take (i+1) ∈ C.val.L := by
  simp [trace_rt_getElem_i_iff2]


lemma elemL_iff_trace_rt [Alphabet α] {C: tCellAutomaton α} (h: C ∈ CA_rt α) {w: Word α}:
    w ∈ C.L ↔ if w = [] then [] ∈ C.L else (C.trace_rt w).getLast? = some true := by
  by_cases hw : w = []
  · simp [hw]
  · have h_tr_ne : (C.trace_rt w) ≠ [] := by simp [trace_rt_neq_empty, hw]
    rw [List.getLast?_eq_some_getLast h_tr_ne]
    simp [hw, trace_rt_L (C := ⟨C, h⟩)]



/-

def word_dvd_k_ext (k: ℕ) (w_len: ℕ) := (w_len - (w_len % w_len)) % w_len

def word_dvd_k (k: ℕ) (w: Word α): Word (Option α) :=
  w.map (fun a => some a) ++ List.replicate (word_dvd_k_ext k w.length) none

def L_dvd_k (k: ℕ) (L: Language α): Language (Option α) := { word_dvd_k k w | w ∈ L }

theorem L_in_RT_iff_L_dvd_k_in_RT [Alphabet α] (k: ℕ) (L: Language α):
    L ∈ ℒ (CA_rt α) ↔ (L_dvd_k k L) ∈ ℒ (CA_rt (Option α)) := by
  sor ry

-/





@[simp]
lemma nextt0 (C: CellAutomaton α β) (c: Config C.Q): C.nextt c 0 = c := by simp [CellAutomaton.nextt]

@[simp]
lemma nextt1 (C: CellAutomaton α β) (c: Config C.Q): C.nextt c 1 = C.next c := by simp [CellAutomaton.nextt]

/-
lemma LCellAutomaton.embed_word_eq (C: LCellAutomaton α) {w: Word α} {p: ℤ} (h: p ∈ w.range):
    C.embed_word w p = C.embed (w.get' p h) := by
      grind [LCellAutomaton.embed_word, Word.get']
-/


lemma LCellAutomaton.nextt_succ_eq (C: CellAutomaton α β) (c: Config C.Q): C.nextt c (t + 1) = C.next (C.nextt c t) := by
  simp


/-
lemma LCellAutomaton.comp_succ_eq (C: LCellAutomaton α): C.comp w (t + 1) = C.next (C.comp w t) := by
  funext i
  simp [LCellAutomaton.comp_unfold, LCellAutomaton.nextt_succ_eq]
-/





variable [Alphabet α] [Alphabet Γ]

lemma ℒ_CA_rt_iff {α} [Alphabet α] {L: Language α}: L ∈ ℒ (CA_rt α) ↔ ∃ C ∈ CA_rt α, C.L = L := by
  unfold ℒ
  constructor
  · rintro ⟨C, hC, rfl⟩
    use C, hC
    rfl
  · rintro ⟨C, hC, rfl⟩
    use C, hC
    rfl


lemma ℒ_oca_def (adv: Advice α Γ) (L: Language α):
      L ∈ ℒ (CA_rt (α × Γ) + adv) ↔ ∃ C ∈ CA_rt (α × Γ), L = { w | (w ⨂ (adv.f w)) ∈ C.L } := by
  unfold ℒ
  constructor
  · rintro ⟨ca, h_ca, rfl⟩
    simp [HAdd.hAdd] at h_ca
    rcases h_ca with ⟨C, hC, rfl⟩
    use C, hC
    rfl
  · rintro ⟨C, hC, rfl⟩
    use tCellAutomatonWithAdvice.mk Γ adv C
    constructor
    · simp [HAdd.hAdd, hC]
    · rfl

def tCellAutomaton.map_embed {α β} (C: tCellAutomaton α) (f: β → α): tCellAutomaton β :=
  {
    toCellAutomaton := C.toCellAutomaton.map_embed (Option.map f)
    t := C.t
    p := C.p
  }

@[simp]
lemma c_map_embed_in_ca_rt_iff_c_in_ca_rt {α β} (C: tCellAutomaton α) (f: β → α):
    C.map_embed f ∈ CA_rt β ↔ C ∈ CA_rt α := by rfl

@[simp]
lemma tCellAutomaton.map_embed_trace_rt {α β} (C: tCellAutomaton α) (f: β → α) (w: Word β):
    (C.map_embed f).trace_rt w = C.trace_rt (w.map f) := by
  unfold tCellAutomaton.map_embed
  simp

@[simp]
lemma map_embed_L {α} (C: tCellAutomaton α) (f: β → α) (w: Word β):
    w ∈ (C.map_embed f).L ↔ (w.map f) ∈ C.L := by

  suffices @CellAutomaton.embed_config _ _ C.toCellAutomaton (word_to_config (w.map f))
      = @CellAutomaton.embed_config _ _ (C.map_embed f).toCellAutomaton (word_to_config w) by
    rw [tCellAutomaton.elem_L_iff]
    rw [tCellAutomaton.elem_L_iff]
    rw [this]
    congr 1
    simp [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold, tCellAutomaton.map_embed, map_embed_nextt]
    rfl
  unfold CellAutomaton.embed_config word_to_config
  funext p
  simp [tCellAutomaton.map_embed, CellAutomaton.map_embed]


lemma CA_rt_subseteq_CA_rt_with_advice (adv: Advice α Γ):
    (ℒ (CA_rt α)) ⊆ ((ℒ (CA_rt (α × Γ) + adv)): Set (Language α)) := by
  intro L hL
  rcases ℒ_CA_rt_iff.mp hL with ⟨C, hC, rfl⟩
  rw [ℒ_oca_def]

  let C': CA_rt (α × Γ) := ⟨ C.map_embed Prod.fst, by simp_all ⟩
  use C'

  constructor
  · simp

  · ext w

    rw [Set.mem_setOf_eq]
    simp [C']
    rw [List.map_fst_zip]
    simp


lemma CArtWithAdvice_eq_CArt_iff (adv: Advice α Γ):
    ℒ (CA_rt (α ⨉ Γ) + adv) = ℒ (CA_rt α)
    ↔ ∀ L ∈ ℒ (CA_rt (α ⨉ Γ) + adv), L ∈ ℒ (CA_rt α) := by
  grind [CA_rt_subseteq_CA_rt_with_advice]






  section
    lemma embed_word_at_eq {α β: Type} (w: Word α) {C: CellAutomaton α？ β} (p: ℤ):
        CellAutomaton.embed_config (C := C) (word_to_config w) p = C.embed (if h: p ∈ w.range then  (some (w.get' p h)) else none) := by rfl

    lemma embed_word_at_eq1 {α β: Type} (w: Word α) {C: CellAutomaton α？ β} (p: ℤ) (h: p ∈ w.range):
        CellAutomaton.embed_config (C := C) (word_to_config w) p = C.embed (some (w.get' p h)) := by
      rw [embed_word_at_eq]; simp [h]

    lemma embed_word_at_eq2 {α β: Type} (w: Word α) {C: CellAutomaton α？ β} (p: ℤ) (h: ¬(p ∈ w.range)):
        CellAutomaton.embed_config (C := C) (word_to_config w) p = C.embed none := by
      rw [embed_word_at_eq]; simp [h]

  end

  @[simp]
  lemma project_config_at {α β: Type} [Alphabet α] [Alphabet β] {C: CellAutomaton α？ β} (p: ℤ) {c: Config C.Q}:
    C.project_config c p = C.project (c p) := project_config_apply C c p

  lemma comp_word_eq_project_nextt {α β: Type} {C: CellAutomaton α？ β} (w: Word α) (t: ℕ):
      C.comp w t = C.project_config (C.nextt w t) := by
    simp only [CellAutomaton.comp_unfold]

  lemma comp_config_eq_project_nextt {α β: Type} {C: CellAutomaton α β} (c: Config α) (t: ℕ):
      C.comp c t = C.project_config (C.nextt c t) := by
    simp only [CellAutomaton.comp_unfold]





lemma nextt_shift {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t: ℕ) (x d: ℤ):
    C.nextt c t (x + d) = C.nextt (fun i => c (i + d)) t x := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [nextt_succ, nextt_succ]
    unfold CellAutomaton.next
    have h1 : x + d - 1 = x - 1 + d := by ring
    have h2 : x + d + 1 = x + 1 + d := by ring
    rw [h1, h2]
    rw [ih (x-1), ih x, ih (x+1)]

lemma nextt_locality {α β: Type} (C: CellAutomaton α β) (c1 c2: Config C.Q) (t: ℕ) (x: ℤ):
    (∀ y, x - t ≤ y ∧ y ≤ x + t → c1 y = c2 y) → C.nextt c1 t x = C.nextt c2 t x := by
  induction t generalizing x with
  | zero =>
    intro h
    apply h
    simp
  | succ t ih =>
    intro h
    rw [nextt_succ, nextt_succ]
    unfold CellAutomaton.next
    grind



lemma nextt_add {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t1 t2: ℕ):
    C.nextt c (t1 + t2) = C.nextt (C.nextt c t1) t2 := by
  rw [Nat.add_comm]
  rw [nextt, Function.iterate_add_apply]
  rfl
