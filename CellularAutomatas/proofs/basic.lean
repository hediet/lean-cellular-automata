import CellularAutomatas.defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring

namespace CellularAutomatas


lemma prop_of_elem_prop_set {α} (x: α) (P: α → Prop): x ∈ { x | P x } ↔ P x := by
  constructor
  · intro h
    exact h
  · intro h
    exact h




private lemma list_map_congr {α β} {f g : α → β} {l : List α} (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
  simp only [List.map_cons, List.cons.injEq]
  constructor
  · apply h; simp
  · apply ih; intro x hx; apply h; simp [hx]


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
    unfold CellAutomaton.next
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
  delta embed_word word_to_config
  unfold CellAutomaton.embed_config
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
theorem LCellAutomaton.scan_temporal_independence {β} [Alphabet β] (C: CellAutomaton α？ β) (p s: Word α):
  (C.trace_rt (p ++ s)).take p.length = C.trace_rt p := by
  unfold CellAutomaton.trace_rt
  rw [← List.map_take, List.take_range, min_eq_left (by simp)]
  apply list_map_congr
  intro t ht
  rw [List.mem_range] at ht
  unfold CellAutomaton.trace CellAutomaton.comp CellAutomaton.project_config
  simp only [Function.comp_apply]
  congr 1
  apply LCellAutomaton.scan_temporal_independence_at_0
  exact ht

@[simp]
theorem CArtTransducer.scan_temporal_independence [Alphabet α] [Alphabet Γ] (C: CArtTransducer α Γ) (p s: Word α):
  (C.advice.f (p ++ s)).take p.length = C.advice.f p := by
  unfold CArtTransducer.advice
  simp



open CellAutomaton


@[simp]
lemma comp_of_map_project {α β γ: Type} {C: CellAutomaton α β} (f: β → γ) (c: Config α):
      (C.map_project f).comp c t i = f (C.comp c t i) := by
  rfl

@[simp]
lemma trace_of_map_project {α β γ: Type} {C: CellAutomaton α？ β} (f: β → γ) (w: Word α):
      (C.map_project f).trace w = f ∘ (C.trace w) := by
  funext i
  unfold trace comp project_config
  simp
  unfold map_project
  rfl

@[simp]
lemma trace_rt_of_map_project {α β γ: Type} {C: CellAutomaton α？ β} (f: β → γ) (w: Word α):
      (C.map_project f).trace_rt w = (C.trace_rt w).map f := by
  unfold trace_rt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

@[simp]
lemma trace_rt_length {α β: Type} {C: CellAutomaton α？ β} {w: Word α}:
  (C.trace_rt w).length = w.length := by simp [trace_rt]



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
  simp [List.getLast_eq_getElem, CellAutomaton.trace_rt, trace_L]




lemma trace_rt_getElem_i_iff2 {C: CA_rt α} {w: Word α} (i: Nat) (h: i < (C.val.trace_rt w).length ):
    (C.val.trace_rt w)[i] = decide (w.take (i+1) ∈ C.val.L) := by
  have h_len : i < w.length := by simpa using h
  simp only [CellAutomaton.trace_rt, List.getElem_map, List.getElem_range]
  unfold CellAutomaton.trace
  simp only [CA_rt_L_iff]
  simp only [List.length_take]
  rw [min_eq_left (by omega)]
  simp only [Nat.add_sub_cancel]
  simp only [Bool.decide_eq_true]

  let p := w.take (i+1)
  let s := w.drop (i+1)
  have hw : w = p ++ s := (List.take_append_drop (i + 1) w).symm

  conv =>
    lhs
    dsimp [CellAutomaton.comp, CellAutomaton.project_config]
    rw [hw]
    rw [← embed_word_word_to_config_eq]
    rw [LCellAutomaton.scan_temporal_independence_at_0 (t := i) (ht := by simp [p]; omega)]

  simp only [embed_word_word_to_config_eq]
  rfl

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





def config_to_trace {α: Type} (c: Config α): Trace α := fun t => c t

section id

  def ca_id (α : Type) [Alphabet α] : CellAutomaton α α := {
    Q := α
    δ := fun _ _ r => r
    embed := id
    project := id
  }


  @[simp]
  lemma ca_id_trace_eq {α : Type} [Alphabet α]:
    (ca_id α).trace = config_to_trace := by
    unfold trace
    funext t
    conv in comp _ => change nextt _

    have shift_next c : (ca_id α).next c = fun i => c (i + 1) := by
      funext i
      simp [CellAutomaton.next, ca_id]

    have shift_nextt k c i: ((ca_id α).nextt c k) i = c (i + k) := by
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



  def ca_id_word (α: Type) [Alphabet α] : CellAutomaton α？ α := (ca_id α？).map_project (·.getD default)

  @[simp]
  lemma ca_id_scan_temporal [Alphabet α]: (ca_id_word α).trace_rt = id := by
    funext w
    rw [id_eq, ca_id_word, trace_rt_of_map_project]
    apply List.ext_getElem (by simp)
    intro i h_i h_len
    unfold trace_rt
    simp [ca_id_trace_eq]
    grind [ca_id_trace_eq, config_to_trace]

end id



def ProdCA {α P γ: Type} [Alphabet P] (f: P → CellAutomaton α γ): CellAutomaton α (P → γ) := {
  Q := ∀ b: P, (f b).Q
  δ := fun qL qC qR a => (f a).δ (qL a) (qC a) (qR a)
  embed := fun a b => (f b).embed a
  project := fun q => (fun b => (f b).project (q b))
}

namespace ProdCA

  variable {α P γ: Type} [Alphabet P]
  variable {f: P → CellAutomaton α γ}

  @[simp, grind =]
  lemma comp [Alphabet γ] {f: P → CellAutomaton α γ}
      (w: Config α) (t: ℕ) (i: ℤ):
      (ProdCA f).comp w t i = fun b => (f b).comp w t i := by
    unfold CellAutomaton.comp CellAutomaton.project_config
    unfold CellAutomaton.nextt

    have nextt_proj (c: Config (ProdCA f).Q) (t: ℕ) (i: ℤ) (b: P):
        (ProdCA f).next^[t] c i b = (f b).next^[t] (fun j => c j b) i := by
      induction t generalizing i c with
      | zero => rfl
      | succ t ih =>
        rw [Function.iterate_succ]
        rw [Function.iterate_succ]
        dsimp
        rw [ih]
        dsimp [CellAutomaton.next, ProdCA]
        rfl

    funext b
    simp
    conv in (ProdCA f).project =>
      simp [ProdCA]
    rw [nextt_proj]
    congr


  -- zipMany over { x => [a, b, c], y => [1, 2, 3] } should be  [ {x => a, y => 1}, {x => b, y => 2}, {x => c, y => 3} ]

  def zipMany {γ: P -> Type v} [∀ b, Inhabited (γ b)] (f: (b: P) → Word (γ b)) : Word ((b: P) -> (γ b)) :=
    let n := (f default).length
    (List.range n).map fun i => fun b => (f b).getD i default

  lemma zipMany_get? {γ: P -> Type v} [∀ b, Inhabited (γ b)] (f: (b: P) → Word (γ b)) (i: ℕ):
      (ProdCA.zipMany f)[i]? = if i < (f default).length then some (fun b => (f b).getD i default) else none := by
    simp [zipMany]
    grind

  @[simp]
  lemma zipMany_get {γ: P -> Type v} [∀ b, Inhabited (γ b)] (w_b: (b: P) → Word (γ b)) (i: ℕ) (h: i < (ProdCA.zipMany w_b).length):
      (ProdCA.zipMany w_b)[i] = fun b => (w_b b).getD i default := by
    simp [zipMany]


  @[simp]
  lemma trace_rt [Alphabet γ] (f: P → CellAutomaton (Option α) γ) (w: Word α):
      (ProdCA f).trace_rt w = zipMany (fun b => (f b).trace_rt w) := by
    unfold CellAutomaton.trace_rt CellAutomaton.trace
    simp [zipMany]
    unfold embed_word
    intro t ht
    funext b
    grind

end ProdCA


def ca_zip {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
  (C1: CellAutomaton α β1) (C2: CellAutomaton α β2) :
    CellAutomaton α (β1 × β2) :=
  (ProdCA
    (fun
      | (0: Fin 2) => C1.map_project (fun v => (v, default))
      | (1: Fin 2) => C2.map_project (fun v => (default, v))
    )
  ).map_project (fun v => ((v 0).fst, (v 1).snd))


infixr:90 " ⨂ "  => ca_zip

@[simp]
lemma ca_zip_comp {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
    {C1: CellAutomaton α β1} {C2: CellAutomaton α β2} {c: Config α} {t: ℕ} {i: ℤ}:
    (C1 ⨂ C2).comp c t i = ((C1.comp c t i), (C2.comp c t i)) := by
  unfold ca_zip
  simp



@[simp]
lemma ca_zip_trace_rt {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
    {C1: CellAutomaton α？ β1} {C2: CellAutomaton α？ β2} {w: Word α}:
    (C1 ⨂ C2).trace_rt w = (C1.trace_rt w) ⨂ (C2.trace_rt w) := by
  unfold ca_zip
  simp
  apply List.ext_getElem?
  intro i
  simp [ProdCA.zipMany_get?]
  by_cases h: i < List.length w
  · simp [h, zip_words]
  · simp [h, zip_words]



/-

def word_dvd_k_ext (k: ℕ) (w_len: ℕ) := (w_len - (w_len % w_len)) % w_len

def word_dvd_k (k: ℕ) (w: Word α): Word (Option α) :=
  w.map (fun a => some a) ++ List.replicate (word_dvd_k_ext k w.length) none

def L_dvd_k (k: ℕ) (L: Language α): Language (Option α) := { word_dvd_k k w | w ∈ L }

theorem L_in_RT_iff_L_dvd_k_in_RT [Alphabet α] (k: ℕ) (L: Language α):
    L ∈ ℒ (CA_rt α) ↔ (L_dvd_k k L) ∈ ℒ (CA_rt (Option α)) := by
  sorry

-/



@[simp]
lemma map_project_comp {α β γ: Type} (C: CellAutomaton α β) (f: β → γ) (c: Config α) (t: ℕ):
  (C.map_project f).comp c t p = f (C.comp c t p) := by rfl

@[simp]
lemma map_project_trace_rt {α β γ: Type} (C: CellAutomaton α？ β) (f: β → γ) (w: Word α):
    (C.map_project f).trace_rt w = (C.trace_rt w).map f := by
  apply List.ext_getElem
  · simp
  · simp




@[simp]
lemma nextt0 (C: CellAutomaton α β) (c: Config C.Q): C.nextt c 0 = c := by simp [CellAutomaton.nextt]

@[simp]
lemma nextt1 (C: CellAutomaton α β) (c: Config C.Q): C.nextt c 1 = C.next c := by simp [CellAutomaton.nextt]

/-
lemma LCellAutomaton.embed_word_eq (C: LCellAutomaton α) {w: Word α} {p: ℤ} (h: p ∈ w.range):
    C.embed_word w p = C.embed (w.get' p h) := by
      grind [LCellAutomaton.embed_word, Word.get']
-/


lemma LCellAutomaton.nextt_succ_eq (C: LCellAutomaton α) (c: Config C.Q): C.nextt c (t + 1) = C.next (C.nextt c t) := by
  simp


/-
lemma LCellAutomaton.comp_succ_eq (C: LCellAutomaton α): C.comp w (t + 1) = C.next (C.comp w t) := by
  funext i
  simp [LCellAutomaton.comp, LCellAutomaton.nextt_succ_eq]
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
lemma map_embed_L {α} (C: tCellAutomaton α) (f: β → α) (w: Word β):
    w ∈ (C.map_embed f).L ↔ (w.map f) ∈ C.L := by

  suffices @embed_word α Bool C.toCellAutomaton (w.map f)
      = @embed_word β Bool (C.map_embed f).toCellAutomaton w by
    rw [tCellAutomaton.elem_L_iff]
    rw [tCellAutomaton.elem_L_iff]
    rw [this]
    simp
    rfl
  unfold embed_word embed_config
  funext p
  unfold word_to_config
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
    unfold zip_words
    rw [<-List.zip]
    rw [List.map_fst_zip]
    simp


lemma CArtWithAdvice_eq_CArt_iff (adv: Advice α Γ):
    ℒ (CA_rt (α ⨉ Γ) + adv) = ℒ (CA_rt α)
    ↔ ∀ L ∈ ℒ (CA_rt (α ⨉ Γ) + adv), L ∈ ℒ (CA_rt α) := by
  grind [CA_rt_subseteq_CA_rt_with_advice]






  section
    lemma embed_word_at_eq {α β: Type} (w: Word α) {C: CellAutomaton α？ β} (p: ℤ):
        @embed_word α β C w p = C.embed (if h: p ∈ w.range then  (some (w.get' p h)) else none) := by rfl

    @[simp]
    lemma embed_word_at_eq1 {α β: Type} (w: Word α) {C: CellAutomaton α？ β} (p: ℤ) (h: p ∈ w.range):
        @embed_word α β C w p = C.embed (some (w.get' p h)) := by simp [embed_word_at_eq, h]

    @[simp]
    lemma embed_word_at_eq2 {α β: Type} (w: Word α) {C: CellAutomaton α？ β} (p: ℤ) (h: ¬(p ∈ w.range)):
        @embed_word α β C w p = C.embed none := by simp [embed_word_at_eq, h]

  end

  @[simp]
  lemma project_config_at {α β: Type} [Alphabet α] [Alphabet β] {C: CellAutomaton α？ β} (p: ℤ) {c: Config C.Q}:
    C.project_config c p = C.project (c p) := by rfl

  lemma comp_word_eq_project_nextt {α β: Type} {C: CellAutomaton α？ β} (w: Word α) (t: ℕ):
      C.comp w t = C.project_config (C.nextt w t) := by rfl

  lemma comp_config_eq_project_nextt {α β: Type} {C: CellAutomaton α β} (c: Config α) (t: ℕ):
      C.comp c t = C.project_config (C.nextt c t) := by rfl






@[simp]
lemma Word.get'_eq {α} (w: Word α) (i: ℕ) (h: i < w.length) (val: α): (w.get'? ↑i).getD val = w[i] := by
  unfold Word.get'?
  by_cases h: ↑↑i ∈ w.range
  simp [h, Word.get']
  simp_all [Word.range]



@[simp]
lemma adv_empty {α} {Γ} (adv : Advice α Γ) : adv.f [] = [] := by
  have h_len : (adv.f []).length = 0 := by simp [adv.len]
  simp [←List.length_eq_zero_iff]

@[simp]
lemma adv_empty_2 {α} {Γ} (adv : Advice α Γ) (w: Word α): adv.f w = [] ↔ w = [] := by
  simp [←List.length_eq_zero_iff]

@[simp]
lemma zip_length {α β} (w1: Word α) (w2: Word β):
    (w1 ⨂ w2).length = Nat.min w1.length w2.length := by
  simp [zip_words]


@[simp]
lemma adv_cannot_empty_2 {α} {Γ} (adv : Advice α Γ) (w: Word α): adv.annotate w = [] ↔ w = [] := by
  unfold Advice.annotate
  simp [←List.length_eq_zero_iff]


lemma advice_eq_iff {α} {Γ} {adv1 adv2: Advice α Γ} (h: adv1.f = adv2.f): adv1 = adv2 := by
  cases adv1
  cases adv2
  simp at h
  subst h
  rfl



section

  variable {α β: Type} (w: Word (α × β))

  def Word.fst: Word α := w.map Prod.fst
  def Word.snd: Word β := w.map Prod.snd

  @[simp] lemma Word.fst_len: (w.fst).length = w.length := by simp [Word.fst]
  @[simp] lemma Word.snd_len: (w.snd).length = w.length := by simp [Word.snd]

  @[simp] lemma Word.get_fst (t: Fin w.length): (w.fst)[t] = w[t].1 := by simp [Word.fst]
  @[simp] lemma Word.get_snd (t: Fin w.length): (w.snd)[t] = w[t].2 := by simp [Word.snd]

  @[simp] lemma Word.get_fst_ (t: ℕ) (h: t < (w.fst).length): (w.fst)[t]'h = ((w[t]'(by simp_all)).1) := by simp [Word.fst]
  @[simp] lemma Word.get_snd_ (t: ℕ) (h: t < (w.snd).length): (w.snd)[t]'h = ((w[t]'(by simp_all)).2) := by simp [Word.snd]

  @[simp] lemma Word.fst_empty: @Word.fst α β [] = [] := by simp [Word.fst]
  @[simp] lemma Word.snd_empty: @Word.snd α β [] = [] := by simp [Word.snd]

  @[simp] lemma Word.cons_fst (a: α × β) (w: Word (α × β)): Word.fst (a :: w) = a.1 :: (Word.fst w) := by simp [Word.fst]
  @[simp] lemma Word.cons_snd (a: α × β) (w: Word (α × β)): Word.snd (a :: w) = a.2 :: (Word.snd w) := by simp [Word.snd]

  @[simp] lemma Word.zip_fst (w1: Word α) (w2: Word β) (h: w1.length = w2.length): (w1 ⨂ w2).fst = w1 := by
    induction w1 generalizing w2 with
    | nil =>
      cases w2
      · rfl
      · contradiction
    | cons a w1 ih =>
      cases w2 with
      | nil => contradiction
      | cons b w2 =>
        simp [zip_words, Word.cons_fst]
        simp at h
        specialize ih w2 h
        simp [zip_words] at ih
        exact ih

  @[simp] lemma Word.zip_snd (w1: Word α) (w2: Word β) (h: w1.length = w2.length): (w1 ⨂ w2).snd = w2 := by
    induction w1 generalizing w2 with
    | nil =>
      cases w2
      · rfl
      · contradiction
    | cons a w1 ih =>
      cases w2 with
      | nil => contradiction
      | cons b w2 =>
        simp [zip_words, Word.cons_snd]
        simp at h
        specialize ih w2 h
        simp [zip_words] at ih
        exact ih

end
