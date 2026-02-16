import CellularAutomatas.defs
import CellularAutomatas.proofs.find_some

namespace CellularAutomatas
@[simp]
lemma nextt0 (C: CellAutomaton) (c: Config C.Q): C.nextt c 0 = c := by simp [CellAutomaton.nextt, apply_iterated]

@[simp]
lemma nextt1 (C: CellAutomaton) (c: Config C.Q): C.nextt c 1 = C.next c := by simp [CellAutomaton.nextt, apply_iterated]


@[simp]
lemma LCellAutomaton.comp_zero {C: LCellAutomaton α} {w}: C.comp w 0 = C.embed_word w := by rfl

lemma LCellAutomaton.embed_word_eq (C: LCellAutomaton α) {w: Word α} {p: ℤ} (h: p ∈ w.range):
    C.embed_word w p = C.embed (w.get' p h) := by
      grind [LCellAutomaton.embed_word, Word.get']

lemma LCellAutomaton.nextt_succ_eq (C: LCellAutomaton α) (c: Config C.Q): C.nextt c (t + 1) = C.next (C.nextt c t) := by
  simp [CellAutomaton.nextt, apply_iterated_succ_apply']



lemma LCellAutomaton.comp_succ_eq (C: LCellAutomaton α): C.comp w (t + 1) = C.next (C.comp w t) := by
  funext i
  simp [LCellAutomaton.comp, LCellAutomaton.nextt_succ_eq]



lemma δδt_succ {C: CellAutomaton} {q: C.Q} {t: ℕ} : δδt q (t + 1) = δδ (δδt q t) := by
  simp [δδt, apply_iterated_succ_apply']

@[simp]
lemma δδt_zero {C: CellAutomaton} {q: C.Q} : δδt q 0 = q := by
  simp [δδt]

lemma CellAutomaton.δδ_of_quiescent {C: CellAutomaton} {q: C.Q} (h: C.quiescent q): δδ q = q := by
  simp_all [δδ, CellAutomaton.quiescent, CellAutomaton.quiescent_set]

lemma CellAutomaton.δ_of_quiescent {C: CellAutomaton} {q: C.Q} (h: C.quiescent q): C.δ q q q = q := by
  simp_all [CellAutomaton.quiescent, CellAutomaton.quiescent_set]

lemma CellAutomaton.δδ_of_quiescent2 {C: CellAutomaton} {q: C.Q} (h: C.quiescent q): δδ q = q := by
  simp_all [δδ, CellAutomaton.δ_of_quiescent]

lemma CellAutomaton.delta_of_dead {C: CellAutomaton} {b: C.Q} (h: C.dead b) (a c: C.Q): C.δ a b c = b := by
  simp_all [CellAutomaton.dead, CellAutomaton.delta_closed_set]



lemma CellAutomaton.next_state_of_closed_set_state
  {C: CellAutomaton} {S} {c: Config C.Q} {i} (h1: C.delta_closed_set S) (h2: c i ∈ S):
    C.next c i ∈ S := by
  unfold CellAutomaton.next
  unfold CellAutomaton.delta_closed_set at h1
  exact h1 (c (i - 1)) ⟨c i, h2⟩ (c (i + 1))


lemma CellAutomaton.quiescent_of_dead {C: CellAutomaton} {q: C.Q} (h: C.dead q): C.quiescent q := by
  unfold CellAutomaton.quiescent
  intro a b c
  unfold CellAutomaton.dead at h
  unfold CellAutomaton.delta_closed_set at h
  simp_all only [Set.mem_singleton_iff, Subtype.forall, forall_eq]
  obtain ⟨a, a_h⟩ := a
  obtain ⟨b, b_h⟩ := b
  obtain ⟨c, c_h⟩ := c
  simp_all only
  simp_all only [Set.mem_singleton_iff]



def uniform_config {C: CellAutomaton} (q: C.Q): Config C.Q := fun _ => q

@[simp]
lemma uniform_config_at_eq {C: CellAutomaton} (q: C.Q) (i: ℤ): uniform_config q i = q := by rfl








@[simp]
lemma empty_word_range: @Word.range α [] = {} := by
  unfold Word.range
  ext x
  simp_all



def Word.cone (w: Word α) (t: ℕ): Set ℤ := { i: ℤ | -t ≤ i ∧ i < w.length + t }

instance (w: Word α) (t: ℕ) (i: ℤ) [d: Decidable (i ∈ { i: ℤ | -t ≤ i ∧ i < w.length + t })]:
  Decidable (i ∈ (Word.cone w t)) := d

section
  variable {w: Word α}

  lemma Word.cone_prop {t: ℕ} {i: ℤ} (d: ℤ) (h: i ∉ w.cone (t + 1)) (h2: d.natAbs ≤ 1): (i + d) ∉ w.cone t := by
    simp_all [Word.cone]
    omega

  lemma Word.cone_prop' {t: ℕ} {i: ℤ} { d: ℤ } (h: (i + d) ∈ w.cone t) (h2: d.natAbs ≤ 1): i ∈ w.cone (t + 1) := by
    simp_all [Word.cone]
    omega

  lemma Word.cone_prop'' {t: ℕ} {i: ℤ} (h: i ∈ w.cone t): i ∈ w.cone (t + 1) := by
    simp_all [Word.cone]
    omega


  lemma Word.cone_succ {t: ℕ} {i: ℤ} (h1: i - 1 ∈ w.cone t) (h2: i + 1 ∈ w.cone t): i ∈ w.cone (t + 1) := by
    simp_all [Word.cone]
    omega

  lemma Word.cone_succ_not {t: ℕ} {i: ℤ} (wlen: w.length > 0) (h1: i - 1 ∉ w.cone t) (h2: i ∉ w.cone t) (h3: i + 1 ∉ w.cone t): i ∉ w.cone (t + 1) := by
    simp_all [cone]
    omega

  @[simp]
  lemma Word.cone_zero_eq_range: w.cone 0 = w.range := by simp [Word.cone, Word.range]

  def Word.get_cone_0 {i} (h: i ∈ w.cone 0) := w.get' i (Word.cone_zero_eq_range ▸ h)

  lemma Word.zero_mem_cone (h: w.length > 0) (t): 0 ∈ w.cone t := by
    simp [Word.cone]
    omega
end



section
  variable {C: LCellAutomaton α}
  variable {w: Word α}



  lemma LCellAutomaton.empty_word_config_eq_uniform_border: C.embed_word [] = uniform_config C.border := by
    funext i
    simp [LCellAutomaton.embed_word, uniform_config, uniform_config]



  lemma LCellAutomaton.uniform_state_eq {q: C.Q}: C.nextt (uniform_config q) = uniform_config ∘ (δδt q) := by
    funext t i
    simp only [CellAutomaton.nextt, δδt, Function.comp_apply, uniform_config]

    induction t generalizing i
    case h.h.zero =>
      simp [uniform_config, apply_iterated_zero]
    case h.h.succ n ih =>
      simp [apply_iterated_succ_apply', ih, δδ, CellAutomaton.next]

  lemma LCellAutomaton.comp_empty_eq_uniform: C.comp [] = uniform_config ∘ (δδt C.border) := by
    simp [LCellAutomaton.comp, LCellAutomaton.empty_word_config_eq_uniform_border, LCellAutomaton.uniform_state_eq]



  lemma LCellAutomaton.embed_word_eq_embed {i} (h: i ∈ w.cone 0): C.embed_word w i = C.embed (w.get_cone_0 h) := by
    rw [Word.cone_zero_eq_range] at h
    simp_all [LCellAutomaton.embed_word, Word.get_cone_0]






  lemma LCellAutomaton.comp_outside_word_cone_eq_border_pow_t {t: ℕ} {i: ℤ} (h: i ∉ w.cone t):
      C.comp w t i = δδt C.border t := by

    induction t generalizing i
    case zero =>
      simp_all [LCellAutomaton.comp, CellAutomaton.nextt, δδt, LCellAutomaton.embed_word, Word.cone_zero_eq_range]
    case succ t ih =>
      have h1 := ih $ Word.cone_prop 0 h (by simp)
      have h2 := ih $ Word.cone_prop (-1) h (by simp)
      have h3 := ih $ Word.cone_prop 1 h (by simp)
      have x: (i + -1) = i - 1 := by rfl

      rw [LCellAutomaton.comp_succ_eq]
      rw [δδt_succ]
      set c := C.comp w t
      simp_all [CellAutomaton.next, δδ]

end
