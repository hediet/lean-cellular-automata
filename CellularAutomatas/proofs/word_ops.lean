import CellularAutomatas.defs

namespace CellularAutomatas


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
  simp [List.zip]


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

  @[simp] lemma Word.zip_fst (w1: Word α) (w2: Word β) (h: w1.length = w2.length): Word.fst (w1 ⨂ w2) = w1 := by
    induction w1 generalizing w2 with
    | nil =>
      cases w2
      · rfl
      · contradiction
    | cons a w1 ih =>
      cases w2 with
      | nil => contradiction
      | cons b w2 =>
        simp
        simp at h
        exact ih w2 h

  @[simp] lemma Word.zip_snd (w1: Word α) (w2: Word β) (h: w1.length = w2.length): Word.snd (w1 ⨂ w2) = w2 := by
    induction w1 generalizing w2 with
    | nil =>
      cases w2
      · rfl
      · contradiction
    | cons a w1 ih =>
      cases w2 with
      | nil => contradiction
      | cons b w2 =>
        simp
        simp at h
        exact ih w2 h

end

end CellularAutomatas
