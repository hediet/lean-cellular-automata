import CellularAutomatas.proofs.word_ops

namespace CellularAutomatas.MarkedPrefix

/-- A choice of prefix length which never exceeds the ambient word length. -/
structure BoundedSelector where
  select : ℕ → ℕ
  bound : ∀ n, select n ≤ n

instance : CoeFun BoundedSelector (fun _ => ℕ → ℕ) where
  coe l := l.select

@[simp]
theorem BoundedSelector.coe_apply (l : BoundedSelector) (n : ℕ) :
    l n = l.select n := rfl

variable {α β γ : Type}

/-- Run `F` on the selected prefix and fill the rest of the word with `blank`. -/
def prefixTransform (l : BoundedSelector) (F : Advice α β) (blank : β) :
    Advice α β where
  f w :=
    F (w.take (l w.length)) ++
      List.replicate (w.length - l w.length) blank
  len w := by
    have hbound := l.bound w.length
    simp only [List.length_append, advice_len, List.length_take,
      List.length_replicate]
    rw [Nat.min_eq_left hbound]
    omega

@[simp]
theorem prefixTransform_apply (l : BoundedSelector) (F : Advice α β)
    (blank : β) (w : Word α) :
    prefixTransform l F blank w =
      F (w.take (l w.length)) ++
        List.replicate (w.length - l w.length) blank := rfl

@[simp]
theorem prefixTransform_length (l : BoundedSelector) (F : Advice α β)
    (blank : β) (w : Word α) :
    (prefixTransform l F blank w).length = w.length :=
  advice_len (prefixTransform l F blank) w

@[simp]
theorem selectedPrefix_length (l : BoundedSelector) (w : Word α) :
    (w.take (l w.length)).length = l w.length := by
  rw [List.length_take, Nat.min_eq_left (l.bound w.length)]

/-- The selected output block is exactly the advice on the selected input prefix. -/
@[simp]
theorem prefixTransform_take_selected (l : BoundedSelector) (F : Advice α β)
    (blank : β) (w : Word α) :
    (prefixTransform l F blank w).take (l w.length) =
      F (w.take (l w.length)) := by
  rw [prefixTransform_apply]
  apply List.take_left'
  calc
    (F (w.take (l w.length))).length =
        (w.take (l w.length)).length := advice_len F _
    _ = l w.length := selectedPrefix_length l w

/-- The complementary output block consists only of padding. -/
@[simp]
theorem prefixTransform_drop_selected (l : BoundedSelector) (F : Advice α β)
    (blank : β) (w : Word α) :
    (prefixTransform l F blank w).drop (l w.length) =
      List.replicate (w.length - l w.length) blank := by
  rw [prefixTransform_apply]
  apply List.drop_left'
  calc
    (F (w.take (l w.length))).length =
        (w.take (l w.length)).length := advice_len F _
    _ = l w.length := selectedPrefix_length l w

/-- The transform is the standard right-padding operation applied to its useful block. -/
theorem prefixTransform_eq_rightpad (l : BoundedSelector) (F : Advice α β)
    (blank : β) (w : Word α) :
    prefixTransform l F blank w =
      List.rightpad w.length blank (F (w.take (l w.length))) := by
  simp only [List.rightpad, prefixTransform_apply, advice_len,
    selectedPrefix_length]

theorem prefixTransform_getElem?_of_lt_selected (l : BoundedSelector)
    (F : Advice α β) (blank : β) (w : Word α) (i : ℕ)
    (hi : i < l w.length) :
    (prefixTransform l F blank w)[i]? =
      (F (w.take (l w.length)))[i]? := by
  rw [prefixTransform_apply]
  have hprefix :
      (F (w.take (l w.length))).length = l w.length := by
    calc
      (F (w.take (l w.length))).length =
          (w.take (l w.length)).length := advice_len F _
      _ = l w.length := selectedPrefix_length l w
  apply List.getElem?_append_left
  rw [hprefix]
  exact hi

theorem prefixTransform_getElem?_of_selected_le (l : BoundedSelector)
    (F : Advice α β) (blank : β) (w : Word α) (i : ℕ)
    (hselected : l w.length ≤ i) (hi : i < w.length) :
    (prefixTransform l F blank w)[i]? = some blank := by
  rw [prefixTransform_apply]
  have hprefix :
      (F (w.take (l w.length))).length = l w.length := by
    calc
      (F (w.take (l w.length))).length =
          (w.take (l w.length)).length := advice_len F _
      _ = l w.length := selectedPrefix_length l w
  rw [List.getElem?_append_right (by simpa only [hprefix] using hselected)]
  apply List.getElem?_replicate_of_lt
  rw [hprefix]
  omega

/-- Pointwise specification on every in-range output position. -/
theorem prefixTransform_getElem?_spec (l : BoundedSelector) (F : Advice α β)
    (blank : β) (w : Word α) (i : ℕ) (hi : i < w.length) :
    (prefixTransform l F blank w)[i]? =
      if i < l w.length then
        (F (w.take (l w.length)))[i]?
      else
        some blank := by
  split
  · exact prefixTransform_getElem?_of_lt_selected l F blank w i ‹_›
  · exact prefixTransform_getElem?_of_selected_le l F blank w i
      (Nat.le_of_not_gt ‹_›) hi

/-- Prefix transformation is exactly closed under composition when both
stages use the same selector. The first-stage padding is never observed. -/
theorem prefixTransform_compose (l : BoundedSelector)
    (F : Advice α β) (G : Advice β γ) (blank₁ : β) (blank₂ : γ) :
    Advice.compose (prefixTransform l F blank₁)
        (prefixTransform l G blank₂) =
      prefixTransform l (Advice.compose F G) blank₂ := by
  apply advice_eq_iff
  funext w
  change
    prefixTransform l G blank₂ (prefixTransform l F blank₁ w) =
      prefixTransform l (Advice.compose F G) blank₂ w
  calc
    prefixTransform l G blank₂ (prefixTransform l F blank₁ w)
        = G ((prefixTransform l F blank₁ w).take (l w.length)) ++
            List.replicate (w.length - l w.length) blank₂ := by
          rw [prefixTransform_apply, prefixTransform_length]
    _ = G (F (w.take (l w.length))) ++
          List.replicate (w.length - l w.length) blank₂ := by
        rw [prefixTransform_take_selected]
    _ = prefixTransform l (Advice.compose F G) blank₂ w := rfl

end CellularAutomatas.MarkedPrefix
