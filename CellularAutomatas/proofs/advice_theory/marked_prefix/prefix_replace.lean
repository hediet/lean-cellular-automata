import CellularAutomatas.proofs.advice_theory.marked_prefix.lt
import CellularAutomatas.proofs.advice_theory.marked_prefix.retain_input
import CellularAutomatas.proofs.advice_theory.time_advice_combinators

namespace CellularAutomatas.MarkedPrefix

variable {α : Type} [Alphabet α]

/-- Replace the selected prefix and preserve the original suffix. Unlike
blank padding, this operation does not discard the unselected input. -/
def prefixReplace (selector : BoundedSelector) (F : Advice α α) : Advice α α where
  f w := F (w.take (selector w.length)) ++ w.drop (selector w.length)
  len w := by
    have hbound := selector.bound w.length
    simp only [List.length_append, advice_len, List.length_take, List.length_drop]
    omega

omit [Alphabet α] in
@[simp] theorem prefixReplace_take_selected (selector : BoundedSelector)
    (F : Advice α α) (w : Word α) :
    (prefixReplace selector F w).take (selector w.length) =
      F (w.take (selector w.length)) := by
  apply List.take_left'
  rw [advice_len, selectedPrefix_length]

omit [Alphabet α] in
@[simp] theorem prefixReplace_drop_selected (selector : BoundedSelector)
    (F : Advice α α) (w : Word α) :
    (prefixReplace selector F w).drop (selector w.length) =
      w.drop (selector w.length) := by
  apply List.drop_left'
  rw [advice_len, selectedPrefix_length]

omit [Alphabet α] in
/-- Suffix-preserving prefix operations have a genuine identity operation. -/
theorem prefixReplace_identity (selector : BoundedSelector) :
    prefixReplace selector (Advice.identity α) = Advice.identity α := by
  apply advice_eq_iff
  funext w
  exact List.take_append_drop (selector w.length) w

/-- Consecutive prefix replacements combine without changing the selector or
the untouched suffix. This alone does not commute a two-stage factor past them. -/
theorem prefixReplace_compose (selector : BoundedSelector)
    (F G : Advice α α) :
    (prefixReplace selector F).compose (prefixReplace selector G) =
      prefixReplace selector (F.compose G) := by
  apply advice_eq_iff
  funext w
  change
    G ((prefixReplace selector F w).take
        (selector (prefixReplace selector F w).length)) ++
        (prefixReplace selector F w).drop
          (selector (prefixReplace selector F w).length) =
      G (F (w.take (selector w.length))) ++ w.drop (selector w.length)
  rw [advice_len, prefixReplace_take_selected, prefixReplace_drop_selected]

private def restoreSuffix : CArtTransducer (α × Option α) α :=
  (ca_trace_id_word (α × Option α)).map_project
    (fun pair => pair.2.getD pair.1)

private theorem restoreSuffix_apply (w : Word (α × Option α)) :
    restoreSuffix.advice w = w.map (fun pair => pair.2.getD pair.1) := by
  simp [restoreSuffix, CArtTransducer.advice, trace_rt_of_map_project,
    ca_trace_id_scan_temporal]

/-- Tagging transformed symbols separates a legitimate output value from the
absence of transformed output. A pointwise decoder then restores the suffix. -/
theorem prefixReplace_eq_decode (selector : BoundedSelector) (F : Advice α α) :
    ((prefixTransform selector (Advice.map some F) none).retainInput.compose
      restoreSuffix.advice) = prefixReplace selector F := by
  apply advice_eq_iff
  funext w
  change restoreSuffix.advice
    ((prefixTransform selector (Advice.map some F) none).retainInput w) = _
  rw [restoreSuffix_apply, Advice.retainInput_apply]
  have hbound := selector.bound w.length
  apply List.ext_getElem
  · simp [prefixReplace, Nat.min_eq_left hbound, Nat.add_sub_of_le hbound]
  · intro i hi hj
    have hin : i < w.length := by
      simpa [Nat.min_eq_left hbound, Nat.add_sub_of_le hbound] using hi
    have hprefix : (F (w.take (selector w.length))).length =
        selector w.length := by
      rw [advice_len, selectedPrefix_length]
    simp only [List.getElem_map, List.getElem_zip]
    by_cases hselected : i < selector w.length
    · have hentry :=
        prefixTransform_getElem?_of_lt_selected selector (Advice.map some F)
          none w i hselected
      have houtput : i < (prefixTransform selector (Advice.map some F) none w).length :=
        by simpa [Nat.min_eq_left hbound, Nat.add_sub_of_le hbound] using hin
      have htransformed : i < (F (w.take (selector w.length))).length := by
        simpa only [hprefix] using hselected
      simp only [List.getElem?_eq_getElem houtput, Advice.map_apply,
        List.getElem?_map, List.getElem?_eq_getElem htransformed,
        Option.map_some, Option.some.injEq] at hentry
      rw [hentry]
      change (F (w.take (selector w.length)))[i] =
        (F (w.take (selector w.length)) ++ w.drop (selector w.length))[i]
      rw [List.getElem_append_left htransformed]
    · have hentry :=
        prefixTransform_getElem?_of_selected_le selector (Advice.map some F)
          none w i (by omega) hin
      have houtput : i < (prefixTransform selector (Advice.map some F) none w).length :=
        by simpa [Nat.min_eq_left hbound, Nat.add_sub_of_le hbound] using hin
      simp only [List.getElem?_eq_getElem houtput, Option.some.injEq] at hentry
      rw [hentry]
      change w[i] =
        (F (w.take (selector w.length)) ++ w.drop (selector w.length))[i]
      rw [List.getElem_append_right (by omega :
        (F (w.take (selector w.length))).length ≤ i)]
      simp only [hprefix, List.getElem_drop]
      congr 1
      omega

/-- The suffix-preserving version is also strongly RT-closed; it uses the
already-proved padded transform and the freely retained original input. -/
noncomputable def dyadicPrefixReplace_rt_closed
    (F : Advice α α) (hF : F.IsLtAdvice) :
    (prefixReplace dyadicSelector F).rt_closed := by
  let optional : (Advice.map some F).IsLtAdvice :=
    ⟨hF.c, hF.witness.map some⟩
  rw [← prefixReplace_eq_decode]
  apply Advice.rt_closed_compose_rt_closed
  · exact Advice.rt_closed_retainInput _
      (dyadicPrefixTransform_rt_closed (Advice.map some F) optional none)
  · exact cart_is_rt_closed restoreSuffix

end CellularAutomatas.MarkedPrefix
