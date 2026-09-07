import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_config
import CellularAutomatas.proofs.advice_theory.marked_prefix.selector_marker

namespace CellularAutomatas.MarkedPrefix

variable {α β Γ : Type} [Alphabet β]

/-- A length-dependent selector is unchanged by retaining extra input tracks. -/
theorem prefixTransform_lift (l : BoundedSelector) (F : Advice α Γ)
    (blank : Γ) (π : β → α) :
    (prefixTransform l F blank).lift π =
      prefixTransform l (F.lift π) blank := by
  apply advice_eq_iff
  funext w
  simp [Advice.lift, prefixTransform]

theorem adviceBlock_lift (adv : Advice α Γ) (blank : Γ) (π : β → α)
    (w : Word β) (p : ℤ) :
    adviceBlock (adv.lift π) blank w p =
      adviceBlock adv blank (w.map π) p := rfl

theorem annotate_lift_map (adv : Advice α Γ) (π : β → α) (w : Word β) :
    ((adv.lift π).annotate w).map (fun pair => (π pair.1, pair.2)) =
      adv.annotate (w.map π) := by
  apply List.ext_getElem
  · show (((adv.lift π).annotate w).map
        (fun pair => (π pair.1, pair.2))).length =
      (adv.annotate (w.map π)).length
    simp [Advice.annotate]
  · intro i hi hj
    show (((adv.lift π).annotate w).map
        (fun pair => (π pair.1, pair.2)))[i] =
      (adv.annotate (w.map π))[i]
    simp [Advice.annotate, Advice.lift]

theorem word_to_config_map_some_getD (w : Word α) (p : ℤ) :
    (word_to_config (w.map some) p).getD none = word_to_config w p := by
  by_cases hp : 0 ≤ p ∧ p < (w.length : ℤ)
  · show (word_to_config (w.map some) p).getD none = word_to_config w p
    simp [word_to_config, hp]
  · show (word_to_config (w.map some) p).getD none = word_to_config w p
    simp [word_to_config, hp]

/-- A reversed-prefix producer only sees the projected input, while the raw
packet keeps the entire input alphabet for the eventual consumer. -/
theorem prefixReversal_adviceBlock_lift (l : BoundedSelector) (π : β → α)
    (w : Word β) (p : ℤ) :
    adviceBlock ((prefixReversal l).lift π) none w p =
      SpeedupKx.compress 3
        (word_to_config (((w.map π).take (l w.length)).reverse)) p := by
  rw [adviceBlock_lift]
  change adviceBlock (prefixTransform l (optionalReversal α) none)
    none (w.map π) p = _
  rw [prefixTransform_adviceBlock]
  funext r
  simpa only [optionalReversal_apply, List.length_map, SpeedupKx.compress] using
    word_to_config_map_some_getD
      (((w.map π).take (l w.length)).reverse) (p * 3 + (r.val : ℤ))

theorem middle_exp_lift_eq (π : β → α) :
    (Advice.middle_exp α).lift π = Advice.middle_exp β := by
  apply advice_eq_iff
  funext w
  simp [Advice.lift, Advice.middle_exp, Advice.from_len_marker,
    Advice.from_marker]

end CellularAutomatas.MarkedPrefix
