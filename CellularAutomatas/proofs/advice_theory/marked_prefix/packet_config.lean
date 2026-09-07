import CellularAutomatas.proofs.advice_theory.marked_prefix.prefix_transform
import CellularAutomatas.proofs.constructions.speedup_compressed

namespace CellularAutomatas.MarkedPrefix

variable {α Γ : Type}

/-- Advice padding never turns an absent ordinary input symbol into an
interior cell of the simulated automaton. -/
theorem annotated_config_eq (adv : Advice α Γ) (blank : Γ)
    (w : Word α) (p : ℤ) :
    word_to_config (adv.annotate w) p =
      (word_to_config w p).map
        (fun a => (a, (word_to_config (adv w) p).getD blank)) := by
  by_cases hp : 0 ≤ p ∧ p < (w.length : ℤ)
  · show word_to_config (adv.annotate w) p = _
    simp [Advice.annotate, word_to_config, hp]
  · show word_to_config (adv.annotate w) p = _
    simp [Advice.annotate, word_to_config, hp]

def adviceBlock (adv : Advice α Γ) (blank : Γ) (w : Word α)
    (p : ℤ) : Fin 3 → Γ :=
  fun r => (word_to_config (adv w) (p * 3 + (r.val : ℤ))).getD blank

def joinBlock (raw : Fin 3 → Option α) (advice : Fin 3 → Γ) :
    Fin 3 → Option (α × Γ) :=
  fun r => (raw r).map (fun a => (a, advice r))

theorem joinBlock_eq_compressed_annotation (adv : Advice α Γ) (blank : Γ)
    (w : Word α) (p : ℤ) :
    joinBlock (SpeedupKx.compress 3 (word_to_config w) p)
        (adviceBlock adv blank w p) =
      SpeedupKx.compress 3 (word_to_config (adv.annotate w)) p := by
  funext r
  show (word_to_config w (p * 3 + (r.val : ℤ))).map
      (fun a => (a, (word_to_config (adv w) (p * 3 + (r.val : ℤ))).getD blank)) =
    word_to_config (adv.annotate w) (p * 3 + (r.val : ℤ))
  exact (annotated_config_eq adv blank w _).symm

/-- Extending a transformed prefix with its padding symbol has the same
defaulted configuration as extending that prefix with absent cells. -/
theorem prefixTransform_config_getD (l : BoundedSelector) (F : Advice α Γ)
    (blank : Γ) (w : Word α) (p : ℤ) :
    (word_to_config (prefixTransform l F blank w) p).getD blank =
      (word_to_config (F (w.take (l w.length))) p).getD blank := by
  have hprefix : (F (w.take (l w.length))).length = l w.length :=
    calc
      (F (w.take (l w.length))).length = (w.take (l w.length)).length := advice_len F _
      _ = l w.length := selectedPrefix_length l w
  by_cases hp : 0 ≤ p ∧ p < (l w.length : ℤ)
  · show (word_to_config (prefixTransform l F blank w) p).getD blank =
      (word_to_config (F (w.take (l w.length))) p).getD blank
    have hword : 0 ≤ p ∧ p < (w.length : ℤ) := by
      have hbound := l.bound w.length
      omega
    have hindex : p.toNat < l w.length := by omega
    have hentry := prefixTransform_getElem?_of_lt_selected l F blank w p.toNat hindex
    have hleft : p.toNat < (prefixTransform l F blank w).length := by
      simp only [prefixTransform_length]
      omega
    have hright : p.toNat < (F (w.take (l w.length))).length := by omega
    rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hentry
    simp only [word_to_config, prefixTransform_length, hprefix,
      dif_pos hp, dif_pos hword, Option.getD_some]
    exact Option.some.inj hentry
  · by_cases hword : 0 ≤ p ∧ p < (w.length : ℤ)
    · show (word_to_config (prefixTransform l F blank w) p).getD blank =
        (word_to_config (F (w.take (l w.length))) p).getD blank
      have hselected : l w.length ≤ p.toNat := by omega
      have hindex : p.toNat < w.length := by omega
      have hentry := prefixTransform_getElem?_of_selected_le l F blank w p.toNat
        hselected hindex
      have hleft : p.toNat < (prefixTransform l F blank w).length := by
        rw [prefixTransform_length]
        exact hindex
      rw [List.getElem?_eq_getElem hleft] at hentry
      simp only [word_to_config, prefixTransform_length, hprefix,
        dif_pos hword, dif_neg hp, Option.getD_some, Option.getD_none]
      exact Option.some.inj hentry
    · show (word_to_config (prefixTransform l F blank w) p).getD blank =
        (word_to_config (F (w.take (l w.length))) p).getD blank
      simp only [word_to_config, prefixTransform_length, hprefix,
        dif_neg hp, dif_neg hword, Option.getD_none]

theorem prefixTransform_adviceBlock (l : BoundedSelector) (F : Advice α Γ)
    (blank : Γ) (w : Word α) (p : ℤ) :
    adviceBlock (prefixTransform l F blank) blank w p =
      fun r : Fin 3 =>
        (word_to_config (F (w.take (l w.length)))
          (p * 3 + (r.val : ℤ))).getD blank := by
  funext r
  exact prefixTransform_config_getD l F blank w _

end CellularAutomatas.MarkedPrefix
