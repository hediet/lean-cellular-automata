import CellularAutomatas.proofs.advice_theory.rt_disclosure_observability

/-!
# Removing the probe layer: the causal first stage

A `FreeProbe` is *nothing but* a causal advice in disguise.

* `Advice.FreeProbe.disclosure_causal` (elsewhere) says every prefix diary is causal.
* `Advice.FreeProbe.ofCausal_disclosure` (here) says the converse: every causal advice `d`
  arises as the diary of the probe "read off the last symbol of `d`".

So the two constructions are mutually inverse, and the probe layer can be dropped entirely.
Restating `Advice.IsFiniteFreeDisclosure` without it gives `Advice.IsRevFstOfCausal`:

> `adv` is the right-to-left FST image of a **causal** advice over a finite alphabet.

With this the whole theory becomes one schema with a strength dial on the first stage:

| notion                     | first stage                | equation             |
| -------------------------- | -------------------------- | -------------------- |
| `Advice.IsRevFstOfCausal`  | causal                     | `M.scanr ∘ d = adv`  |
| `Advice.IsFiniteRtDisclosure` | causal + advised-RT     | `M.scanr ∘ d = adv`  |
| `Advice.IsTwoStageAdvice`  | causal + CART              | `M.scanr ∘ d = adv`  |

and `open_question_1` becomes the single question

> if `adv = M.scanr ∘ d` with `d` causal and `adv` is weakly RT-closed,
> is the causal part `d` weakly RT-closed too?

which is `Advice.two_stage_iff_revFstOfCausal_closed` minus its remaining gap. This is
strictly better than the probe formulation: closure of *causal* advices is completely
understood (`is_cart_advice_of_rt_closed_and_causal`), so the obligation now sits on the
one class where we have a full structure theorem.
-/

namespace CellularAutomatas

variable {α Γ Δ : Type} [Alphabet α] [Alphabet Γ] [Alphabet Δ]
variable {adv : Advice α Γ}

/-! ## Free probes are exactly causal advices -/

/-- The probe that reads off the last symbol of an advice. For *causal* `d` this inverts
`Advice.FreeProbe.disclosure`. -/
def Advice.FreeProbe.ofCausal (adv : Advice α Γ) (d : Advice α Δ) : adv.FreeProbe Δ where
  value := fun u => (d u).getLast?.getD default

omit [Alphabet α] [Alphabet Γ] in
/-- **Every causal advice is a diary.** Entry `k` of the diary of `ofCausal d` is the last
symbol of `d (w.take (k+1))`, which by causality is `(d w)[k]`. -/
theorem Advice.FreeProbe.ofCausal_disclosure (d : Advice α Δ) (hd : d.causal) :
    (Advice.FreeProbe.ofCausal adv d).disclosure = d := by
  apply advice_ext
  funext w
  apply List.ext_getElem
  · show ((Advice.FreeProbe.ofCausal adv d).disclosure.f w).length = (d.f w).length
    simp [Advice.FreeProbe.disclosure, d.len]
  · intro k h1 h2
    have hk : k < (d.f w).length := h2
    -- Unfold the diary: entry `k` is the probe applied to `w.take (k+1)`.
    simp only [Advice.FreeProbe.disclosure, List.getElem_map, List.getElem_range]
    show (d.f (w.take (k + 1))).getLast?.getD default = (d.f w)[k]
    -- Causality turns the shorter run into a prefix of the full run.
    rw [(hd w).2 (k + 1)]
    -- The last symbol of a `(k+1)`-prefix is the element at index `k`.
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    show ((d.f w).take k ++ [(d.f w)[k]]).getLast?.getD default = (d.f w)[k]
    rw [List.getLast?_concat]
    rfl

/-! ## `adv` as a reverse-FST image of a causal advice -/

/-- **`adv` presented as the right-to-left FST image of a causal advice.**

This is `Advice.IsFiniteFreeDisclosure` with the probe layer removed: the first stage is
just a causal advice over a finite alphabet. -/
structure Advice.IsRevFstOfCausal (adv : Advice α Γ) where
  /-- Alphabet of the causal first stage. -/
  Δ : Type
  [alphabetΔ : Alphabet Δ]
  /-- The causal first stage. -/
  first : Advice α Δ
  /-- ... which is indeed causal. -/
  first_causal : first.causal
  /-- The right-to-left reconstruction transducer. -/
  M : FiniteStateTransducer Δ Γ
  /-- Scanning the first stage from the right reproduces `adv`. -/
  spec : ∀ w, M.scanr (first w) = adv w

attribute [instance] Advice.IsRevFstOfCausal.alphabetΔ

/-- A finite free disclosure *is* a reverse-FST presentation: take the diary as first stage. -/
def Advice.IsFiniteFreeDisclosure.toRevFstOfCausal (h : adv.finite_free_disclosure) :
    adv.IsRevFstOfCausal where
  Δ := h.Δ
  first := h.probe.disclosure
  first_causal := h.probe.disclosure_causal
  M := h.M
  spec := h.spec

/-- ... and conversely, using the last-symbol probe of the causal first stage. -/
def Advice.IsRevFstOfCausal.toFiniteFreeDisclosure (h : adv.IsRevFstOfCausal) :
    adv.finite_free_disclosure where
  Δ := h.Δ
  probe := Advice.FreeProbe.ofCausal adv h.first
  M := h.M
  spec := by
    intro w
    rw [Advice.FreeProbe.ofCausal_disclosure h.first h.first_causal]
    exact h.spec w

omit [Alphabet Δ] in
/-- **Finite future variation = being a reverse-FST image of a causal advice.**

The combinatorial bound and the structural presentation are the same notion; the probe layer
was only ever bookkeeping. -/
theorem Advice.finite_future_variation_iff_revFstOfCausal (adv : Advice α Γ) :
    adv.finite_future_variation ↔ Nonempty adv.IsRevFstOfCausal := by
  rw [adv.finite_future_variation_iff_nonempty_finite_free_disclosure]
  exact ⟨fun ⟨h⟩ => ⟨h.toRevFstOfCausal⟩, fun ⟨h⟩ => ⟨h.toFiniteFreeDisclosure⟩⟩

/-! ## The whole open question, in one line -/

/-- **If the causal part is closed, `adv` is two-stage.**

Closure of a *causal* advice already gives it a CART presentation, and post-composing the
reconstruction transducer is literally a two-stage presentation. Nothing is assumed about
`adv` itself. -/
def Advice.IsRevFstOfCausal.toTwoStage (h : adv.IsRevFstOfCausal)
    (hclosed : h.first.weak_rt_closed) : adv.is_two_stage_advice :=
  h.toFiniteFreeDisclosure.toTwoStage
    (by
      show (Advice.FreeProbe.ofCausal adv h.first).disclosure.weak_rt_closed
      rw [Advice.FreeProbe.ofCausal_disclosure h.first h.first_causal]
      exact hclosed)

omit [Alphabet Δ] in
/-- **Two-stage ⟺ some causal first stage is weakly RT-closed.**

This is the probe-free form of `Advice.two_stage_iff_rt_closed_diary`, and it isolates
`open_question_1` completely: given `adv` weakly RT-closed and written as `M.scanr ∘ d` with
`d` causal, does closure descend from `adv` to `d`?

Note the asymmetry that makes this hard — `d` is *richer* than `adv` (the transducer maps
`d ↦ adv`, never back), so closure is being demanded of a strictly stronger advice. -/
theorem Advice.two_stage_iff_revFstOfCausal_closed (adv : Advice α Γ) :
    Nonempty adv.is_two_stage_advice ↔
      ∃ h : adv.IsRevFstOfCausal, Nonempty h.first.weak_rt_closed := by
  rw [adv.two_stage_iff_rt_closed_diary]
  constructor
  · show (∃ h : adv.finite_free_disclosure, Nonempty h.probe.disclosure.weak_rt_closed) → _
    rintro ⟨h, hclosed⟩
    exact ⟨h.toRevFstOfCausal, hclosed⟩
  · show (∃ h : adv.IsRevFstOfCausal, Nonempty h.first.weak_rt_closed) → _
    rintro ⟨h, ⟨hclosed⟩⟩
    exact ⟨h.toFiniteFreeDisclosure, by
      show Nonempty (Advice.FreeProbe.ofCausal adv h.first).disclosure.weak_rt_closed
      rw [Advice.FreeProbe.ofCausal_disclosure h.first h.first_causal]
      exact ⟨hclosed⟩⟩

end CellularAutomatas
