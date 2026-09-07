import CellularAutomatas.proofs.advice_theory.finite_future_variation_iff_free_disclosure

/-!
# Closure properties of `Advice.finite_future_variation`

`Advice.finite_future_variation` is the combinatorial half of the two-stage question: it says
that, uniformly in the prefix `p`, only boundedly many advice words can appear on `p` when `p`
is extended by an arbitrary suffix.

To use it as a design tool — for building candidate advices out of simpler pieces, and for
ruling candidates out — we need to know how the bound behaves under the standard operations.
This file collects those facts:

* `Advice.finite_future_variation_of_causal` — a causal advice has bound `1`; the suffix has
  no influence at all.
* `Advice.finite_future_variation_lift` — relabelling the input alphabet keeps the bound.
  This matters because `Advice.rt_closed` quantifies over all such lifts.
* `Advice.finite_future_variation_compose_fst` — post-composing a right-to-left finite-state
  transducer keeps the property. This is the exact operation the second stage of a two-stage
  advice performs, so the class is stable under "clean-up passes".
* `Advice.finite_future_variation_pair` — running two advices side by side multiplies bounds.
* `Advice.IsTwoStageAdvice.finite_future_variation` — every two-stage advice has finite future
  variation, which is the form in which the notion is used as a *necessary* condition.

Everything is proved either from the counting definition directly or by routing through
`Advice.finite_future_variation_iff_nonempty_finite_free_disclosure`, whichever is shorter.
-/

namespace CellularAutomatas

open Classical

variable {α β Γ Γ₁ Γ₂ : Type} [Alphabet α] [Alphabet β] [Alphabet Γ] [Alphabet Γ₁] [Alphabet Γ₂]


/-! ## A convenient sufficient condition

Rather than computing the reachable set exactly, it is almost always easier to exhibit a
uniformly bounded *over-approximation* of it. -/

omit [Alphabet α] [Alphabet Γ] in
/-- Any uniformly bounded family of sets containing all reachable advice prefixes witnesses
finite future variation. -/
lemma Advice.finite_future_variation_of_bound {adv : Advice α Γ} (N : ℕ)
    (F : Word α → Set (Word Γ)) (hcard : ∀ p, (F p).encard ≤ N)
    (hmem : ∀ p s, rel_repr adv p s ∈ F p) :
    adv.finite_future_variation := by
  refine ⟨N, fun p => ?_⟩
  refine le_trans (Set.encard_mono ?_) (hcard p)
  rintro _ ⟨s, -, rfl⟩
  exact hmem p s

omit [Alphabet α] [Alphabet Γ] in
/-- Finset form of `Advice.finite_future_variation_of_bound`. -/
lemma Advice.finite_future_variation_of_finset_bound {adv : Advice α Γ} (N : ℕ)
    (F : Word α → Finset (Word Γ)) (hcard : ∀ p, (F p).card ≤ N)
    (hmem : ∀ p s, rel_repr adv p s ∈ F p) :
    adv.finite_future_variation :=
  Advice.finite_future_variation_of_bound N (fun p => ↑(F p))
    (fun p => by
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast hcard p)
    (fun p s => Finset.mem_coe.mpr (hmem p s))


/-! ## Causal advice -/

omit [Alphabet α] [Alphabet Γ] in
/-- A causal advice already knows its value on `p` before the suffix arrives, so exactly one
advice prefix is reachable. -/
theorem Advice.finite_future_variation_of_causal {adv : Advice α Γ} (h : adv.causal) :
    adv.finite_future_variation := by
  refine Advice.finite_future_variation_of_bound 1 (fun p => {adv p}) (fun p => by simp) ?_
  intro p s
  show rel_repr adv p s ∈ ({adv p} : Set (Word Γ))
  -- Causality applied to `p ++ s` at cut `|p|` says exactly `adv p = rel_repr adv p s`.
  have hcut : (p ++ s).take p.length = p := List.take_left' rfl
  have hcausal : adv.f ((p ++ s).take p.length) = (adv.f (p ++ s)).take p.length :=
    (h (p ++ s)).2 p.length
  rw [hcut] at hcausal
  show rel_repr adv p s ∈ ({adv p} : Set (Word Γ))
  simp only [Set.mem_singleton_iff, rel_repr]
  exact hcausal.symm


/-! ## Relabelling the input alphabet -/

omit [Alphabet α] [Alphabet Γ] in
/-- Reading the input through `π` can only shrink the set of reachable advice prefixes: every
suffix of the lifted advice acts through its image, so the bound of `adv` still works. -/
theorem Advice.finite_future_variation_lift {adv : Advice α Γ}
    (h : adv.finite_future_variation) (π : β → α) :
    (adv.lift π).finite_future_variation := by
  obtain ⟨N, hN⟩ := h
  refine Advice.finite_future_variation_of_bound N
    (fun p => Set.image (fun s : Word α => rel_repr adv (p.map π) s) Set.univ)
    (fun p => hN _) ?_
  intro p s
  refine ⟨s.map π, Set.mem_univ _, ?_⟩
  show rel_repr adv (p.map π) (s.map π) = rel_repr (adv.lift π) p s
  simp [rel_repr, Advice.lift]


/-! ## Post-composition with a finite-state transducer

This is the operation performed by the second stage of a two-stage advice. Composing it onto
an advice with finite future variation is transparent at the level of free disclosures: keep
the probe, and compose the reconstruction transducers. -/

/-- Finite future variation survives a right-to-left finite-state clean-up pass. -/
theorem Advice.finite_future_variation_compose_fst {adv : Advice α Γ₁}
    (h : adv.finite_future_variation) (M : FiniteStateTransducer Γ₁ Γ₂) :
    (adv.compose M.advice).finite_future_variation := by
  -- The free disclosure of `adv`, with `M` appended to the reconstruction transducer.
  let d := Advice.finite_free_disclosure_of_finite_future_variation h
  refine Advice.finite_future_variation_of_finite_free_disclosure
    (adv := adv.compose M.advice)
    { Δ := d.Δ
      probe := ⟨d.probe.value⟩
      M := M ⊚ d.M
      spec := ?_ }
  intro w
  show (M ⊚ d.M).scanr (d.probe.disclosure w) = M.scanr (adv w)
  rw [FiniteStateTransducer.compose_spec2]
  show M.scanr (d.M.scanr (d.probe.disclosure w)) = M.scanr (adv w)
  rw [d.spec w]


/-! ## Running two advices side by side -/

/-- Two advices over the same input, bundled into a single advice over the product alphabet. -/
def Advice.pair (adv₁ : Advice α Γ₁) (adv₂ : Advice α Γ₂) : Advice α (Γ₁ × Γ₂) :=
  ⟨fun w => (adv₁ w) ⨂ (adv₂ w), by intro w; simp⟩

omit [Alphabet α] [Alphabet Γ] [Alphabet Γ₁] [Alphabet Γ₂] in
private lemma take_zip_eq {γ δ : Type} (n : ℕ) (l₁ : List γ) (l₂ : List δ) :
    (l₁ ⨂ l₂).take n = (l₁.take n) ⨂ (l₂.take n) := by
  induction n generalizing l₁ l₂ with
  | zero => simp
  | succ n ih =>
    cases l₁ with
    | nil => simp
    | cons a l₁ =>
      cases l₂ with
      | nil => simp
      | cons b l₂ => simp [List.zip_cons_cons, ih]

omit [Alphabet α] [Alphabet Γ] in
/-- The reachable advice prefixes of a pair are pairs of reachable advice prefixes, so the
bounds multiply. -/
theorem Advice.finite_future_variation_pair {adv₁ : Advice α Γ₁} {adv₂ : Advice α Γ₂}
    (h₁ : adv₁.finite_future_variation) (h₂ : adv₂.finite_future_variation) :
    (adv₁.pair adv₂).finite_future_variation := by
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  have hfin₁ : ∀ p : Word α,
      (Set.image (fun s : Word α => rel_repr adv₁ p s) Set.univ).Finite :=
    fun p => Set.finite_of_encard_le_coe (hN₁ p)
  have hfin₂ : ∀ p : Word α,
      (Set.image (fun s : Word α => rel_repr adv₂ p s) Set.univ).Finite :=
    fun p => Set.finite_of_encard_le_coe (hN₂ p)
  refine Advice.finite_future_variation_of_finset_bound (N₁ * N₂)
    (fun p => ((hfin₁ p).toFinset ×ˢ (hfin₂ p).toFinset).image
      (fun q : Word Γ₁ × Word Γ₂ => q.1 ⨂ q.2)) ?_ ?_
  · intro p
    show (((hfin₁ p).toFinset ×ˢ (hfin₂ p).toFinset).image
      (fun q : Word Γ₁ × Word Γ₂ => q.1 ⨂ q.2)).card ≤ N₁ * N₂
    have c₁ : (hfin₁ p).toFinset.card ≤ N₁ := by
      have hb := hN₁ p
      rw [← Set.Finite.coe_toFinset (hfin₁ p), Set.encard_coe_eq_coe_finsetCard] at hb
      exact_mod_cast hb
    have c₂ : (hfin₂ p).toFinset.card ≤ N₂ := by
      have hb := hN₂ p
      rw [← Set.Finite.coe_toFinset (hfin₂ p), Set.encard_coe_eq_coe_finsetCard] at hb
      exact_mod_cast hb
    calc (((hfin₁ p).toFinset ×ˢ (hfin₂ p).toFinset).image
            (fun q : Word Γ₁ × Word Γ₂ => q.1 ⨂ q.2)).card
        ≤ ((hfin₁ p).toFinset ×ˢ (hfin₂ p).toFinset).card := Finset.card_image_le
      _ = (hfin₁ p).toFinset.card * (hfin₂ p).toFinset.card := Finset.card_product _ _
      _ ≤ N₁ * N₂ := Nat.mul_le_mul c₁ c₂
  · intro p s
    refine Finset.mem_image.mpr ⟨(rel_repr adv₁ p s, rel_repr adv₂ p s), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨(hfin₁ p).mem_toFinset.mpr ⟨s, Set.mem_univ _, rfl⟩,
         (hfin₂ p).mem_toFinset.mpr ⟨s, Set.mem_univ _, rfl⟩⟩
    · show (rel_repr adv₁ p s) ⨂ (rel_repr adv₂ p s) = rel_repr (adv₁.pair adv₂) p s
      show (rel_repr adv₁ p s) ⨂ (rel_repr adv₂ p s)
          = ((adv₁ (p ++ s)) ⨂ (adv₂ (p ++ s))).take p.length
      rw [take_zip_eq]
      rfl


/-! ## Two-stage advices have finite future variation

This is the direction in which the notion is used to *refute* two-stage-ness: exhibiting an
advice of unbounded future variation shows it is not two-stage. -/

/-- Every two-stage advice has finite future variation. -/
theorem Advice.IsTwoStageAdvice.finite_future_variation {adv : Advice α Γ}
    (h : adv.is_two_stage_advice) : adv.finite_future_variation :=
  Advice.finite_future_variation_of_finite_free_disclosure
    h.finite_rt_disclosure.finite_free_disclosure

end CellularAutomatas
