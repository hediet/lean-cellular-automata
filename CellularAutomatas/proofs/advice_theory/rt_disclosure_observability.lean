import CellularAutomatas.proofs.advice_theory.finite_future_variation_iff_free_disclosure
import CellularAutomatas.proofs.constructions.basic_product_ca

/-!
# Isolating the gap between free disclosure and RT disclosure

`Advice.finite_free_disclosure` and `Advice.finite_rt_disclosure` differ in exactly one field:
the RT version additionally demands, for each probe value `d`, a real-time cell automaton that
— *reading the advice* — decides whether the probe of the input is `d`. This file makes that
single difference into a named property and proves the resulting equivalence:

```
Nonempty adv.finite_rt_disclosure ↔ ∃ h : adv.finite_free_disclosure, Nonempty h.probe.IsObservable
```

Combined with `Advice.finite_future_variation_iff_nonempty_finite_free_disclosure`, this pins the
open question down to a concrete property of one explicitly constructed function: an advice with
finite future variation is two-stage (given weak RT closure) **iff its canonical
index-translation table is observable**.

Two tools are provided for actually establishing observability:

* `Advice.IsFiniteFreeDisclosure.toRt_of_refines` — it suffices to find *any* observable probe
  that the free probe factors through. This is the practical shape of a positive answer: one
  never has to observe the canonical table itself, only something at least as fine.
* `Advice.RtProbe.ofAnnotatedDFA` — any probe value computed by a finite automaton scanning the
  advice-annotated input is observable, with no closure hypothesis whatsoever. This is the main
  supply of observable probes: the recognizer may read `adv w` in full, so everything the advice
  itself reveals about the input is free.
-/

namespace CellularAutomatas

open Classical

variable {α Γ Δ : Type} [Alphabet α] [Alphabet Γ] [Alphabet Δ]


/-! ## Observability: the single field separating free from RT disclosure -/

/-- A free probe is **observable** when each of its fibers is recognized by a real-time cell
automaton that is allowed to read the advice track. This is precisely the extra data an
`Advice.RtProbe` carries over an `Advice.FreeProbe`. -/
structure Advice.FreeProbe.IsObservable {adv : Advice α Γ} (probe : adv.FreeProbe Δ) where
  /-- Advised real-time recognizer for the fiber over `d`. -/
  recognizer : Δ → CA_rt (α × Γ)
  /-- The recognizer accepts exactly the words whose probe value is `d`. -/
  spec : ∀ d w, w ∈ (recognizer d + adv).L ↔ probe.value w = d

/-- Attaching recognizers turns a free probe into an RT probe. -/
def Advice.FreeProbe.toRtProbe {adv : Advice α Γ} (probe : adv.FreeProbe Δ)
    (h : probe.IsObservable) : adv.RtProbe Δ where
  toFreeProbe := probe
  recognizer := h.recognizer
  spec := h.spec

/-- Forgetting the recognizers of an RT probe leaves an observable free probe. -/
def Advice.RtProbe.isObservable {adv : Advice α Γ} (probe : adv.RtProbe Δ) :
    probe.toFreeProbe.IsObservable where
  recognizer := probe.recognizer
  spec := probe.spec


/-! ## The isolation theorem -/

/-- A free disclosure whose probe is observable *is* an RT disclosure. -/
def Advice.IsFiniteFreeDisclosure.toRt {adv : Advice α Γ} (h : adv.finite_free_disclosure)
    (hobs : h.probe.IsObservable) : adv.finite_rt_disclosure where
  Δ := h.Δ
  probe := h.probe.toRtProbe hobs
  M := h.M
  spec := h.spec

/-- Conversely, an RT disclosure is a free disclosure with an observable probe. -/
def Advice.IsFiniteRtDisclosure.probe_isObservable {adv : Advice α Γ}
    (h : adv.finite_rt_disclosure) :
    (h.finite_free_disclosure).probe.IsObservable :=
  h.probe.isObservable

omit [Alphabet α] in
/-- **Isolation.** The whole distance between `finite_free_disclosure` (equivalently, finite
future variation) and `finite_rt_disclosure` is the observability of a single probe. -/
theorem Advice.finite_rt_disclosure_iff_observable_free_disclosure (adv : Advice α Γ) :
    Nonempty adv.finite_rt_disclosure ↔
      ∃ h : adv.finite_free_disclosure, Nonempty h.probe.IsObservable := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.finite_free_disclosure, ⟨h.probe_isObservable⟩⟩
  · rintro ⟨h, ⟨hobs⟩⟩
    exact ⟨h.toRt hobs⟩


/-! ## Refinement: observing something finer is enough

One never has to observe the canonical table itself. Any observable probe through which the
free probe factors does the job — the reconstruction transducer simply pre-composes with the
factoring map. -/

/-- If an observable probe refines the probe of a free disclosure, the disclosure upgrades to
an RT disclosure. -/
def Advice.IsFiniteFreeDisclosure.toRt_of_refines {adv : Advice α Γ}
    (h : adv.finite_free_disclosure) {Δ' : Type} [Alphabet Δ']
    (probe' : adv.RtProbe Δ') (g : Δ' → h.Δ)
    (hg : ∀ u : Word α, h.probe.value u = g (probe'.value u)) :
    adv.finite_rt_disclosure where
  Δ := Δ'
  probe := probe'
  M := h.M ⊚ FiniteStateTransducer.M_map g
  spec := by
    intro w
    -- Relabelling the finer diary entrywise reproduces the coarser diary.
    have hmap : List.map g (probe'.disclosure w) = h.probe.disclosure w := by
      apply List.ext_getElem
      · simp [Advice.RtProbe.disclosure, Advice.FreeProbe.disclosure]
      · intro i h1 h2
        simp only [List.getElem_map, Advice.RtProbe.disclosure,
          Advice.FreeProbe.disclosure_getElem]
        exact (hg _).symm
    calc (h.M ⊚ FiniteStateTransducer.M_map g).scanr (probe'.disclosure w)
        = h.M.scanr ((FiniteStateTransducer.M_map g).scanr (probe'.disclosure w)) := by
          rw [FiniteStateTransducer.compose_spec2]; rfl
      _ = h.M.scanr (List.map g (probe'.disclosure w)) := by
          rw [FiniteStateTransducer.M_map_scanr]
      _ = h.M.scanr (h.probe.disclosure w) := by rw [hmap]
      _ = adv w := h.spec w

/-- **Isolated form of the open question.** For an advice with finite future variation, finite
RT disclosure follows as soon as some observable probe refines the canonical
index-translation table of `finite_free_disclosure_of_finite_future_variation`. -/
noncomputable def Advice.finite_rt_disclosure_of_refines_canonical_table {adv : Advice α Γ}
    (h : adv.finite_future_variation) {Δ' : Type} [Alphabet Δ']
    (probe' : adv.RtProbe Δ')
    (g : Δ' → FiniteFutureVariation.Tbl Γ h.choose)
    (hg : ∀ u : Word α,
      (FiniteFutureVariation.freeProbe adv h.choose h.choose_spec).value u = g (probe'.value u)) :
    adv.finite_rt_disclosure :=
  (Advice.finite_free_disclosure_of_finite_future_variation h).toRt_of_refines probe' g hg


/-! ## A supply of observable probes: finite automata over the annotated input

The recognizer of an RT probe reads the *advice-annotated* word. So everything the advice
already displays about the input is observable for free, with no RT-closure hypothesis. The
cleanest packaging: any probe value computed by a DFA scanning `w ⨂ adv w` is observable. -/

section AnnotatedDFA

variable {σ : Type} [Alphabet σ]

/-- The fiber recognizer: the same automaton, with the accepting set carved out by `φ · = d`. -/
private def annotatedFiberCA (D : DFA (α × Γ) σ) (φ : σ → Δ) (d : Δ) : CA_rt (α × Γ) :=
  toRtCa (DFAtoCA { step := D.step, start := D.start, accept := { s | φ s = d } })

/-- A probe whose value is read off a finite automaton scanning the advice-annotated input.
No closure assumption is needed: the recognizer is allowed to read the advice. -/
def Advice.RtProbe.ofAnnotatedDFA (adv : Advice α Γ) (D : DFA (α × Γ) σ) (φ : σ → Δ) :
    adv.RtProbe Δ where
  value := fun w => φ (D.eval (adv.annotate w))
  recognizer := fun d => annotatedFiberCA D φ d
  spec := by
    intro d w
    rw [tCellAutomatonWithAdvice.elem_L_iff]
    show (annotatedFiberCA D φ d).accepts (adv.annotate w) ↔ _
    rw [annotatedFiberCA, DFAtoCA.accepts_iff]
    show D.evalFrom D.start (adv.annotate w) ∈ { s | φ s = d } ↔ _
    rfl

@[simp]
lemma Advice.RtProbe.ofAnnotatedDFA_value (adv : Advice α Γ) (D : DFA (α × Γ) σ) (φ : σ → Δ)
    (w : Word α) :
    (Advice.RtProbe.ofAnnotatedDFA adv D φ).value w = φ (D.eval (adv.annotate w)) := rfl

end AnnotatedDFA


/-! ## The bound-one case is already settled

Weak RT closure plays no role in `finite_rt_disclosure`: the recognizers of an RT probe are
allowed to read the advice, so no elimination hypothesis is needed. That makes the natural
strengthening of the open question

> does `finite_future_variation` alone imply `finite_rt_disclosure`?

and the smallest instance of it is already a theorem: future variation bounded by `1` is
literally causality, and causal advices have finite RT disclosure unconditionally
(`Advice.finite_rt_disclosure_of_causal`). The first open case is the bound `2`. -/

omit [Alphabet Δ] in
/-- An advice has at most one reachable advice prefix per prefix exactly when it is causal. -/
theorem Advice.causal_iff_variation_le_one (adv : Advice α Γ) :
    adv.causal ↔ ∀ p : Word α, (Set.univ.image (fun s : Word α => rel_repr adv p s)).encard ≤ 1 := by
  constructor
  · intro hcausal p
    -- Causality pins every reachable prefix to `adv p`.
    have hsub : (Set.univ.image (fun s : Word α => rel_repr adv p s)) ⊆ ({adv p} : Set (Word Γ)) := by
      rintro _ ⟨s, -, rfl⟩
      have hcut : (p ++ s).take p.length = p := List.take_left' rfl
      have hstep : adv.f ((p ++ s).take p.length) = (adv.f (p ++ s)).take p.length :=
        (hcausal (p ++ s)).2 p.length
      rw [hcut] at hstep
      exact hstep.symm
    exact le_trans (Set.encard_mono hsub) (le_of_eq (Set.encard_singleton _))
  · intro hbound w
    refine ⟨adv.len w, fun i => ?_⟩
    show adv (w.take i) = (adv w).take i
    by_cases hi : i ≤ w.length
    · -- Split `w` at `i`; the empty extension and the actual extension must agree.
      set p := w.take i with hp
      have hplen : p.length = i := by simp [hp, Nat.min_eq_left hi]
      have hsplit : p ++ w.drop i = w := List.take_append_drop i w
      have heq : rel_repr adv p (w.drop i) = rel_repr adv p [] :=
        (Set.encard_le_one_iff.1 (hbound p)) _ _ ⟨_, Set.mem_univ _, rfl⟩ ⟨[], Set.mem_univ _, rfl⟩
      rw [rel_repr_nil] at heq
      show adv p = (adv w).take i
      rw [← heq]
      show (adv (p ++ w.drop i)).take p.length = (adv w).take i
      rw [hsplit, hplen]
    · -- Beyond the length of `w` both sides are `adv w`.
      have hw : w.take i = w := List.take_of_length_le (by omega)
      have hadv : (adv w).take i = adv w := List.take_of_length_le (by simp; omega)
      rw [hw, hadv]

omit [Alphabet Δ] in
/-- **The strengthened conjecture holds for bound `1`.** -/
def Advice.finite_rt_disclosure_of_variation_le_one (adv : Advice α Γ)
    (h : ∀ p : Word α, (Set.univ.image (fun s : Word α => rel_repr adv p s)).encard ≤ 1) :
    adv.finite_rt_disclosure :=
  Advice.finite_rt_disclosure_of_causal adv ((Advice.causal_iff_variation_le_one adv).2 h)


/-! ## Under weak RT closure the advice track is free
Observability is stated in terms of *advised* real-time recognition, which looks like a
genuinely weaker demand than plain real-time recognition. Under weak RT closure it is not:
closure strips the advice from every recognizer, and conversely a recognizer may always
ignore the advice track. So for a weakly RT-closed advice a probe is observable **iff every
fiber is a plain real-time language over `α`** — the advice disappears from the problem
entirely. -/

omit [Alphabet Δ] in
/-- Ignoring the advice track is always allowed, so a probe whose fibers are plain real-time
languages is observable. No closure hypothesis is needed for this direction. -/
noncomputable def Advice.FreeProbe.isObservable_of_fibers_ca_rt {adv : Advice α Γ}
    (probe : adv.FreeProbe Δ)
    (h : ∀ d, {u : Word α | probe.value u = d} ∈ ℒ (CA_rt α)) : probe.IsObservable where
  recognizer := fun d => (ℒ_CA_rt_iff.1 (h d)).choose.map_embed Prod.fst
  spec := by
    intro d w
    rw [tCellAutomatonWithAdvice.elem_L_iff, map_embed_L]
    -- The first track of the annotated word is the input itself.
    rw [show (adv.annotate w).map Prod.fst = w from List.map_fst_zip (by simp)]
    rw [(ℒ_CA_rt_iff.1 (h d)).choose_spec]
    rfl

omit [Alphabet Δ] in
/-- Conversely, weak RT closure eliminates the advice from every recognizer, turning each
fiber into a plain real-time language. -/
theorem Advice.FreeProbe.fibers_ca_rt_of_isObservable {adv : Advice α Γ}
    {probe : adv.FreeProbe Δ} (hobs : probe.IsObservable) (hclosed : adv.weak_rt_closed)
    (d : Δ) : {u : Word α | probe.value u = d} ∈ ℒ (CA_rt α) := by
  rw [ℒ_CA_rt_iff]
  refine ⟨hclosed.map (hobs.recognizer d), ?_⟩
  rw [hclosed.spec]
  ext u
  exact (tCellAutomatonWithAdvice.elem_L_iff u).symm.trans (hobs.spec d u)

omit [Alphabet Δ] in
/-- **For a weakly RT-closed advice, observability is plain real-time computability.** -/
theorem Advice.observable_iff_fibers_ca_rt {adv : Advice α Γ} (hclosed : adv.weak_rt_closed)
    (probe : adv.FreeProbe Δ) :
    Nonempty probe.IsObservable ↔ ∀ d, {u : Word α | probe.value u = d} ∈ ℒ (CA_rt α) :=
  ⟨fun ⟨hobs⟩ d => probe.fibers_ca_rt_of_isObservable hobs hclosed d,
    fun h => ⟨probe.isObservable_of_fibers_ca_rt h⟩⟩

/-- **The open question, with the advice eliminated.** For a weakly RT-closed advice, a
two-stage presentation exists exactly when some finite free disclosure has all of its probe
fibers in `ℒ (CA_rt α)`.

This is the sharpest available restatement: no advised machine models remain, only the
question whether a bounded-range combinatorial function of the input — the canonical
index-translation table of the possibility tree — is computable in real time. -/
theorem Advice.two_stage_iff_free_disclosure_with_rt_fibers (adv : Advice α Γ)
    (hclosed : adv.weak_rt_closed) :
    Nonempty adv.is_two_stage_advice ↔
      ∃ h : adv.finite_free_disclosure,
        ∀ d, {u : Word α | h.probe.value u = d} ∈ ℒ (CA_rt α) := by
  calc Nonempty adv.is_two_stage_advice
      ↔ Nonempty adv.weak_rt_closed ∧ Nonempty adv.finite_rt_disclosure :=
        (weak_rt_closed_and_finite_rt_disclosure_iff_two_stage adv).symm
    _ ↔ Nonempty adv.finite_rt_disclosure :=
        ⟨And.right, fun h => ⟨⟨hclosed⟩, h⟩⟩
    _ ↔ ∃ h : adv.finite_free_disclosure, Nonempty h.probe.IsObservable :=
        Advice.finite_rt_disclosure_iff_observable_free_disclosure adv
    _ ↔ ∃ h : adv.finite_free_disclosure,
          ∀ d, {u : Word α | h.probe.value u = d} ∈ ℒ (CA_rt α) :=
        exists_congr fun h => Advice.observable_iff_fibers_ca_rt hclosed h.probe


/-! ## A necessary condition for closure: the advice may not reveal external information

A weakly RT-closed advice cannot tell a real-time CA anything the CA could not already have
computed from the input by itself. The sharpest cheap instance: reading the *last* advice
symbol is an advised real-time test, so closure forces the corresponding language of inputs
to be plainly real-time.

This is the practical way to refute closure. It is exactly what fails for an advice that
displays the prefix of an arbitrary oracle set `R ⊆ ℕ` at power-of-two lengths and blanks
otherwise: its last-symbol language is `{w : |w| = 2 ^ k ∧ |w| - 1 ∈ R}`, which pins an
arbitrary subset of the powers of two and so is not real-time for most `R`. -/

/-- **Closure forces the last advice symbol to be real-time computable from the input alone.** -/
theorem Advice.WeakRtClosed.last_symbol_language_ca_rt {adv : Advice α Γ}
    (hclosed : adv.weak_rt_closed) (c : Γ) : L_c adv c ∈ ℒ (CA_rt α) := by
  rw [ℒ_CA_rt_iff]
  refine ⟨hclosed.map (CA_adv_L_c α c), ?_⟩
  rw [hclosed.spec]
  exact CA_adv_L_c_spec adv c

/-- Contrapositive: a single non-real-time last-symbol language refutes weak RT closure,
hence also refutes any two-stage presentation. -/
theorem Advice.not_weak_rt_closed_of_last_symbol_not_ca_rt {adv : Advice α Γ} (c : Γ)
    (h : L_c adv c ∉ ℒ (CA_rt α)) : IsEmpty adv.weak_rt_closed :=
  ⟨fun hclosed => h (hclosed.last_symbol_language_ca_rt c)⟩


/-! ## Observable probes compose in parallel

A real-time CA can run boundedly many computations side by side in a product state set and
combine their verdicts at the end. So observability never has to be established for a
complicated probe in one go: build independently observable pieces and pair them. Combined
with `Advice.IsFiniteFreeDisclosure.toRt_of_refines` — which only asks the combined probe to
*refine* the canonical table — this is the practical route to a positive answer. -/

private def interCa {β : Type} [Alphabet β] (C₁ C₂ : CA_rt β) : CA_rt β :=
  toRtCa ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && b))

private lemma interCa_L {β : Type} [Alphabet β] (C₁ C₂ : CA_rt β) (w : Word β) :
    w ∈ (interCa C₁ C₂).L ↔ w ∈ C₁.L ∧ w ∈ C₂.L := by
  rw [CA_rt_L_iff (C := interCa C₁ C₂), CA_rt_L_iff (C := C₁), CA_rt_L_iff (C := C₂)]
  show ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project
      (fun (a, b) => a && b)).comp ⦋w⦌ (w.length - 1) 0 = true ↔ _
  simp only [comp_of_map_project, ca_zip_comp, Bool.and_eq_true]

/-- **Two observable probes run in parallel are an observable probe.** The recognizer for a
pair of values is the product of the two recognizers, reading the same annotated word. -/
def Advice.RtProbe.pair {adv : Advice α Γ} {Δ₁ Δ₂ : Type} [Alphabet Δ₁] [Alphabet Δ₂]
    (p₁ : adv.RtProbe Δ₁) (p₂ : adv.RtProbe Δ₂) : adv.RtProbe (Δ₁ × Δ₂) where
  value := fun w => (p₁.value w, p₂.value w)
  recognizer := fun d => interCa (p₁.recognizer d.1) (p₂.recognizer d.2)
  spec := by
    intro d w
    obtain ⟨d₁, d₂⟩ := d
    rw [(tCellAutomatonWithAdvice.elem_L_iff w).trans (interCa_L _ _ _)]
    show (w ∈ (p₁.recognizer d₁ + adv).L ∧ w ∈ (p₂.recognizer d₂ + adv).L)
      ↔ (p₁.value w, p₂.value w) = (d₁, d₂)
    rw [p₁.spec, p₂.spec, Prod.mk.injEq]

@[simp] lemma Advice.RtProbe.pair_value {adv : Advice α Γ} {Δ₁ Δ₂ : Type}
    [Alphabet Δ₁] [Alphabet Δ₂] (p₁ : adv.RtProbe Δ₁) (p₂ : adv.RtProbe Δ₂) (w : Word α) :
    (p₁.pair p₂).value w = (p₁.value w, p₂.value w) := rfl


/-! ## The diary is a causal advice: closing the diary is the whole question

A diary `probe.disclosure` is not an arbitrary advice — it is *causal* by construction, since
entry `i` only inspects `w.take (i+1)`. For causal advices the theory is already complete:
`is_cart_advice_of_rt_closed_and_causal` turns weak RT closure into a CART presentation. So a
weakly RT-closed diary immediately makes the whole advice two-stage, with **no hypothesis on
`adv` itself**.

This gives a second, closure-flavoured reformulation of the open question, complementing the
observability one: `adv` is two-stage iff it has *some* finite free disclosure whose diary is
weakly RT-closed. -/

section DiaryClosure

variable {adv : Advice α Γ}

omit [Alphabet α] [Alphabet Γ] in
/-- Two advices agree as soon as their underlying word functions do; the length field is a
proof and hence irrelevant. -/
lemma advice_ext {β : Type} {adv₁ adv₂ : Advice α β} (h : adv₁.f = adv₂.f) :
    adv₁ = adv₂ := by
  cases adv₁; cases adv₂; subst h; rfl

omit [Alphabet α] [Alphabet Γ] in
/-- **The prefix diary is causal by construction.** Truncating the input truncates the diary,
because entry `i` only reads `w.take (i+1)`. -/
theorem Advice.FreeProbe.disclosure_causal (probe : adv.FreeProbe Δ) :
    probe.disclosure.causal := by
  intro w
  refine ⟨probe.disclosure.len w, fun i => ?_⟩
  apply List.ext_getElem
  · show (probe.disclosure.f (w.take i)).length = ((probe.disclosure.f w).take i).length
    simp [Advice.FreeProbe.disclosure]
  · intro j h1 h2
    -- `j` indexes into the truncated diary, so `j < i`; hence the two prefixes agree.
    have hj : j < i := by
      simp only [Advice.FreeProbe.disclosure, List.length_map, List.length_range,
        List.length_take] at h1
      omega
    simp only [Advice.FreeProbe.disclosure, List.getElem_take, List.getElem_map,
      List.getElem_range, List.take_take]
    rw [show min (j + 1) i = j + 1 from by omega]

/-- **A weakly RT-closed diary makes the advice two-stage.**

The diary is causal, so weak RT closure upgrades it to a CART presentation
(`is_cart_advice_of_rt_closed_and_causal`); feeding that transducer into the reconstruction
transducer `h.M` is literally a two-stage presentation of `adv`. Note that nothing is assumed
about `adv` — the closure hypothesis sits on the diary alone. -/
def Advice.IsFiniteFreeDisclosure.toTwoStage (h : adv.finite_free_disclosure)
    (hclosed : h.probe.disclosure.weak_rt_closed) : adv.is_two_stage_advice := by
  obtain ⟨C, hC⟩ := is_cart_advice_of_rt_closed_and_causal h.probe.disclosure hclosed
    h.probe.disclosure_causal
  have htrace : C.trace_rt = h.probe.disclosure.f := congrArg Advice.f hC
  exact
    { witness := { β := h.Δ, C := C, M := h.M }
      spec := advice_ext (funext fun w => by
        show h.M.scanr (C.trace_rt w) = adv w
        rw [htrace]
        exact h.spec w) }

/-- **Two-stage ⟺ some diary is weakly RT-closed.**

The forward direction uses the first stage's final-output probe, whose diary is exactly the
CART trace and hence closed. This replaces the observability obligation of
`Advice.finite_rt_disclosure_iff_observable_free_disclosure` by a closure obligation on a
*causal* advice — the one class where closure is completely understood. -/
theorem Advice.two_stage_iff_rt_closed_diary (adv : Advice α Γ) :
    Nonempty adv.is_two_stage_advice ↔
      ∃ h : adv.finite_free_disclosure, Nonempty h.probe.disclosure.weak_rt_closed := by
  constructor
  · show Nonempty adv.is_two_stage_advice → _
    rintro ⟨h⟩
    obtain ⟨W, rfl⟩ := h
    refine ⟨W.finite_rt_disclosure.finite_free_disclosure, ?_⟩
    -- The diary of the final-output probe is exactly the CART trace, i.e. `W.C.advice`.
    have hdiary : (W.finite_rt_disclosure.finite_free_disclosure).probe.disclosure
        = W.C.advice :=
      advice_ext (funext fun w => W.C.final_output_probe_disclosure W.advice w)
    rw [hdiary]
    exact ⟨(Advice.is_cart_advice.is_two_stage (⟨W.C, rfl⟩ : W.C.advice.is_cart_advice)).weak_rt_closed⟩
  · show (∃ h : adv.finite_free_disclosure, Nonempty h.probe.disclosure.weak_rt_closed) → _
    rintro ⟨h, ⟨hclosed⟩⟩
    exact ⟨h.toTwoStage hclosed⟩

end DiaryClosure

end CellularAutomatas
