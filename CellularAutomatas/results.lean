import CellularAutomatas.defs
import CellularAutomatas.proofs.advice_theory.middle_not_two_stage
import CellularAutomatas.proofs.advice_theory.rt_closed.of_prefix_mem
import CellularAutomatas.proofs.advice_theory.is_two_stage_of_rt_closed_and_causal
import CellularAutomatas.proofs.constructions.left_indep_to_regular
import CellularAutomatas.proofs.constructions.left_indep_from_regular
import CellularAutomatas.proofs.constructions.speedup_left_independent
import CellularAutomatas.proofs.constructions.border_quiescent_left_independent
import CellularAutomatas.proofs.constructions.border_dead
import CellularAutomatas.proofs.constructions.speedup_k_step
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_cart
import CellularAutomatas.proofs.advice_theory.rt_closed.of_two_stage
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_two_stage
import CellularAutomatas.proofs.advice_theory.rt_closed.of_compose
import CellularAutomatas.proofs.constructions.basic_exp_word
import CellularAutomatas.proofs.rt_eq_2n_iff_rt_eq_rt_rev.rt_eq_2n_iff_rt_eq_rt_rev
import CellularAutomatas.proofs.language.dfa_to_left_indep_ca
import CellularAutomatas.proofs.language.oca_rt_proper_subset_ca_rt
import CellularAutomatas.proofs.language.oca_rt_unary_regular
import CellularAutomatas.proofs.constructions.linear_time_speedup
import CellularAutomatas.proofs.constructions.speedup_right_border_oca
import CellularAutomatas.proofs.language.oca_reversal_equivalences
import CellularAutomatas.proofs.advice_theory.middle_exp_two_stage
import CellularAutomatas.proofs.advice_theory.middle_iff_compress2_weak_rt_closed
import CellularAutomatas.proofs.advice_theory.rt_eq_lt_iff_compress2_weak_rt_closed

/-!
# Stable Results

This module is the curated public theorem surface of the project. It exposes
the principal construction, language-class, and advice results while leaving
implementation lemmas in their owning proof modules.

Run `lake build verify_proofs` to check the configured axiom policy for this
module and the other stable proof modules.
-/

open CellularAutomatas

namespace CellularAutomatas.results

variable {α} [Alphabet α]
variable {Γ} [Alphabet Γ]

/-!
## 1. Simulation and boundary control

The first group is the construction toolkit used by the later language-class
results. The two diagonal simulations translate between unrestricted and
one-way information flow. The following border and speedup constructions make
those simulations usable at exact observation times.
-/

section SimulationAndBoundaryResults

/-- A left-independent CA can be simulated by an unrestricted CA along a
  space-time diagonal: one simulator step performs two original steps.

  **Proof idea.** Left independence makes the missing left predecessor
  irrelevant, so the new local rule composes two applications of the
  original rule in one step. After `t` simulator steps, the original value
  lies at time `2 * t` and shifted position `i - t`. -/
theorem result_left_indep_to_regular
    {β : Type} [Alphabet β] (C : CellAutomaton α β)
    (h_left_indep : C.left_independent)
    (c : Config α) (t : ℕ) (i : ℤ) :
    let e := LeftIndepToRegular.mk C h_left_indep
    e.C.comp c t i = C.comp c (2 * t) (i - t) := by
  intro e
  exact LeftIndepToRegular.spec e c t i

/-- Conversely, a left-independent CA can encode an unrestricted CA along the
  opposite diagonal, with one original step represented by two simulator
  steps.

  **Proof idea.** The simulator alternates between `single` states and
  `pair` states containing adjacent original states. The pair phase supplies
  the information normally received from the left, allowing the transition
  itself to ignore its left argument. At time `2 * t`, a `single` state
  contains the original value at `(t, i + t)`. -/
theorem result_regular_to_left_indep
    {β : Type} [Alphabet β] (C : CellAutomaton α β)
    (c : Config α) (t : ℕ) (i : ℤ) :
    let e := RegularToLeftIndep.mk C
    e.C.comp c (2 * t) i = .single (C.comp c t (i + t)) := by
  intro e
  exact RegularToLeftIndep.spec_even e c t i

/-- The preceding encoding really is a one-way automaton.

  **Proof idea.** Its transition is defined entirely from the center and
  right encoded states. A case split over the encoded state constructors
  therefore proves that changing the left neighbor changes nothing. -/
theorem result_regular_to_left_indep_is_left_indep
    {β : Type} [Alphabet β] (C : CellAutomaton α β) :
    (RegularToLeftIndep.mk C).C.left_independent :=
  RegularToLeftIndep.C_left_independent _

/-- A left-independent CA can be given a quiescent border while preserving its
  computation inside the one-way light cone.

  **Proof idea.** The enlarged state records enough of the original border's
  evolution to reproduce it inside the cone, while its new external border
  is fixed by the local rule. An induction over the cone proves agreement;
  outside it, the new CA projects the quiescent border value. This is the
  boundary preparation needed by the block speedup below. -/
theorem result_quiescent_border_spec
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β)
    (h_left_indep : C.left_independent) :
    let C' := (QuiescentBorderLeftIndep.mk C h_left_indep).C
    C'.quiescent C'.border
      ∧ C'.left_independent
      ∧ ∀ (w : Word α) (_hw : w.length > 0) (t : ℕ) (i : ℤ),
          C'.comp w t i =
            if i ∈ WordConeLeftIndep w t then C.comp w t i
            else C.project C.border :=
  ⟨QuiescentBorderLeftIndep.C_border_quiescent _,
    QuiescentBorderLeftIndep.C_left_indep _,
    fun w hw t i =>
      QuiescentBorderLeftIndep.spec
        (QuiescentBorderLeftIndep.mk C h_left_indep) w hw t i⟩

/-- The `k`-step left-independent speedup stores `k` consecutive diagonal
    states in each cell.

    **Proof idea.** First make the border quiescent using the preceding
    construction. A compressed cell can then update a width-`k` tuple locally,
    advancing several points of the original diagonal at once. Component `j`
    gives the original state at the exact time and position displayed below. -/
theorem result_left_indep_speedup
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (k : ℕ) (hk : k ≥ 2)
    (h_left_indep : C.left_independent)
    (w : Word α) (hw : w.length > 0) (t : ℕ) (i : ℤ)
    (hi2 : -(t : ℤ) ≤ i) (hi : i < 0) (j : Fin k) :
    let e := LeftIndepSpeedup.mk C k hk h_left_indep
    (e.C.comp w t i) j =
    C.comp w (t - ((k - 1) * i) - j).toNat (k * i + j) := by
  intro e
  exact LeftIndepSpeedup.spec e w hw t i hi2 hi j

/-- Any CA can be given a dead border while preserving its trace for a chosen
    linear-time window.

    **Proof idea.** The construction folds a bounded family of simulated tape
    lanes into each cell. Those lanes contain every original dependency that
    can reach position `0` before `c_const * w.length`; states beyond the
    folded region collapse to an absorbing dead border. Coordinate lemmas then
    show that the observed trace is unchanged throughout that window. -/
theorem result_dead_border_spec
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β) (c_const : ℕ) :
    let C' := (DeadBorder.mk ⟨ c_const ⟩ C).C
    C'.dead C'.border
    ∧ ∀ (w : Word α) (t : ℕ) (_h : t < c_const * w.length),
      C'.trace w t = C.trace w t :=
  ⟨@DeadBorder.spec_left_border_dead { c := c_const, C_orig := C },
    fun _w _t h =>
      @DeadBorder.spec_comp_trace { c := c_const, C_orig := C } _ _ h⟩

/-- A CA can be sped up by any fixed number `k` of steps throughout a chosen
    linear-time window: at time `i`, the new CA exposes the original trace at
    time `i + k`.

    **Proof idea.** The one-step construction stores both the current state and
    a function describing the next update's dependence on the unknown left
    predecessor. Once `i ≥ w.length - 1`, a dead left border supplies that
    predecessor, so the function reveals one future trace value. Before each
    iteration, `DeadBorder` restores this invariant without changing the trace
    below `c * w.length`; iterating it `k` times gives the stated additive
    speedup. -/
theorem result_constant_step_speedup
    {β : Type} [Alphabet β] (C : CellAutomaton α？ β)
    (k c : ℕ) (w : Word α) (i : ℕ)
    (h_len : i ≥ w.length - 1) (h_bound : i + k < c * w.length) :
    let e : SpeedupKSteps := { C_orig := C, k := k, c := c }
    e.C.trace w i = C.trace w (i + k) := by
  intro e
  exact e.spec w i h_len h_bound

end SimulationAndBoundaryResults

/-!
## 2. Expressive power in real time

One-way real-time CAs already contain all regular languages, but over a unary
alphabet they contain nothing more. A signal-and-mirror construction gives an
unrestricted real-time CA a nonregular unary language, yielding the strict
separation at the end of the section.
-/

section ExpressivePowerResults

/-- Every DFA language is recognizable by a one-way real-time CA.

    **Proof idea.** Position `0` starts with the DFA transition on the first
    input symbol. At each CA step, the center state consumes the symbol carried
    by its right neighbor, so after `n - 1` steps it contains the DFA state for
    the complete word. The rule never inspects the left neighbor and is
    therefore an OCA rule. -/
theorem result_dfa_subset_OCA_rt
    {σ : Type} [Fintype σ] [DecidableEq σ] [Inhabited σ] :
    ℒ (DFA α σ) ⊆ ℒ (OCA_rt α) :=
  dfa_subset_OCA_rt

/-- Every unary real-time one-way CA language is regular.

    **Proof idea.** On a unary word, the one-way light cone remains uniform
    until the right boundary arrives. Its evolution at position `0` is thus an
    iteration of the finite map `q ↦ C.δ q q q`. A DFA stores that iterated
    state; over `Unit`, every word belongs to this unary slice. -/
theorem oca_rt_unary_regular : ∀ L ∈ ℒ (OCA_rt Unit), L.IsRegular :=
  CellularAutomatas.oca_rt_unary_regular

/-- The powers-of-two length language is recognizable by a real-time CA.

    **Proof idea.** A setup automaton feeds a signal-and-mirror machine. The
    signal repeatedly travels from the left edge to a moving mirror and back;
    the return intervals double, so the accepting returns occur exactly at
    lengths `2 ^ n`. The projection separately handles the singleton base
    case. -/
theorem exp_word_length_rt :
    ∃ C : CA_rt Unit, C.L = { w | ∃ n, w.length = 2 ^ n } :=
  CellularAutomatas.exp_word_length_rt

/-- One-way real-time CAs recognize strictly fewer languages than unrestricted
    real-time CAs.

    **Proof idea.** Inclusion simply forgets the left-independence proof. For
    strictness, lift `exp_word_length_rt` from `Unit` to any alphabet by erasing
    symbols. If an OCA recognized this powers-of-two length language, its unary
    slice at a fixed letter would be regular by the generalized unary-slice
    theorem underlying `oca_rt_unary_regular`, contradicting nonregularity of
    the powers-of-two lengths. -/
theorem oca_rt_proper_subset_ca_rt {α : Type} [Alphabet α] :
    ℒ (OCA_rt α) ⊂ ℒ (CA_rt α) :=
  CellularAutomatas.oca_rt_proper_subset_ca_rt

end ExpressivePowerResults

/-!
## 3. Speedup, observation geometry, and reversal

Linear time first collapses to the canonical bound `2 * (n - 1)`. Diagonal
simulations then reinterpret that time bound as a change of observation
position. Spatial reflection turns those coordinate identities into reversal
identities, culminating in the equivalence between the RT/LT question and
closure of real-time languages under reversal.
-/

section TimeAndReversalResults

/-- Linear-time speedup: two-way CAs need no more than `2 * (n - 1)` time.

    **Proof idea.** For a coefficient `c ≥ 2`, first compute width-`c`
    compression advice in `n` steps, then run a quiescent-border block CA for
    another `n` steps to simulate `c * (n - 1)` original steps. The resulting
    proper-time `2 * n` recognizer is normalized to `2 * (n - 1)` by a constant
    speedup; coefficients `0` and `1` are handled separately. The reverse
    inclusion is the immediate choice `c = 2`. -/
theorem ca_2n_eq_ca_lt : ℒ (CA_2n α) = ℒ (CA_lt α) :=
  CellularAutomatas.ca_2n_eq_ca_lt

/-- Linear-time speedup for one-way CAs: every linear-time OCA language is
    recognized by an OCA in time `2 * (n - 1)`.

    **Proof idea.** After making the right border quiescent, the construction
    compresses by `c - 1` and updates each tuple using only the center and right
    neighbors. At time `2 * (n - 1)`, component `c - 2` is exactly the original
    state at time `c * (n - 1)`. Coefficients below `3` are handled directly or
    by a delay, and every case preserves left independence. -/
theorem oca_linear_time_eq_2n : ℒ (OCA_lt α) = ℒ (OCA_2n α) :=
  (CellularAutomatas.OCA_2n_eq_OCA_lt α).symm

/-- A `2 * (n - 1)`-time OCA is equivalent to a right-reading real-time CA.

    **Proof idea.** Apply the two diagonal simulations from Section 1. The
    identity
    `regular(t, i) = leftIndependent(2 * t, i - t)` sends the OCA observation
    `(2 * (n - 1), 0)` to the right-reading point `(n - 1, n - 1)`, and the
    converse simulation recovers the OCA. -/
theorem oca_2n_eq_car_rt : ℒ (OCA_2n α) = ℒ (CAr_rt α) :=
  CellularAutomatas.oca_2n_eq_car_rt

/-- A `2 * (n - 1)`-time OCA observed at `-(n - 1)` is equivalent to a
    left-reading real-time CA.

    **Proof idea.** The same diagonal identities now send the OCA observation
    `(2 * (n - 1), -(n - 1))` to `(n - 1, 0)`. Thus changing only the readout
    coordinate recovers the standard real-time class. -/
theorem oca_2n_left_neg_np1_eq_ca_rt :
    ℒ (OCA_2n_left_neg_np1 α) = ℒ (CA_rt α) :=
  CellularAutomatas.oca_2n_left_neg_np1_eq_ca_rt

/-- Reversing linear-time OCA languages gives exactly the languages of
  right-reading linear-time right-independent CAs.

  **Proof idea.** Spatially flip the local rule and reverse the embedded
  input. A left-independent rule becomes right-independent, position `0`
  becomes position `n - 1`, and the flipped run accepts exactly the reversed
  language. Flipping twice supplies the converse inclusion. -/
theorem oca_lt_rev_eq_ocar_lt : ℒ_rev (OCA_lt α) = ℒ (OCAr_lt α) :=
  CellularAutomatas.oca_lt_rev_eq_ocar_lt

/-- Right-reading right-independent linear-time CAs recognize exactly the
  real-time CA languages.

  **Proof idea.** Flip to reversed OCA languages, replace OCA linear time by
  `2 * (n - 1)` using `oca_linear_time_eq_2n`, and apply the right-reading
  diagonal equivalence. Reversal is involutive, so the resulting class is
  exactly `CA_rt`. -/
theorem ocar_lt_eq_ca_rt : ℒ (OCAr_lt α) = ℒ (CA_rt α) :=
  CellularAutomatas.ocar_lt_eq_ca_rt

/-- Collecting the preceding geometry, real-time CA languages are equivalently
  reversed `2 * (n - 1)`-time OCA languages, reversed linear-time OCA
  languages, or `2 * (n - 1)`-time OCA languages observed at `-(n - 1)`.

  **Proof idea.** Chain `oca_2n_eq_car_rt`, spatial flip, OCA speedup, and
  `oca_2n_left_neg_np1_eq_ca_rt`. Packaging all three equalities in one
  theorem exposes the complete time/position/reversal diagram to downstream
  proofs. -/
theorem ca_rt_eq_rev_oca :
    ℒ (CA_rt α) = ℒ_rev (OCA_2n α) ∧
    ℒ_rev (OCA_2n α) = ℒ_rev (OCA_lt α) ∧
    ℒ_rev (OCA_lt α) = ℒ (OCA_2n_left_neg_np1 α) :=
  CellularAutomatas.ca_rt_eq_rev_oca

/-- Globally over all alphabets, real time equals linear time exactly when
  real-time languages are closed under reversal.

  **Proof idea.** If RT equals LT, a reversed RT language first lies in the
  canonical `2 * (n - 1)` class by the OCA/reversal diagram and hence returns
  to RT by the assumed equality. Conversely, start with a
  `2 * (n - 1)`-time language, add a fresh `Option` padding symbol, and use a
  double-reversal argument: suffix-pad, reverse, remove the padding, and
  reverse again. This moves from `β` to `Option β`, which is why the
  reversal-closure hypothesis in this hard direction must be uniform over all
  finite alphabets. Finally `ca_2n_eq_ca_lt` replaces the canonical bound by
  linear time. -/
theorem result_rt_eq_lt_iff_rt_eq_rt_rev :
    (∀ (β : Type) [Alphabet β], ℒ (CA_rt β) = ℒ (CA_lt β)) ↔
    (∀ (γ : Type) [Alphabet γ], ℒ (CA_rt γ) = ℒ_rev (CA_rt γ)) := by
  simp [← ca_2n_eq_ca_lt, rt_eq_2n_iff_rt_eq_rt_rev]

end TimeAndReversalResults

/-!
## 4. Real-time transducers and advice

The final group studies length-preserving word annotations. A two-stage advice
first takes the temporal trace of a real-time CA and then applies a finite-state
right-to-left scan. The first results show that these descriptions can be
eliminated from real-time recognition and compose robustly. The final results
recast the RT/LT question from Section 3 as the eliminability of one concrete
compression advice.
-/

section TransducerAndAdviceResults

/-- Real-time CA transductions are closed under composition.

  **Proof idea.** The second transducer cannot wait for the first trace to be
  completed. Instead, the construction places triples from the first trace
  on a space-time diagonal, simulates a threefold speedup of the second CA
  from that diagonal, decompresses its output, and removes the fixed startup
  delay. The resulting trace is pointwise the functional composition. -/
theorem result_rt_transducers_closed_under_composition
    {β γ : Type} [Alphabet β] [Alphabet γ]
    (C1 : CellAutomaton α？ β) (C2 : CellAutomaton β？ γ) :
    (C2.compose_trace_rt C1).trace_rt = C2.trace_rt ∘ C1.trace_rt :=
  CellAutomaton.compose_trace_rt_spec C2 C1

/-- Every two-stage advice can be eliminated from real-time recognition, even
  after changing the input alphabet through a map into the base alphabet.

  **Proof idea.** Pair an identity trace with the advice trace, compose this
  two-stage word function with the advised recognizer's own trace, and read
  the final Boolean output. This gives weak RT-closure. Mapping the first
  CA's embedding along an arbitrary `S → α` repeats the construction for
  every lifted alphabet, giving uniform `rt_closed`. -/
def result_two_stage_is_rt_closed
    (adv : TwoStageAdvice α Γ) :
    adv.advice.rt_closed :=
  two_stage_is_rt_closed adv

/-- Prefix-membership advice for a real-time language is two-stage.

  At position `i`, this advice records whether the prefix ending at `i`
  belongs to the language.

  **Proof idea.** The real-time trace of the recognizing CA already records
  exactly those prefix decisions. Use that CA as the first stage and the
  identity finite-state transducer as the right-to-left stage. -/
def result_advice_prefix_mem_is_two_stage_advice :
    ∀ C : CA_rt α, Advice.is_two_stage_advice (Advice.prefix_mem C.L) :=
  advice_prefix_mem_is_two_stage_advice

/-- Causal weakly RT-closed advice is computed by a single real-time CA
  trace.

  **Proof idea.** For each possible advice symbol `c`, weak RT-closure turns
  the language “the last advice symbol is `c`” into an unadvised real-time
  recognizer. Run all these recognizers in parallel and select the unique
  accepted symbol. Causality identifies its answer on each prefix with the
  advice symbol at the corresponding position, so the combined trace is the
  complete advice word. -/
def result_is_cart_advice_of_rt_closed_and_causal :
    ∀ adv : Advice α Γ,
      adv.weak_rt_closed → adv.causal → adv.is_cart_advice :=
  is_cart_advice_of_rt_closed_and_causal

/-- Two-stage advice is closed under composition.

  **Proof idea.** Naive substitution produces the stages in the bad order
  `FST₂ ∘ CA₂ ∘ FST₁ ∘ CA₁`. The `backwards_fsm` construction commutes
  `CA₂` past `FST₁` by simulating the CA for every possible finite-state
  summary and letting a new FST select the correct branch. The two CA traces
  and the two finite-state scans can then each be composed. -/
theorem result_two_stage_closed_under_composition
    {Γ' : Type} [Alphabet Γ']
    (a1 : TwoStageAdvice α Γ') (a2 : TwoStageAdvice Γ' Γ) :
    (compose_two_stage a2 a1 : TwoStageAdvice α Γ).advice =
      a2.advice ∘ a1.advice :=
  compose_two_stage_spec a1 a2

/-- Uniformly RT-closed advice is closed under composition.

    **Proof idea.** To eliminate `f₂ (f₁ w)`, first lift the uniform closure of
    `f₂` to the decorated alphabet carrying both `f₁ w` and `w`. After
    reassociating and swapping the zipped tracks, eliminate `f₁` using its own
    closure. Uniformity is essential for that intermediate alphabet change. -/
noncomputable def result_rt_closed_compose_rt_closed
    {Γ' : Type} [Alphabet Γ']
    (f₁ : Advice α Γ') (f₂ : Advice Γ' Γ)
    (h₁ : f₁.rt_closed) (h₂ : f₂.rt_closed) :
    (f₁.compose f₂).rt_closed :=
  Advice.rt_closed_compose_rt_closed f₁ f₂ h₁ h₂

/-- The exponential-middle marker is computable in two stages. It marks the
    largest power of two `p` satisfying `2 * p ≤ w.length`.

    **Proof idea.** The first-stage CA trace marks every prefix whose length is
    a power of two, using the powers-of-two recognizer from Section 2. A
    finite-state scan from the right selects the second such marker, which is
    exactly the largest `p` with `2 * p ≤ w.length`. -/
def middle_exp_two_stage_advice :
    (Advice.middle_exp α).is_two_stage_advice :=
  CellularAutomatas.middle_exp_two_stage_advice

/-- The ordinary middle-marker advice is not two-stage.

    **Proof idea.** Fix a long constant prefix. By choosing different suffix
    lengths, the middle marker induces arbitrarily many distinct observable
    prefix patterns. A two-stage representation can distinguish at most one
    such pattern per state of its finite-state second stage. Taking more
    patterns than states gives the contradiction. -/
theorem result_middle_not_two_stage_advice :
    IsEmpty (Advice.middle α).is_two_stage_advice :=
  middle_not_two_stage_advice

/-- Over a unary alphabet, middle-marker advice and width-two compression
  advice have equivalent weak real-time closure behavior.

  **Proof idea.** Explicit RT-closed post-processors translate each advice
  into the other. One direction extracts the middle marker from adjacent
  pairs. The other enriches the middle marker with parity and left-neighbor
  information, then reconstructs the adjacent pairs. Composing either
  post-processor preserves weak RT-closure. -/
theorem middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary :
    Nonempty (Advice.middle Unit).weak_rt_closed ↔
    Nonempty (Advice.compress2 Unit).weak_rt_closed :=
  CellularAutomatas.middle_weak_rt_closed_iff_compress2_weak_rt_closed_unary

/-- Real time equals linear time exactly when width-two compression advice can
  be eliminated from real-time recognizers.

  **Proof idea.** If `compress2` is weakly RT-closed, annotate each input with
  adjacent symbol pairs, use the factor-two block simulation to run any
  `CA_2n` machine in real time, and eliminate the annotation; Section 3 then
  gives all of `CA_lt`. Conversely, `compress2` itself is computable in
  linear time, so any real-time recognizer using it defines a linear-time
  language. Under `CA_rt = CA_lt`, that language has an unadvised real-time
  recognizer, which is precisely weak RT-closure. -/
theorem ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed :
    ℒ (CA_rt α) = ℒ (CA_lt α) ↔
    Nonempty (Advice.compress2 α).weak_rt_closed :=
  CellularAutomatas.ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed

end TransducerAndAdviceResults
