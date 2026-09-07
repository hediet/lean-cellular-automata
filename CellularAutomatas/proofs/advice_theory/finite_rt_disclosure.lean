import CellularAutomatas.proofs.advice_theory.is_two_stage_of_rt_closed_and_causal
import CellularAutomatas.proofs.ca_rt_utils
import CellularAutomatas.proofs.language.dfa_to_left_indep_ca

namespace CellularAutomatas

open Classical

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- An unrestricted finite observation of a complete word. Unlike an RT probe,
its fibers need not be recognizable using the advice. -/
structure Advice.FreeProbe (adv : Advice α Γ) (Δ : Type) where
  value : Word α → Δ

/-- The free-probe value on every nonempty prefix of the input word. -/
def Advice.FreeProbe.disclosure
    {Δ : Type} [Alphabet Δ]
    {adv : Advice α Γ}
    (probe : adv.FreeProbe Δ) :
    Advice α Δ :=
  {
    f := fun w =>
      (List.range w.length).map fun i =>
        probe.value (w.take (i + 1))
    len := by simp
  }

/-- A finite observation whose fibers are recognizable in real time using `adv`. -/
structure Advice.RtProbe (adv : Advice α Γ) (Δ : Type)
    extends adv.FreeProbe Δ where
  recognizer : Δ → CA_rt (α × Γ)
  spec : ∀ d w, w ∈ (recognizer d + adv).L ↔ value w = d

/-- The probe value on every nonempty prefix of the input word. -/
def Advice.RtProbe.disclosure
    {Δ : Type} [Alphabet Δ]
    {adv : Advice α Γ}
    (probe : adv.RtProbe Δ) :
    Advice α Δ :=
  probe.toFreeProbe.disclosure

/-- An advice has finite free disclosure when an unrestricted finite probe's
prefix diary can be scanned from right to left to reconstruct the advice. -/
structure Advice.IsFiniteFreeDisclosure (adv : Advice α Γ) where
  Δ : Type
  [alphabetΔ : Alphabet Δ]
  probe : adv.FreeProbe Δ
  M : FiniteStateTransducer Δ Γ
  spec : ∀ w, M.scanr (probe.disclosure w) = adv w

attribute [instance] Advice.IsFiniteFreeDisclosure.alphabetΔ

abbrev Advice.finite_free_disclosure (adv : Advice α Γ) :=
  adv.IsFiniteFreeDisclosure

/-- An advice has finite RT disclosure when a finite probe's prefix diary can
be scanned from right to left to reconstruct the advice. -/
structure Advice.IsFiniteRtDisclosure (adv : Advice α Γ) where
  Δ : Type
  [alphabetΔ : Alphabet Δ]
  probe : adv.RtProbe Δ
  M : FiniteStateTransducer Δ Γ
  spec : ∀ w, M.scanr (probe.disclosure w) = adv w

attribute [instance] Advice.IsFiniteRtDisclosure.alphabetΔ

abbrev Advice.finite_rt_disclosure (adv : Advice α Γ) :=
  adv.IsFiniteRtDisclosure

/-- Forgetting the recognizers of a finite RT disclosure leaves a finite free
disclosure with the same diary and reconstruction transducer. -/
def Advice.IsFiniteRtDisclosure.finite_free_disclosure
    {adv : Advice α Γ} (h : adv.finite_rt_disclosure) :
    adv.finite_free_disclosure where
  Δ := h.Δ
  probe := h.probe.toFreeProbe
  M := h.M
  spec := h.spec

/-- The graph of an advice, represented by a word whose first track is the
input and whose second track is a candidate advice word. -/
def Advice.graph_language (adv : Advice α Γ) : Language (α × Γ) :=
  { paired | paired.map Prod.snd = adv (paired.map Prod.fst) }

omit [Alphabet α] [Alphabet Γ] in
@[simp]
lemma Advice.zip_mem_graph_language_iff (adv : Advice α Γ)
    (input : Word α) (candidate : Word Γ)
    (h_length : candidate.length = input.length) :
    input ⨂ candidate ∈ adv.graph_language ↔ candidate = adv input := by
  have h_input_length : input.length ≤ candidate.length := by omega
  have h_candidate_length : candidate.length ≤ input.length := by omega
  change (input ⨂ candidate).map Prod.snd =
    adv ((input ⨂ candidate).map Prod.fst) ↔ _
  rw [List.map_snd_zip h_candidate_length, List.map_fst_zip h_input_length]

omit [Alphabet α] [Alphabet Γ] in
/-- For each input, its advice is the unique equal-length candidate in the
graph. This is the semantic specification used by exhaustive search. -/
theorem Advice.existsUnique_candidate_in_graph (adv : Advice α Γ)
    (input : Word α) :
    ∃! candidate : Word Γ,
      candidate.length = input.length ∧
        input ⨂ candidate ∈ adv.graph_language := by
  refine ⟨adv input, ?_, ?_⟩
  · show (adv input).length = input.length ∧
      input ⨂ adv input ∈ adv.graph_language
    exact ⟨adv.len input, (adv.zip_mem_graph_language_iff input (adv input)
      (adv.len input)).2 rfl⟩
  · intro candidate h_candidate
    show candidate = adv input
    exact (adv.zip_mem_graph_language_iff input candidate h_candidate.1).1
      h_candidate.2

/-- A fixed DFA that checks whether the candidate component of every input
symbol agrees with the corresponding supplied advice symbol. -/
private def adviceGraphDFA : DFA ((α × Γ) × Γ) Bool where
  step := fun valid symbol => valid && decide (symbol.1.2 = symbol.2)
  start := true
  accept := {true}

private instance adviceGraphDFA_accept_decidable :
    DecidablePred (· ∈ (adviceGraphDFA (α := α) (Γ := Γ)).accept) := by
  intro valid
  change Decidable (valid = true)
  infer_instance

omit [Alphabet α] in
private lemma adviceGraphDFA_evalFrom_zip
    (valid : Bool) (paired : Word (α × Γ)) (candidate : Word Γ)
    (h_length : candidate.length = paired.length) :
    adviceGraphDFA.evalFrom valid (paired ⨂ candidate) =
      (valid && decide (paired.map Prod.snd = candidate)) := by
  induction paired generalizing valid candidate with
  | nil =>
      have h_candidate : candidate = [] := by
        simpa using h_length
      subst candidate
      simp [DFA.evalFrom]
  | cons symbol paired ih =>
      cases candidate with
      | nil => simp at h_length
      | cons adviceSymbol candidate =>
          simp only [List.length_cons, Nat.succ.injEq] at h_length
          change adviceGraphDFA.evalFrom
              (valid && decide (symbol.2 = adviceSymbol))
              (paired ⨂ candidate) =
            (valid && decide
              (List.map Prod.snd (symbol :: paired) = adviceSymbol :: candidate))
          rw [ih (valid && decide (symbol.2 = adviceSymbol)) candidate h_length]
          by_cases h_equal : symbol.2 = adviceSymbol <;> simp [h_equal]

/-- The advised real-time checker for the advice graph. -/
private def adviceGraphChecker : CA_rt ((α × Γ) × Γ) :=
  toRtCa (DFAtoCA adviceGraphDFA)

private lemma adviceGraphChecker_spec
    (paired : Word (α × Γ)) (candidate : Word Γ)
    (h_length : candidate.length = paired.length) :
    adviceGraphChecker.accepts (paired ⨂ candidate) ↔
      paired.map Prod.snd = candidate := by
  unfold adviceGraphChecker
  rw [DFAtoCA.accepts_iff]
  change adviceGraphDFA.evalFrom true (paired ⨂ candidate) = true ↔ _
  rw [adviceGraphDFA_evalFrom_zip true paired candidate h_length]
  simp

/-- If the advice lifted to candidate-decorated inputs is weakly RT-closed,
one fixed unadvised real-time CA recognizes the full advice graph. -/
def Advice.graphCaOfLiftWeakRtClosed (adv : Advice α Γ)
    (hclosed : (adv.lift (β := α × Γ) Prod.fst).weak_rt_closed) :
    CA_rt (α × Γ) :=
  hclosed.map adviceGraphChecker

@[simp]
lemma Advice.graphCaOfLiftWeakRtClosed_spec (adv : Advice α Γ)
    (hclosed : (adv.lift (β := α × Γ) Prod.fst).weak_rt_closed) :
    (adv.graphCaOfLiftWeakRtClosed hclosed).L = adv.graph_language := by
  show (hclosed.map adviceGraphChecker).L = adv.graph_language
  rw [hclosed.spec]
  ext paired
  change adviceGraphChecker.accepts
      ((adv.lift (β := α × Γ) Prod.fst).annotate paired) ↔
    paired.map Prod.snd = adv (paired.map Prod.fst)
  unfold Advice.annotate
  rw [adviceGraphChecker_spec]
  · rfl
  · simp [Advice.lift, adv.len]

/-- Uniform RT closure supplies weak closure on the candidate-decorated
alphabet, so the advice graph itself is a real-time CA language. -/
def Advice.graphCa (adv : Advice α Γ) (hclosed : adv.rt_closed) :
    CA_rt (α × Γ) :=
  adv.graphCaOfLiftWeakRtClosed (hclosed (α × Γ) Prod.fst)

@[simp]
lemma Advice.graphCa_spec (adv : Advice α Γ) (hclosed : adv.rt_closed) :
    (adv.graphCa hclosed).L = adv.graph_language :=
  adv.graphCaOfLiftWeakRtClosed_spec (hclosed (α × Γ) Prod.fst)

@[simp]
lemma Advice.graphCa_accepts_zip_iff (adv : Advice α Γ)
    (hclosed : adv.rt_closed) (input : Word α) (candidate : Word Γ)
    (h_length : candidate.length = input.length) :
    (adv.graphCa hclosed).accepts (input ⨂ candidate) ↔
      candidate = adv input := by
  change input ⨂ candidate ∈ (adv.graphCa hclosed).L ↔ _
  rw [adv.graphCa_spec hclosed]
  exact adv.zip_mem_graph_language_iff input candidate h_length

/-- The graph-language formulation of advice elimination. -/
theorem Advice.graph_language_in_ca_rt (adv : Advice α Γ)
    (hclosed : adv.rt_closed) :
    adv.graph_language ∈ ℒ (CA_rt (α × Γ)) := by
  rw [ℒ_CA_rt_iff]
  exact ⟨adv.graphCa hclosed, adv.graphCa_spec hclosed⟩

/-- Two suffixes are future-equivalent for `adv` when every left context sees
the same advice on all positions belonging to that context. -/
def Advice.future_equivalent (adv : Advice α Γ) (z z' : Word α) : Prop :=
  ∀ x, (adv (x ++ z)).take x.length = (adv (x ++ z')).take x.length

/-- A concrete finite presentation of the quotient by `future_equivalent`.
The representative field records a chosen word in every finite index class. -/
structure Advice.IsFiniteFutureIndex (adv : Advice α Γ) where
  S : Type
  [alphabetS : Alphabet S]
  index : Word α → S
  representative : S → Word α
  representative_index : ∀ s, index (representative s) = s
  index_eq_iff : ∀ z z',
    index z = index z' ↔ adv.future_equivalent z z'

attribute [instance] Advice.IsFiniteFutureIndex.alphabetS

abbrev Advice.finite_future_index (adv : Advice α Γ) :=
  adv.IsFiniteFutureIndex

omit [Alphabet α] [Alphabet Γ] in
/-- Future equivalence is preserved by prepending the same input symbol. -/
lemma Advice.future_equivalent_cons {adv : Advice α Γ} {z z' : Word α}
    (h_equivalent : adv.future_equivalent z z') (a : α) :
    adv.future_equivalent (a :: z) (a :: z') := by
  intro x
  have h_context := h_equivalent (x ++ [a])
  have h_prefix := congrArg (List.take x.length) h_context
  simpa [List.take_take, List.append_assoc] using h_prefix

-- `Advice.IsFiniteFutureIndex.finite_free_disclosure` lives in
-- `finite_future_variation_iff_free_disclosure`, where it is derived from the strictly weaker
-- `Advice.finite_future_variation`.

namespace CArtTransducer

variable {Δ : Type} [Alphabet Δ]

/-- The final real-time output of a CART, viewed as a probe that ignores the
supplied advice track. -/
def final_output_probe (C : CArtTransducer α Δ) (adv : Advice α Γ) :
    adv.RtProbe Δ where
  value := fun w => C.trace w (w.length - 1)
  recognizer := fun d =>
    (toRtCa (C.map_project fun output => decide (output = d))).map_embed Prod.fst
  spec := by
    intro d w
    rw [tCellAutomatonWithAdvice.elem_L_iff, map_embed_L]
    have h_fst : (adv.annotate w).map Prod.fst = w := by
      unfold Advice.annotate
      apply List.ext_getElem
      · simp [adv.len]
      · intro i h_annotated h_w
        simp
    rw [h_fst, CA_rt_L_iff]
    change decide (C.trace w (w.length - 1) = d) = true ↔ _
    simp

/-- Prefix disclosure of the final-output probe is exactly the CART trace. -/
lemma final_output_probe_disclosure (C : CArtTransducer α Δ)
    (adv : Advice α Γ) (w : Word α) :
  (C.final_output_probe adv).disclosure w = C.trace_rt w := by
  apply List.ext_getElem
  · simp [Advice.RtProbe.disclosure, Advice.FreeProbe.disclosure,
      CellAutomaton.trace_rt]
  · intro i h_disclosure h_trace
    have h_i : i < w.length := by
      simpa [CellAutomaton.trace_rt] using h_trace
    simp only [Advice.RtProbe.disclosure, Advice.FreeProbe.disclosure,
      List.getElem_map, List.getElem_range, final_output_probe,
      CellAutomaton.trace_rt]
    have h_prefix_len : (w.take (i + 1)).length = i + 1 := by
      simp [Nat.min_eq_left (by omega : i + 1 ≤ w.length)]
    rw [h_prefix_len, Nat.add_sub_cancel]
    unfold CellAutomaton.trace
    have h_local := LCellAutomaton.scan_temporal_independence_at_0 C
      (w.take (i + 1)) (w.drop (i + 1)) i (by simp [h_prefix_len])
    rw [List.take_append_drop] at h_local
    exact congrArg C.project h_local.symm

end CArtTransducer

/-- A two-stage presentation is itself a finite RT disclosure presentation:
probe the first stage's final output and reuse the second-stage transducer. -/
def TwoStageAdvice.finite_rt_disclosure (adv : TwoStageAdvice α Γ) :
    adv.advice.finite_rt_disclosure where
  Δ := adv.β
  probe := adv.C.final_output_probe adv.advice
  M := adv.M
  spec := by
    intro w
    change adv.M.scanr ((adv.C.final_output_probe adv.advice).disclosure w) =
      adv.M.scanr (adv.C.trace_rt w)
    rw [adv.C.final_output_probe_disclosure adv.advice]

/-- Finite RT disclosure is invariant under replacing an advice by an equal one. -/
def Advice.IsFiniteRtDisclosure.congr
    {adv₁ adv₂ : Advice α Γ} (h : adv₁.finite_rt_disclosure)
    (h_eq : adv₁ = adv₂) : adv₂.finite_rt_disclosure := by
  subst adv₂
  exact h

/-- Every two-stage advice has finite RT disclosure. -/
def Advice.IsTwoStageAdvice.finite_rt_disclosure
    {adv : Advice α Γ} (h : adv.is_two_stage_advice) :
    adv.finite_rt_disclosure :=
  h.witness.finite_rt_disclosure.congr h.spec

/-- Every two-stage advice is uniformly RT-closed. -/
def Advice.IsTwoStageAdvice.rt_closed
    {adv : Advice α Γ} (h : adv.is_two_stage_advice) :
    adv.rt_closed := by
  rw [← h.spec]
  exact two_stage_is_rt_closed h.witness

/-- Every two-stage advice is weakly RT-closed. -/
def Advice.IsTwoStageAdvice.weak_rt_closed
    {adv : Advice α Γ} (h : adv.is_two_stage_advice) :
    adv.weak_rt_closed :=
  Advice.rt_closed_implies_weak_rt_closed h.rt_closed

namespace Advice

/-- Probe the final advice symbol, using the default symbol on the empty word. -/
def last_symbol_probe (adv : Advice α Γ) : adv.RtProbe Γ where
  value := fun w => (adv w).getLast?.getD default
  recognizer := fun c => fix_empty (decide (c = default)) (CA_adv_L_c α c)
  spec := by
    intro c w
    rw [tCellAutomatonWithAdvice.elem_L_iff, fix_empty_spec]
    by_cases h_empty : w = []
    · simpa [h_empty] using (eq_comm : c = default ↔ default = c)
    · have h_annotated : adv.annotate w ≠ [] := by
        simp [h_empty]
      rw [if_neg (by simpa using h_annotated)]
      have h_last : ∃ g, (adv w).getLast? = some g := by
        have h_adv_nonempty : adv w ≠ [] := by
          simpa [← List.length_eq_zero_iff, adv.len] using h_empty
        exact ⟨(adv w).getLast h_adv_nonempty,
          List.getLast?_eq_getLast_of_ne_nil h_adv_nonempty⟩
      obtain ⟨g, hg⟩ := h_last
      rw [decide_eq_true_eq]
      calc
        adv.annotate w ∈ (CA_adv_L_c α c).L
            ↔ w ∈ (CA_adv_L_c α c + adv).L :=
              (tCellAutomatonWithAdvice.elem_L_iff w).symm
        _ ↔ (adv w).getLast? = some c := by
              rw [CA_adv_L_c_spec]
              rfl
        _ ↔ (adv w).getLast?.getD default = c := by simp [hg]

/-- The last-symbol probe discloses a causal advice exactly. -/
lemma last_symbol_probe_disclosure_of_causal
    (adv : Advice α Γ) (hcausal : adv.causal) (w : Word α) :
  adv.last_symbol_probe.disclosure w = adv w := by
  apply List.ext_getElem
  · simp [Advice.RtProbe.disclosure, Advice.FreeProbe.disclosure, adv.len]
  · intro i h_disclosure h_adv
    simp only [Advice.RtProbe.disclosure, Advice.FreeProbe.disclosure,
      List.getElem_map, List.getElem_range, last_symbol_probe]
    rw [(hcausal w).2 (i + 1)]
    rw [PrefixStableProof.getLastOfTake h_adv]
    rw [List.getElem?_eq_getElem h_adv]
    rfl

/-- Every causal advice has finite RT disclosure, independently of any
RT-closure assumption. -/
def finite_rt_disclosure_of_causal
    (adv : Advice α Γ) (hcausal : adv.causal) :
    adv.finite_rt_disclosure where
  Δ := Γ
  probe := adv.last_symbol_probe
  M := FiniteStateTransducer.M_id Γ
  spec := by
    intro w
    rw [FiniteStateTransducer.M_id_scanr_eq]
    exact adv.last_symbol_probe_disclosure_of_causal hcausal w

omit [Alphabet α] in
/-- Prefix-membership advice is causal for every language. -/
lemma prefix_mem_causal (L : Language α) [DecidablePred L] :
    (Advice.prefix_mem L).causal := by
  intro w
  constructor
  · simp [Advice.prefix_mem]
  · intro i
    apply List.ext_getElem
    · simp [Advice.prefix_mem]
    · intro j h_prefix h_full
      have h_j : j < i ∧ j < w.length := by
        simpa [Advice.prefix_mem] using h_prefix
      simp only [Advice.prefix_mem, List.getElem_map, List.getElem_range,
        List.getElem_take]
      congr 2
      simp [List.take_take, Nat.min_eq_left (by omega : j + 1 ≤ i)]

/-- Prefix-membership advice always has finite RT disclosure. -/
def prefix_mem_finite_rt_disclosure (L : Language α) [DecidablePred L] :
    (Advice.prefix_mem L).finite_rt_disclosure :=
  finite_rt_disclosure_of_causal (Advice.prefix_mem L) (prefix_mem_causal L)

omit [Alphabet α] in
/-- On a nonempty word, the last prefix-membership bit decides membership of
the complete word. -/
lemma prefix_mem_getLast?_eq (L : Language α) [DecidablePred L]
    (w : Word α) (h_nonempty : w ≠ []) :
    (Advice.prefix_mem L w).getLast? = some (decide (w ∈ L)) := by
  have h_advice_nonempty : Advice.prefix_mem L w ≠ [] := by
    intro h_empty
    have : w.length = 0 := by
      simpa [Advice.prefix_mem] using congrArg List.length h_empty
    exact h_nonempty (List.length_eq_zero_iff.mp this)
  rw [List.getLast?_eq_getLast_of_ne_nil h_advice_nonempty,
    List.getLast_eq_getElem]
  simp only [Advice.prefix_mem, List.getElem_map, List.getElem_range,
    List.length_map, List.length_range, List.extract_eq_drop_take,
    List.drop_zero]
  congr 2
  have h_length_ne : w.length ≠ 0 := by
    simpa [List.length_eq_zero_iff] using h_nonempty
  have h_length_pos : 0 < w.length := Nat.pos_of_ne_zero h_length_ne
  have h_endpoint : w.length - 1 + 1 = w.length := by omega
  simp [h_endpoint]
  rfl

/-- If `L` excludes the empty word and is not real-time recognizable, then its
prefix-membership advice cannot be two-stage. -/
theorem prefix_mem_not_two_stage
    (L : Language α) [DecidablePred L]
    (h_empty : [] ∉ L) (h_not_rt : L ∉ ℒ (CA_rt α)) :
    IsEmpty (Advice.prefix_mem L).is_two_stage_advice := by
  constructor
  intro htwoStage
  apply h_not_rt
  rw [ℒ_CA_rt_iff]
  refine ⟨htwoStage.witness.to_CA_rt, ?_⟩
  rw [TwoStageAdvice.to_CA_rt_L]
  ext w
  change (htwoStage.witness.advice w).getLast? = some true ↔ w ∈ L
  rw [htwoStage.spec]
  by_cases h_nonempty : w = []
  · simp [h_nonempty, h_empty, Advice.prefix_mem]
  · rw [prefix_mem_getLast?_eq L w h_nonempty]
    simp

/-- The same prefix-membership advice is not weakly RT-closed: finite
disclosure plus weak closure would force a two-stage presentation. -/
theorem prefix_mem_not_weak_rt_closed
    (L : Language α) [DecidablePred L]
    (h_empty : [] ∉ L) (h_not_rt : L ∉ ℒ (CA_rt α)) :
    IsEmpty (Advice.prefix_mem L).weak_rt_closed := by
  constructor
  intro hclosed
  have htwoStage := is_two_stage_of_rt_closed_and_causal
    (Advice.prefix_mem L) hclosed (prefix_mem_causal L)
  exact (prefix_mem_not_two_stage L h_empty h_not_rt).false htwoStage

/-- In particular, the finitely disclosed prefix-membership advice is not
uniformly RT-closed. -/
theorem prefix_mem_not_rt_closed
    (L : Language α) [DecidablePred L]
    (h_empty : [] ∉ L) (h_not_rt : L ∉ ℒ (CA_rt α)) :
    IsEmpty (Advice.prefix_mem L).rt_closed := by
  constructor
  intro hclosed
  exact (prefix_mem_not_weak_rt_closed L h_empty h_not_rt).false
    (Advice.rt_closed_implies_weak_rt_closed hclosed)

end Advice

namespace Advice.RtProbe

variable {Δ : Type} [Alphabet Δ]
variable {adv : Advice α Γ}

/-- Eliminate the advice from the recognizer for one probe fiber. -/
def fiberCa (probe : adv.RtProbe Δ) (hclosed : adv.weak_rt_closed)
    (d : Δ) : CA_rt α :=
  hclosed.map (probe.recognizer d)

omit [Alphabet Δ] in
@[simp]
lemma fiberCa_spec (probe : adv.RtProbe Δ) (hclosed : adv.weak_rt_closed)
    (d : Δ) :
    (probe.fiberCa hclosed d).L = {w | probe.value w = d} := by
  show (hclosed.map (probe.recognizer d)).L = {w | probe.value w = d}
  rw [hclosed.spec]
  ext w
  exact probe.spec d w

omit [Alphabet Δ] in
@[simp]
lemma mem_fiberCa_iff (probe : adv.RtProbe Δ)
    (hclosed : adv.weak_rt_closed) (d : Δ) (w : Word α) :
    w ∈ (probe.fiberCa hclosed d).L ↔ probe.value w = d := by
  have h_language := probe.fiberCa_spec hclosed d
  have h_membership :
      (w ∈ (probe.fiberCa hclosed d).L) = (probe.value w = d) := by
    change (w ∈ (probe.fiberCa hclosed d).L) =
      (w ∈ ({w | probe.value w = d} : Language α))
    exact congrArg (fun language : Language α => w ∈ language) h_language
  constructor
  · show w ∈ (probe.fiberCa hclosed d).L → probe.value w = d
    exact Eq.mp h_membership
  · show probe.value w = d → w ∈ (probe.fiberCa hclosed d).L
    exact Eq.mpr h_membership

/-- Run all de-advised fiber recognizers in parallel and decode their unique
true output as the probe value. -/
def cart (probe : adv.RtProbe Δ) (hclosed : adv.weak_rt_closed) :
    CArtTransducer α Δ :=
  (ProdCA fun d => (probe.fiberCa hclosed d).toCellAutomaton).map_project
    PrefixStableProof.first_true_or_default

/-- Weak RT closure leaks one probe value at every prefix time, so the probe
disclosure is an ordinary CART trace. -/
lemma cart_trace_spec (probe : adv.RtProbe Δ)
    (hclosed : adv.weak_rt_closed) (w : Word α) :
    (probe.cart hclosed).trace_rt w = probe.disclosure w := by
  apply List.ext_getElem
  · simp [Advice.RtProbe.disclosure, Advice.FreeProbe.disclosure]
  · intro i h_cart h_disclosure
    have h_i : i < w.length := by
      simpa [CellAutomaton.trace_rt] using h_cart

    calc
      ((probe.cart hclosed).trace_rt w)[i]
          = PrefixStableProof.first_true_or_default
              (fun d => decide (w.take (i + 1) ∈ (probe.fiberCa hclosed d).L)) := by
              simp [cart, h_i, trace_rt_getElem_i_iff2]
      _ = PrefixStableProof.first_true_or_default
              (fun d => decide (probe.value (w.take (i + 1)) = d)) := by
              simp only [mem_fiberCa_iff]
      _ = probe.value (w.take (i + 1)) := by
              rw [PrefixStableProof.first_true_or_default_spec]
      _ = (probe.disclosure w)[i] := by
              simp [Advice.RtProbe.disclosure, Advice.FreeProbe.disclosure]

def disclosure_is_cart_advice (probe : adv.RtProbe Δ)
    (hclosed : adv.weak_rt_closed) :
    probe.disclosure.is_cart_advice := by
  refine ⟨probe.cart hclosed, ?_⟩
  apply advice_eq_iff
  funext w
  exact probe.cart_trace_spec hclosed w

end Advice.RtProbe

/-- Weak RT closure turns a finite advised disclosure into an unadvised CART
trace; its reconstruction transducer is therefore a two-stage presentation. -/
def is_two_stage_of_weak_rt_closed_and_finite_rt_disclosure
    (adv : Advice α Γ)
    (hclosed : adv.weak_rt_closed)
    (hdisclosure : adv.finite_rt_disclosure) :
    adv.is_two_stage_advice := by
  refine ⟨{
    β := hdisclosure.Δ
    C := hdisclosure.probe.cart hclosed
    M := hdisclosure.M
  }, ?_⟩
  apply advice_eq_iff
  funext w
  change hdisclosure.M.scanr (hdisclosure.probe.cart hclosed |>.trace_rt w) = adv w
  calc
    hdisclosure.M.scanr (hdisclosure.probe.cart hclosed |>.trace_rt w)
        = hdisclosure.M.scanr (hdisclosure.probe.disclosure w) := by
            rw [hdisclosure.probe.cart_trace_spec hclosed]
    _ = adv w := hdisclosure.spec w

/-- Uniform RT closure implies the weak closure needed by finite RT
disclosure, by specializing the refinement map to the identity. -/
def is_two_stage_of_rt_closed_and_finite_rt_disclosure
    (adv : Advice α Γ)
    (hclosed : adv.rt_closed)
    (hdisclosure : adv.finite_rt_disclosure) :
    adv.is_two_stage_advice :=
  is_two_stage_of_weak_rt_closed_and_finite_rt_disclosure adv
    (Advice.rt_closed_implies_weak_rt_closed hclosed) hdisclosure

/-- Among weakly RT-closed advice, finite RT disclosure is equivalent to a
two-stage presentation. -/
theorem weak_rt_closed_and_finite_rt_disclosure_iff_two_stage
    (adv : Advice α Γ) :
    Nonempty adv.weak_rt_closed ∧ Nonempty adv.finite_rt_disclosure ↔
      Nonempty adv.is_two_stage_advice := by
  constructor
  · rintro ⟨⟨hclosed⟩, ⟨hdisclosure⟩⟩
    exact ⟨is_two_stage_of_weak_rt_closed_and_finite_rt_disclosure
      adv hclosed hdisclosure⟩
  · rintro ⟨htwoStage⟩
    exact ⟨⟨htwoStage.weak_rt_closed⟩,
      ⟨htwoStage.finite_rt_disclosure⟩⟩

/-- Uniform RT closure together with finite RT disclosure is equivalent to a
two-stage presentation. -/
theorem rt_closed_and_finite_rt_disclosure_iff_two_stage
    (adv : Advice α Γ) :
    Nonempty adv.rt_closed ∧ Nonempty adv.finite_rt_disclosure ↔
      Nonempty adv.is_two_stage_advice := by
  constructor
  · rintro ⟨⟨hclosed⟩, ⟨hdisclosure⟩⟩
    exact ⟨is_two_stage_of_rt_closed_and_finite_rt_disclosure
      adv hclosed hdisclosure⟩
  · rintro ⟨htwoStage⟩
    exact ⟨⟨htwoStage.rt_closed⟩,
      ⟨htwoStage.finite_rt_disclosure⟩⟩

end CellularAutomatas
