/-
  # Separation: ℒ(OCA_rt α) ⊊ ℒ(CA_rt α)

  Main results:
  - `oca_rt_proper_subset_ca_rt_unit`:  ℒ(OCA_rt Unit) ⊊ ℒ(CA_rt Unit)
  - `oca_rt_proper_subset_ca_rt`:       ℒ(OCA_rt α)    ⊊ ℒ(CA_rt α) for any alphabet `α`

  ## Strategy

  Witness: the powers-of-2-length language `L_α := { w | ∃ k, |w| = 2^k }`.

  - **`L_α ∈ ℒ(CA_rt α)`** — lift the `Unit` automaton `exp_word_ca` along the
    constant map `α → Unit` using `tCellAutomaton.map_embed`. The pre-image is
    exactly `L_α` because `(replicate n ()) ∈ exp_word_ca.L  ↔  ∃ k, n = 2^k`.

  - **`L_α ∉ ℒ(OCA_rt α)`** — any `OCA_rt α` language has a regular unary slice
    at any letter `a` (`oca_rt_unary_slice_regular`). The slice of `L_α` at the
    default letter is the powers-of-2 language, which is not regular
    (`exp_word_not_regular` machinery: `IsAPFree.powers_of_two`).

  Combining: `L_α ∈ ℒ(CA_rt α)` but `L_α ∉ ℒ(OCA_rt α)`, so the inclusion is
  strict.
-/

import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.basic_exp_word
import CellularAutomatas.proofs.language.oca_rt_unary_regular
import CellularAutomatas.proofs.language.exp_word_not_regular

namespace CellularAutomatas

/-! ## Powers-of-2-length language is not in ℒ(OCA_rt) over any alphabet -/

/-- Auxiliary: the unary slice of `{ w | ∃ k, w.length = 2^k }` at `a` has
    `lengthSet a` equal to `{2^k}`. -/
private lemma exp_α_slice_lengthSet {α : Type} (a : α) :
    Language.lengthSet a
        (Language.unarySlice a ({ w : Word α | ∃ k, w.length = 2 ^ k } : Language α)) =
      { n | ∃ k, n = 2 ^ k } := by
  ext n
  -- LHS unfolds to: replicate n a ∈ unarySlice a {w | ∃ k, |w| = 2^k}
  show List.replicate n a ∈
         Language.unarySlice a ({ w | ∃ k, w.length = 2 ^ k } : Language α) ↔
       ∃ k, n = 2 ^ k
  -- unarySlice membership: (∃ m, replicate n a = replicate m a) ∧ |replicate n a| = 2^k
  -- The first conjunct is trivially satisfied with m := n.
  show ((∃ m, List.replicate n a = List.replicate m a) ∧
        ∃ k, (List.replicate n a).length = 2 ^ k) ↔ ∃ k, n = 2 ^ k
  simp only [List.length_replicate]
  refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨n, rfl⟩, h⟩⟩

/-- The slice's length set is infinite (it equals `{2^k}` which is infinite). -/
private lemma exp_α_slice_lengthSet_infinite {α : Type} (a : α) :
    (Language.lengthSet a
        (Language.unarySlice a ({ w : Word α | ∃ k, w.length = 2 ^ k } : Language α))).Infinite := by
  rw [exp_α_slice_lengthSet]
  exact powers_of_two_infinite

/-- **Layer 3.b transferred to `α`.** The powers-of-2-length language over any
    alphabet `α` is not in `ℒ(OCA_rt α)`. -/
theorem exp_α_not_in_oca_rt {α : Type} [Alphabet α] :
    { w : Word α | ∃ k, w.length = 2 ^ k } ∉ ℒ (OCA_rt α) := by
  intro h_oca
  -- Pick the default letter
  let a : α := default
  set L_α : Language α := { w | ∃ k, w.length = 2 ^ k }
  -- The slice of L_α at `a` is regular (since L_α ∈ ℒ(OCA_rt α))
  have h_slice_reg : (Language.unarySlice a L_α).IsRegular :=
    oca_rt_unary_slice_regular a L_α h_oca
  -- The slice's length set is infinite, hence contains an infinite AP
  have h_inf := exp_α_slice_lengthSet_infinite a
  have h_AP : Set.ContainsInfiniteAP (Language.lengthSet a (Language.unarySlice a L_α)) :=
    regular_infinite_lengthSet_contains_infinite_AP a (Language.unarySlice a L_α)
      h_slice_reg h_inf
  -- But the length set is `{2^k}`, which is AP-free
  have h_free : Set.IsAPFree (Language.lengthSet a (Language.unarySlice a L_α)) := by
    rw [exp_α_slice_lengthSet]
    exact Set.IsAPFree.powers_of_two
  -- AP-rich and AP-free is a contradiction
  exact Set.not_containsInfiniteAP_of_isAPFree h_AP h_free

/-! ## Powers-of-2-length language is in ℒ(CA_rt) over any alphabet -/

/-- For any `α`, `w.map (fun _ => ()) = List.replicate w.length ()`. -/
private lemma word_map_const_unit {α : Type} (w : Word α) :
    w.map (fun _ => ()) = List.replicate w.length () := by
  induction w with
  | nil => rfl
  | cons _ w' ih => simp [List.replicate_succ, ih]

/-- **Lifting.** The powers-of-2-length language over any alphabet `α` is in
    `ℒ(CA_rt α)`, obtained by composing `exp_word_ca` with the constant
    `α → Unit` map. -/
theorem exp_α_in_ca_rt {α : Type} [Alphabet α] :
    { w : Word α | ∃ k, w.length = 2 ^ k } ∈ ℒ (CA_rt α) := by
  -- Pull back exp_word_ca : CA_rt Unit along (fun _ : α => ())
  refine ⟨exp_word_ca.map_embed (fun _ : α => ()), ?_⟩
  -- Show that membership in the lifted CA's language equals length being 2^k
  ext w
  -- The goal has shape `w ∈ {... 2^k} ↔ w ∈ DefinesLanguage.L (...)`.
  -- DefinesLanguage.L on tCellAutomaton unfolds to .L.
  symm
  show w ∈ (exp_word_ca.map_embed (fun _ : α => ())).L ↔ ∃ k, w.length = 2 ^ k
  rw [map_embed_L]
  -- Now: w ∈ (...).L ↔ w.map (fun _ => ()) ∈ exp_word_ca.L
  -- which equals: replicate w.length () ∈ exp_word_ca.L ↔ ∃ k, w.length = 2^k
  show w.map (fun _ : α => ()) ∈ exp_word_ca.L ↔ ∃ k, w.length = 2 ^ k
  rw [word_map_const_unit]
  -- exp_word_ca.L = { w | ∃ n, w.length = 2^n }
  show List.replicate w.length () ∈ exp_word_ca.L ↔ ∃ k, w.length = 2 ^ k
  -- Use exp_word_ca_correct: replicate n () ∈ exp_word_ca.L ↔ ∃ k, n = 2^k
  -- via the .L = .accepts equivalence built into tCellAutomaton.L
  show exp_word_ca.accepts (List.replicate w.length ()) ↔ ∃ k, w.length = 2 ^ k
  rw [show (exp_word_ca.accepts (List.replicate w.length ()) = true) =
        exp_word_ca.accepts (List.replicate w.length ()) from rfl]
  rw [exp_word_ca_correct]
  -- ∃ k, |replicate w.length ()| = 2^k ↔ ∃ k, w.length = 2^k
  simp only [List.length_replicate]

/-! ## Main separations -/

/-- **General separation.** For any alphabet `α`, the languages recognized by
    one-way real-time CAs are a *strict* subset of those recognized by general
    real-time CAs.

    Proof: the powers-of-2-length language is in `ℒ(CA_rt α)` (by lifting from
    `Unit`) but not in `ℒ(OCA_rt α)` (because its unary slice at the default
    letter would have to be regular, yet the powers of 2 are not regular). -/
theorem oca_rt_proper_subset_ca_rt {α : Type} [Alphabet α] :
    ℒ (OCA_rt α) ⊂ ℒ (CA_rt α) := by
  refine ⟨ℒ_OCA_rt_sub_CA_rt, fun hsub => ?_⟩
  -- The witness: the powers-of-2-length language
  exact exp_α_not_in_oca_rt (hsub exp_α_in_ca_rt)
where
  ℒ_OCA_rt_sub_CA_rt : ℒ (OCA_rt α) ⊆ ℒ (CA_rt α) :=
    fun _ ⟨C, hL⟩ => ⟨C.1, hL⟩

/-- **Unit separation** as a special case. -/
theorem oca_rt_proper_subset_ca_rt_unit : ℒ (OCA_rt Unit) ⊂ ℒ (CA_rt Unit) :=
  oca_rt_proper_subset_ca_rt

end CellularAutomatas
