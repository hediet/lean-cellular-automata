import CellularAutomatas.proofs.advice_theory.middle_not_two_stage
import CellularAutomatas.proofs.advice_theory.finite_rt_disclosure

/-!
# Finite future variation is exactly finite free disclosure

`Advice.finite_future_variation` (from `middle_not_two_stage`) is the purely combinatorial
statement that, uniformly in the prefix `p`, only boundedly many advice words can appear
on `p` when `p` is extended by an arbitrary suffix.

`Advice.finite_free_disclosure` (from `finite_rt_disclosure`) is the structural statement
that the advice is reconstructible by a right-to-left finite-state scan of a finite
observation taken at every prefix.

This file proves the two notions are **equivalent**:

* `Advice.finite_future_variation_of_finite_free_disclosure` — the transducer state is the
  only channel through which the suffix can influence the advice on `p`, so at most
  `|Q|` advice prefixes are reachable (the bottleneck argument).
* `Advice.finite_free_disclosure_of_finite_future_variation` — conversely, enumerate the
  (boundedly many) reachable advice prefixes of each prefix `p`; the *index* into that
  enumeration is a finite state, and the disclosure at `p` is the table that says, for
  each index, which advice symbol it selects and how the index is inherited by `p`'s
  own prefix.

Consequences:

* The gap between `finite_free_disclosure` and `finite_rt_disclosure` — i.e. between the
  open question `weak_rt_closed → two_stage` and the theorem
  `weak_rt_closed + finite_rt_disclosure → two_stage` — is *exactly* the requirement that
  the disclosed table be observable in real time. The table built below records
  counterfactual data (which advice symbol the prefix would carry under other
  continuations), which an advised real-time recognizer has no access to.
* `finite_future_variation` is *strictly* weaker than `finite_future_index` (see
  `finite_future_variation_not_future_index`), so `Advice.IsFiniteFutureIndex.finite_free_disclosure`
  is now a corollary rather than a separate construction.
-/

namespace CellularAutomatas

open Classical

variable {α Γ Δ : Type} [Alphabet α] [Alphabet Γ] [Alphabet Δ]


section DisclosureBasics

variable {adv : Advice α Γ}

@[simp]
lemma Advice.FreeProbe.disclosure_length (probe : adv.FreeProbe Δ) (w : Word α) :
    (probe.disclosure w).length = w.length := by
  simp [Advice.FreeProbe.disclosure]

lemma Advice.FreeProbe.disclosure_getElem (probe : adv.FreeProbe Δ) (w : Word α)
    (i : ℕ) (h : i < (probe.disclosure w).length) :
    (probe.disclosure w)[i] = probe.value (w.take (i + 1)) := by
  simp [Advice.FreeProbe.disclosure]

/-- The diary of a prefix is exactly the corresponding prefix of the diary of any
extension: the probe only ever looks at prefixes. -/
lemma Advice.FreeProbe.disclosure_take (probe : adv.FreeProbe Δ) (p s : Word α) :
    (probe.disclosure (p ++ s)).take p.length = probe.disclosure p := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < p.length := by simpa using h2
    rw [List.getElem_take]
    rw [Advice.FreeProbe.disclosure_getElem, Advice.FreeProbe.disclosure_getElem]
    congr 1
    exact List.take_append_of_le_length (by omega)

end DisclosureBasics


section RelReprBasics

variable {adv : Advice α Γ}

/-- With the empty extension the reachable advice prefix is the advice itself. -/
lemma rel_repr_nil (p : Word α) : rel_repr adv p [] = adv p := by
  have hlen : (adv p).length = p.length := by simp
  simp only [rel_repr, List.append_nil, ← hlen, List.take_length]

end RelReprBasics


/-! ## Free disclosure implies finite future variation -/

section FreeDisclosureToVariation

variable {adv : Advice α Γ}

/-- The suffix influences the advice on `p` only through the transducer state that the
backward scan has reached at the boundary. -/
lemma free_disclosure_rel_repr_eq (h : adv.finite_free_disclosure) (p s : Word α) :
    rel_repr adv p s =
      h.M.scanr_q
        (h.M.scanr_reduce ((h.probe.disclosure (p ++ s)).drop p.length))
        (h.probe.disclosure p) := by
  dsimp [rel_repr]
  rw [← h.spec (p ++ s)]
  set W := h.probe.disclosure (p ++ s) with hW
  have h_split : W = W.take p.length ++ W.drop p.length :=
    (List.take_append_drop p.length W).symm
  conv in (h.M.scanr W) => rw [h_split]
  have h_indep : W.take p.length = h.probe.disclosure p := by
    rw [hW]; exact Advice.FreeProbe.disclosure_take h.probe p s
  rw [h_indep]
  have h_len_p : (h.probe.disclosure p).length = p.length := by simp
  conv => lhs; arg 1; rw [← h_len_p]
  exact FiniteStateTransducer.scanr_append_take _ _

/-- **Bottleneck direction.** A finite free disclosure bounds, uniformly in the prefix,
the number of advice prefixes reachable by varying the suffix. -/
theorem Advice.finite_future_variation_of_finite_free_disclosure
    (h : adv.finite_free_disclosure) : adv.finite_future_variation := by
  refine ⟨Fintype.card h.M.Q, fun p => ?_⟩
  have hsub : (Set.univ.image (fun s : Word α => rel_repr adv p s))
      ⊆ ↑((Finset.univ : Finset h.M.Q).image
            (fun q => h.M.scanr_q q (h.probe.disclosure p))) := by
    rintro l ⟨s, -, rfl⟩
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨_, (free_disclosure_rel_repr_eq h p s).symm⟩
  refine le_trans (Set.encard_mono hsub) ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast (Finset.card_image_le).trans (le_of_eq Finset.card_univ)

end FreeDisclosureToVariation


/-! ## Finite future variation implies free disclosure -/

namespace FiniteFutureVariation

variable (adv : Advice α Γ) (N : ℕ)

/-- The advice prefixes of `p` realizable by some extension of `p`. -/
def possib (p : Word α) : Set (Word Γ) :=
  Set.univ.image (fun s : Word α => rel_repr adv p s)

variable {adv}

lemma mem_possib (p s : Word α) : rel_repr adv p s ∈ possib adv p :=
  ⟨s, Set.mem_univ _, rfl⟩

lemma adv_mem_possib (p : Word α) : adv p ∈ possib adv p := by
  have := mem_possib (adv := adv) p []
  rwa [rel_repr_nil] at this

variable (adv)

variable (hN : ∀ p : Word α, (Set.univ.image (fun s : Word α => rel_repr adv p s)).encard ≤ N)

include hN

lemma possib_finite (p : Word α) : (possib adv p).Finite :=
  Set.finite_of_encard_le_coe (hN p)

/-- The reachable advice prefixes of `p`, as a finite set. -/
noncomputable def possibFinset (p : Word α) : Finset (Word Γ) :=
  (possib_finite adv N hN p).toFinset

lemma mem_possibFinset_iff (p : Word α) (v : Word Γ) :
    v ∈ possibFinset adv N hN p ↔ v ∈ possib adv p := by
  simp [possibFinset]

lemma possibFinset_card_le (p : Word α) : (possibFinset adv N hN p).card ≤ N := by
  have hcoe : ((possibFinset adv N hN p : Finset (Word Γ)) : Set (Word Γ)) = possib adv p := by
    simp [possibFinset]
  have := hN p
  rw [show (Set.univ.image (fun s : Word α => rel_repr adv p s)) = possib adv p from rfl,
    ← hcoe, Set.encard_coe_eq_coe_finsetCard] at this
  exact_mod_cast this

/-- A canonical enumeration of the reachable advice prefixes of `p`, arranged so that the
"no further input" value `adv p` sits at index `0`. -/
noncomputable def enum (p : Word α) : List (Word Γ) :=
  adv p :: ((possibFinset adv N hN p).erase (adv p)).toList

lemma enum_length_le (p : Word α) : (enum adv N hN p).length ≤ N := by
  have hmem : adv p ∈ possibFinset adv N hN p :=
    (mem_possibFinset_iff adv N hN p _).2 (adv_mem_possib p)
  have hcard := possibFinset_card_le adv N hN p
  have hpos : 1 ≤ (possibFinset adv N hN p).card := Finset.card_pos.2 ⟨_, hmem⟩
  have herase := Finset.card_erase_of_mem hmem
  simp only [enum, List.length_cons, Finset.length_toList, herase]
  omega

lemma mem_enum {p : Word α} {v : Word Γ} (hv : v ∈ possib adv p) :
    v ∈ enum adv N hN p := by
  by_cases h : v = adv p
  · simp [enum, h]
  · have : v ∈ possibFinset adv N hN p := (mem_possibFinset_iff adv N hN p _).2 hv
    simp [enum, Finset.mem_toList, Finset.mem_erase, h, this]

/-- The finite state: the position of an advice prefix inside the canonical enumeration. -/
noncomputable def idx (p : Word α) (v : Word Γ) : Fin (N + 1) :=
  ⟨min ((enum adv N hN p).idxOf v) N, by omega⟩

/-- Decoding a finite state back into an advice prefix. -/
noncomputable def valAt (p : Word α) (k : Fin (N + 1)) : Word Γ :=
  (enum adv N hN p).getD k.val (adv p)

lemma idx_adv (p : Word α) : idx adv N hN p (adv p) = 0 := by
  apply Fin.ext
  simp [idx, enum]

lemma valAt_idx {p : Word α} {v : Word Γ} (hv : v ∈ possib adv p) :
    valAt adv N hN p (idx adv N hN p v) = v := by
  have hmem := mem_enum adv N hN hv
  have hlt : (enum adv N hN p).idxOf v < (enum adv N hN p).length :=
    List.idxOf_lt_length_of_mem hmem
  have hle : (enum adv N hN p).idxOf v ≤ N :=
    le_trans (le_of_lt hlt) (enum_length_le adv N hN p)
  have hmin : min ((enum adv N hN p).idxOf v) N = (enum adv N hN p).idxOf v :=
    min_eq_left hle
  simp only [valAt, idx, hmin]
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_idxOf hlt

/-- Type of disclosed tables: how the index is inherited by the shorter prefix, and which
advice symbol each index selects. -/
abbrev Tbl (Γ : Type) (N : ℕ) := (Fin (N + 1) → Fin (N + 1)) × (Fin (N + 1) → Γ)

/-- The disclosure taken at a prefix `u`: for every possible index, the advice symbol it
puts at the last position of `u`, together with the index it induces on `u.dropLast`. -/
noncomputable def freeProbe : adv.FreeProbe (Tbl Γ N) where
  value := fun u =>
    ( fun k => idx adv N hN u.dropLast (valAt adv N hN u k).dropLast
    , fun k => ((valAt adv N hN u k).getLast?).getD default )

/-- The backward scan: carry the index, emit the selected advice symbol. -/
noncomputable def recTransducer : FiniteStateTransducer (Tbl Γ N) Γ where
  Q := Fin (N + 1) × Γ
  δ := fun st d => (d.1 st.1, d.2 st.1)
  q0 := (0, default)
  f := Prod.snd

omit [Alphabet α] hN in
private lemma take_succ_dropLast (l : List Γ) (k : ℕ) (h : k < l.length) :
    (l.take (k + 1)).dropLast = l.take k := by
  rw [List.dropLast_eq_take]
  rw [List.length_take, Nat.min_eq_left (by omega : k + 1 ≤ l.length)]
  rw [List.take_take]
  simp

omit hN in
private lemma rel_repr_dropLast (p : Word α) (a : α) (t : Word α) :
    (rel_repr adv (p ++ [a]) t).dropLast = rel_repr adv p (a :: t) := by
  have hcat : (p ++ [a]) ++ t = p ++ a :: t := by simp
  have hlen : p.length < (adv (p ++ a :: t)).length := by simp
  simp only [rel_repr, hcat, List.length_append, List.length_cons, List.length_nil]
  show (List.take (p.length + 1) (adv (p ++ a :: t))).dropLast
      = List.take p.length (adv (p ++ a :: t))
  exact take_succ_dropLast _ _ hlen

/-- The backward scan reaches exactly the index of the advice prefix that the suffix
actually realizes. -/
lemma reduce_fst (s p : Word α) :
    ((recTransducer (Γ := Γ) N).scanr_reduce
        (((freeProbe adv N hN).disclosure (p ++ s)).drop p.length)).1
      = idx adv N hN p (rel_repr adv p s) := by
  induction s generalizing p with
  | nil =>
      have hnil : (((freeProbe adv N hN).disclosure (p ++ [])).drop p.length) = [] := by
        simp
      rw [hnil, FiniteStateTransducer.scanr_reduce_empty, rel_repr_nil, idx_adv]
      rfl
  | cons a t ih =>
      have hcat : p ++ a :: t = (p ++ [a]) ++ t := by simp
      rw [hcat]
      have hlt : p.length
          < ((freeProbe adv N hN).disclosure ((p ++ [a]) ++ t)).length := by simp
      rw [List.drop_eq_getElem_cons hlt, FiniteStateTransducer.scanr_reduce_cons]
      have hget : ((freeProbe adv N hN).disclosure ((p ++ [a]) ++ t))[p.length]
          = (freeProbe adv N hN).value (p ++ [a]) := by
        rw [Advice.FreeProbe.disclosure_getElem]
        congr 1
        exact List.take_left' (by simp)
      have hlen : p.length + 1 = (p ++ [a]).length := by simp
      rw [hget, hlen]
      -- The transducer step applies the freshly read table to the state that the scan
      -- of the strictly shorter suffix has reached.
      show ((freeProbe adv N hN).value (p ++ [a])).1
          ((recTransducer (Γ := Γ) N).scanr_reduce
            (((freeProbe adv N hN).disclosure ((p ++ [a]) ++ t)).drop (p ++ [a]).length)).1
          = idx adv N hN p (rel_repr adv p (a :: t))
      rw [ih (p ++ [a])]
      show idx adv N hN (p ++ [a]).dropLast
          ((valAt adv N hN (p ++ [a])
            (idx adv N hN (p ++ [a]) (rel_repr adv (p ++ [a]) t))).dropLast)
          = idx adv N hN p (rel_repr adv p (a :: t))
      rw [valAt_idx adv N hN (mem_possib (p ++ [a]) t), List.dropLast_concat,
        rel_repr_dropLast]

/-- The disclosed tables, scanned right to left, reconstruct the advice. -/
lemma recTransducer_scanr_disclosure (w : Word α) :
    (recTransducer (Γ := Γ) N).scanr ((freeProbe adv N hN).disclosure w) = adv w := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hw : i < w.length := by simpa using h2
    have hD : i < ((freeProbe adv N hN).disclosure w).length := by simpa using hw
    have hplen : (w.take (i + 1)).length = i + 1 := by
      simp [Nat.min_eq_left (by omega : i + 1 ≤ w.length)]
    -- The state the backward scan has reached at position `i` indexes the advice prefix
    -- that the *actual* continuation of `w.take (i+1)` realizes.
    have hreduce := reduce_fst adv N hN (w.drop (i + 1)) (w.take (i + 1))
    rw [List.take_append_drop, hplen] at hreduce
    have hEq : ((recTransducer (Γ := Γ) N).scanr
          ((freeProbe adv N hN).disclosure w))[i]'h1
        = (recTransducer (Γ := Γ) N).f ((recTransducer (Γ := Γ) N).δ
            ((recTransducer (Γ := Γ) N).scanr_reduce
              (((freeProbe adv N hN).disclosure w).drop (i + 1)))
            ((freeProbe adv N hN).disclosure w)[i]) :=
      FiniteStateTransducer.scanr_get'_eq1 _ ⟨i, hD⟩
    rw [hEq, Advice.FreeProbe.disclosure_getElem _ _ _ hD]
    show ((freeProbe adv N hN).value (w.take (i + 1))).2
        ((recTransducer (Γ := Γ) N).scanr_reduce
          (((freeProbe adv N hN).disclosure w).drop (i + 1))).1 = _
    rw [hreduce]
    show (((valAt adv N hN (w.take (i + 1))
        (idx adv N hN (w.take (i + 1))
          (rel_repr adv (w.take (i + 1)) (w.drop (i + 1))))).getLast?).getD default) = _
    rw [valAt_idx adv N hN (mem_possib (w.take (i + 1)) (w.drop (i + 1)))]
    have hval : rel_repr adv (w.take (i + 1)) (w.drop (i + 1)) = (adv w).take (i + 1) := by
      rw [rel_repr, List.take_append_drop, hplen]
    rw [hval, PrefixStableProof.getLastOfTake h2, List.getElem?_eq_getElem h2]
    rfl

end FiniteFutureVariation

/-- **Reconstruction direction.** A uniform bound on the reachable advice prefixes is
already enough to reconstruct the advice by a right-to-left finite-state scan of a finite
observation of every prefix. -/
noncomputable def Advice.finite_free_disclosure_of_finite_future_variation
    {adv : Advice α Γ} (h : adv.finite_future_variation) : adv.finite_free_disclosure where
  Δ := FiniteFutureVariation.Tbl Γ h.choose
  probe := FiniteFutureVariation.freeProbe adv h.choose h.choose_spec
  M := FiniteFutureVariation.recTransducer (Γ := Γ) h.choose
  spec := FiniteFutureVariation.recTransducer_scanr_disclosure adv h.choose h.choose_spec

/-- **Free disclosure is exactly finite future variation.** The structural notion (reconstruct the
advice by a right-to-left finite-state scan of a finite per-prefix observation) and the
purely combinatorial notion (boundedly many advice prefixes are reachable by varying the
suffix) coincide. -/
theorem Advice.finite_future_variation_iff_nonempty_finite_free_disclosure
    (adv : Advice α Γ) :
    adv.finite_future_variation ↔ Nonempty adv.finite_free_disclosure :=
  ⟨fun h => ⟨Advice.finite_free_disclosure_of_finite_future_variation h⟩,
   fun ⟨h⟩ => Advice.finite_future_variation_of_finite_free_disclosure h⟩


/-! ## Finite future index is a special case -/

namespace Advice.IsFiniteFutureIndex

variable {adv : Advice α Γ}

/-- Future-equivalent suffixes force the same advice prefix, so every reachable advice
prefix of `p` is already realized by one of the finitely many class representatives. -/
theorem finite_future_variation (h : adv.finite_future_index) : adv.finite_future_variation := by
  refine ⟨Fintype.card h.S, fun p => ?_⟩
  have hsub : (Set.univ.image (fun s : Word α => rel_repr adv p s))
      ⊆ ↑((Finset.univ : Finset h.S).image
            (fun c => rel_repr adv p (h.representative c))) := by
    rintro l ⟨s, -, rfl⟩
    -- `s` and the representative of its class agree on every left context, in particular `p`
    have hrep : adv.future_equivalent (h.representative (h.index s)) s :=
      (h.index_eq_iff _ _).1 (h.representative_index (h.index s))
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨h.index s, hrep p⟩
  refine le_trans (Set.encard_mono hsub) ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast (Finset.card_image_le).trans (le_of_eq Finset.card_univ)

/-- Finite future index implies finite free disclosure, now as a corollary of the
`finite_future_variation` characterization rather than a bespoke construction. -/
noncomputable def finite_free_disclosure (h : adv.finite_future_index) :
    adv.finite_free_disclosure :=
  Advice.finite_free_disclosure_of_finite_future_variation h.finite_future_variation

end Advice.IsFiniteFutureIndex

end CellularAutomatas
