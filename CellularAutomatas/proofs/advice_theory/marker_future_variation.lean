import CellularAutomatas.proofs.advice_theory.finite_future_variation_iff_free_disclosure

/-!
# Marker advice: when does delayed revelation destroy two-stage-ness?

A *marker advice* `Advice.from_len_marker f` marks the single position `f n - 1` of a word
of length `n`. This is the canonical shape of an advice that "reveals something about early
positions only once enough later characters are present": the marker is the boundary of the
revealed region, and the boundary moves as padding is added.

The general criterion below says such an advice fails `finite_future_variation` — and hence,
by `finite_future_variation_iff_nonempty_finite_free_disclosure`, is not two-stage — exactly
when arbitrarily many marker positions remain reachable from arbitrarily long prefixes.

This separates the two regimes cleanly:

* **sparse boundaries stay two-stage.** For `middle_exp` the marker sits at a power of two
  with `2p ≤ n`, so `2p ≤ n < 4p` pins `p` to within a factor of four of the prefix length:
  only boundedly many markers are reachable, and indeed `middle_exp` *is* two-stage.
* **dense boundaries do not.** `middle` (`p = n / 2`) and the logarithmic boundary
  `p = ⌊log₂ n⌋` both leave unboundedly many reachable markers below a fixed prefix.

The logarithmic marker is the interesting new case: it is the boundary of "reveal position
`i` once the word has length at least `2^i`". It is not two-stage, and unlike `middle` its
weak RT closure is *not* known to be equivalent to `CA_rt = CA_lt` — it hands a real-time CA
only `⌊log₂ n⌋`, i.e. `log log n` bits, and hands them at time `⌊log₂ n⌋`.
-/

namespace CellularAutomatas

open Classical

variable {α : Type} [Alphabet α]

/-! ## The general criterion -/

/-- A length-marker advice has unbounded future variation as soon as arbitrarily many
marker positions stay reachable from arbitrarily long prefixes.

The prefix `p` of length `k` sees one advice word per reachable marker below `k`, and these
words are pairwise distinct, so no uniform bound on the number of reachable values exists. -/
theorem from_len_marker_not_finite_future_variation (f : ℕ → Option ℕ)
    (hunbounded : ∀ N : ℕ, ∃ k, N ≤ (reachable_markers f k).card) :
    ¬ (Advice.from_len_marker (α := α) f).finite_future_variation := by
  rintro ⟨N, hN⟩
  obtain ⟨k, hk⟩ := hunbounded (N + 1)
  let p : Word α := List.replicate k (default : α)
  have hplen : p.length = k := by simp [p]
  obtain ⟨S, hSsub, hScard⟩ := distinct_prefixes_from_markers (α := α) f p
  -- Lower bound: one distinct advice prefix per reachable marker.
  have hcard : N + 1 ≤ S.card := by
    show N + 1 ≤ S.card
    rw [hScard, hplen]
    exact hk
  have hsubset : (S : Set (List Bool)) ⊆
      Set.univ.image (fun s : Word α => rel_repr (Advice.from_len_marker f) p s) := by
    intro v hv
    obtain ⟨s, rfl⟩ := hSsub hv
    exact ⟨s, Set.mem_univ _, rfl⟩
  -- Comparing with the assumed uniform bound gives `N + 1 ≤ N`.
  have hlower : ((N + 1 : ℕ) : ℕ∞) ≤
      (Set.univ.image (fun s : Word α => rel_repr (Advice.from_len_marker f) p s)).encard :=
    calc ((N + 1 : ℕ) : ℕ∞)
        ≤ (S.card : ℕ∞) := by exact_mod_cast hcard
      _ = (S : Set (List Bool)).encard := (Set.encard_coe_eq_coe_finsetCard S).symm
      _ ≤ _ := Set.encard_mono hsubset
  have : N + 1 ≤ N := ENat.coe_le_coe.mp (le_trans hlower (hN p))
  omega

/-! ## The middle marker, via the criterion -/

/-- Above a prefix of length `2 * k` the middle marker reaches at least `k` positions. -/
theorem Advice.middle_not_finite_future_variation :
    ¬ (Advice.middle α).finite_future_variation :=
  from_len_marker_not_finite_future_variation _
    (fun N => ⟨2 * N, middle_reachable_card N⟩)

/-! ## The logarithmic revelation boundary -/

/-- The boundary of "position `i` is revealed once the word has length at least `2 ^ i`". -/
def log_idx (n : ℕ) : Option ℕ := some (Nat.log 2 n)

/-- Marks the position `⌊log₂ n⌋`, the boundary of the revealed region. -/
def Advice.log_marker (α) : Advice α Bool := Advice.from_len_marker log_idx

/-- Every position strictly above `log₂ k` is a reachable marker from prefix length `k`:
the witness is the word of length `2 ^ pos`, which is at least `k` precisely because `pos`
exceeds `log₂ k`. -/
lemma log_reachable_subset (k : ℕ) :
    Finset.Icc (Nat.log 2 k + 1) k ⊆ reachable_markers log_idx k := by
  intro pos hpos
  rw [Finset.mem_Icc] at hpos
  obtain ⟨hlo, hhi⟩ := hpos
  have hk : k < 2 ^ pos :=
    calc k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
      _ ≤ 2 ^ pos := Nat.pow_le_pow_right (by norm_num) hlo
  rw [reachable_markers, Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, by omega, 2 ^ pos, by omega, ?_⟩
  show log_idx (2 ^ pos) = some pos
  simp [log_idx, Nat.log_pow]

/-- At prefix length `2 ^ (N + 1)` at least `N` marker positions are reachable. -/
lemma log_reachable_card (N : ℕ) :
    N ≤ (reachable_markers log_idx (2 ^ (N + 1))).card := by
  have hlog : Nat.log 2 (2 ^ (N + 1)) = N + 1 := Nat.log_pow (by norm_num) _
  have hsub := log_reachable_subset (2 ^ (N + 1))
  rw [hlog] at hsub
  have hcard : (Finset.Icc (N + 1 + 1) (2 ^ (N + 1))).card = 2 ^ (N + 1) - (N + 1) := by
    rw [Nat.card_Icc]; omega
  -- `N + 1 ≤ 2 ^ N` makes the interval long enough.
  have hgrow : N < 2 ^ N := Nat.lt_two_pow_self
  have hsucc : 2 ^ (N + 1) = 2 ^ N * 2 := pow_succ 2 N
  calc N ≤ (Finset.Icc (N + 1 + 1) (2 ^ (N + 1))).card := by rw [hcard]; omega
    _ ≤ _ := Finset.card_le_card hsub

/-- The logarithmic revelation boundary has unbounded future variation. -/
theorem Advice.log_marker_not_finite_future_variation :
    ¬ (Advice.log_marker α).finite_future_variation :=
  from_len_marker_not_finite_future_variation _
    (fun N => ⟨2 ^ (N + 1), log_reachable_card N⟩)

/-- Consequently the logarithmic revelation boundary is not two-stage. Whether it is
weakly RT-closed is open — and unlike `middle`, it is not known to be tied to
`ℒ(CA_rt) = ℒ(CA_lt)`. -/
theorem Advice.log_marker_not_two_stage :
    IsEmpty (Advice.log_marker α).is_two_stage_advice := by
  constructor
  intro h
  exact Advice.log_marker_not_finite_future_variation
    (Advice.finite_future_variation_of_finite_free_disclosure
      h.finite_rt_disclosure.finite_free_disclosure)

/-! ## The converse: sparse boundaries keep finite future variation -/

omit [Alphabet α] in
/-- The observable advice prefix above `p` is just the marker word for the boundary that the
total length induces. A boundary of `none`, of `0`, or one lying beyond `p` all collapse to
the same blank word. -/
lemma rel_repr_from_len_marker (f : ℕ → Option ℕ) (p s : Word α) :
    rel_repr (Advice.from_len_marker f) p s
      = marker_list p.length ((f (p ++ s).length).getD 0) := by
  apply List.ext_getElem
  · simp [rel_repr, Advice.from_len_marker, Advice.from_marker, marker_list]
  · intro i h1 h2
    simp only [rel_repr, Advice.from_len_marker, Advice.from_marker, marker_list,
      List.getElem_take, List.getElem_map, List.getElem_range, List.length_append]
    cases hf : f (p.length + s.length) with
    | none => simp [hf]
    | some pos => simp [hf]

/-- A boundary outside `[1, n]` marks nothing, so it is indistinguishable from no boundary. -/
lemma marker_list_of_out_of_range (n pos : ℕ) (h : pos = 0 ∨ n < pos) :
    marker_list n pos = marker_list n 0 := by
  apply List.ext_getElem
  · simp [marker_list]
  · intro i h1 h2
    simp only [marker_list, List.getElem_map, List.getElem_range]
    have hi : i < n := by simpa [marker_list] using h1
    have : ¬ (i + 1 = pos) := by omega
    simp [this]

omit [Alphabet α] in
/-- **Converse of the criterion.** If only boundedly many boundary positions are ever
reachable, the marker advice has finite future variation: every observable prefix is the
marker word of a reachable boundary, or the blank word. -/
theorem from_len_marker_finite_future_variation (f : ℕ → Option ℕ) (c : ℕ)
    (hbound : ∀ k, (reachable_markers f k).card ≤ c) :
    (Advice.from_len_marker (α := α) f).finite_future_variation := by
  refine ⟨c + 1, fun p => ?_⟩
  let candidates : Finset (List Bool) :=
    insert (marker_list p.length 0)
      ((reachable_markers f p.length).image (marker_list p.length))
  have hsubset : Set.univ.image (fun s : Word α => rel_repr (Advice.from_len_marker f) p s)
      ⊆ ↑candidates := by
    rintro l ⟨s, -, rfl⟩
    simp only [rel_repr_from_len_marker]
    set pos := (f (p ++ s).length).getD 0 with hpos
    by_cases hrange : 1 ≤ pos ∧ pos ≤ p.length
    · -- The boundary lies inside `p`, so it is a reachable marker.
      have hreach : pos ∈ reachable_markers f p.length := by
        rw [reachable_markers, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, by omega, (p ++ s).length, by simp, ?_⟩
        -- `getD 0 = pos` with `pos ≠ 0` forces the option to be `some pos`.
        cases hf : f (p ++ s).length with
        | none => rw [hf] at hpos; simp at hpos; omega
        | some q => rw [hf] at hpos; simpa using hpos.symm
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hreach))
    · -- Otherwise the boundary marks nothing inside `p`.
      rw [marker_list_of_out_of_range _ _ (by omega)]
      exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
  refine le_trans (Set.encard_mono hsubset) ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  have hcard : candidates.card ≤ c + 1 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have himg : ((reachable_markers f p.length).image (marker_list p.length)).card ≤ c :=
      le_trans Finset.card_image_le (hbound p.length)
    omega
  exact_mod_cast hcard

/-! ## Same information, opposite classification

`Advice.log_marker` marks position `⌊log₂ n⌋`; `Advice.pow2_marker` marks position
`2 ^ ⌊log₂ n⌋`. Each of the two determines the other's content — both are exactly the
statement "`n` lies in `[2^k, 2^(k+1))`" — yet they land on opposite sides of the two-stage
boundary. The only difference is *where the mark sits*: at a position proportional to `n`,
or at a position logarithmic in `n`. -/

/-- The largest power of two not exceeding `n`. -/
def pow2_idx (n : ℕ) : Option ℕ := some (2 ^ Nat.log 2 n)

/-- Marks the position `2 ^ ⌊log₂ n⌋`. -/
def Advice.pow2_marker (α) : Advice α Bool := Advice.from_len_marker pow2_idx

/-- From a prefix of length `k`, the *only* reachable boundary is `2 ^ ⌊log₂ k⌋`: a witness
`n ≥ k` with boundary `2 ^ j ≤ k` forces `2 ^ j ≤ k ≤ n < 2 ^ (j + 1)`. -/
lemma pow2_reachable_subset (k : ℕ) :
    reachable_markers pow2_idx k ⊆ {2 ^ Nat.log 2 k} := by
  intro pos hpos
  rw [reachable_markers, Finset.mem_filter, Finset.mem_range] at hpos
  obtain ⟨hle, hgt, n, hn, hfn⟩ := hpos
  have hpos_eq : pos = 2 ^ Nat.log 2 n := by simpa [pow2_idx] using hfn.symm
  have hn0 : n ≠ 0 := by omega
  have hlow : 2 ^ Nat.log 2 n ≤ k := by omega
  have hhigh : k < 2 ^ (Nat.log 2 n + 1) :=
    lt_of_le_of_lt hn (Nat.lt_pow_succ_log_self (by norm_num) n)
  have : Nat.log 2 k = Nat.log 2 n := Nat.log_eq_of_pow_le_of_lt_pow hlow hhigh
  simp [hpos_eq, this]

omit [Alphabet α] in
/-- The power-of-two boundary keeps finite future variation, in sharp contrast to the
logarithmic boundary that carries the same information. -/
theorem Advice.pow2_marker_finite_future_variation :
    (Advice.pow2_marker α).finite_future_variation :=
  from_len_marker_finite_future_variation _ 1
    (fun k => le_trans (Finset.card_le_card (pow2_reachable_subset k))
      (le_of_eq (Finset.card_singleton _)))

/-- Consequently the power-of-two boundary has finite free disclosure. -/
theorem Advice.pow2_marker_finite_free_disclosure :
    Nonempty (Advice.pow2_marker α).finite_free_disclosure :=
  (Advice.finite_future_variation_iff_nonempty_finite_free_disclosure _).1
    Advice.pow2_marker_finite_future_variation

end CellularAutomatas
