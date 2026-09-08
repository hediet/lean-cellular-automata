import CellularAutomatas.proofs.advice_theory.finite_future_variation_iff_free_disclosure

/-!
# Finite future variation is *strictly* weaker than finite future index

`Advice.IsFiniteFutureIndex.finite_future_variation` shows that a finite Myhill–Nerode index on
suffixes bounds the future variation. This file shows the converse fails, so the equivalence
`finite_future_variation ↔ finite_free_disclosure` is a strict strengthening of the old route
`finite_future_index → finite_free_disclosure`.

The witness is a *length-triggered mask*: the input passes through unchanged when its
length is a power of two, and is blanked out otherwise.

```
lengthPow2Mask w = if |w| is a power of two then w else 0^|w|
```

* Only two advice prefixes are reachable above any prefix `p` — namely `p` itself and
  the all-`false` word — so `finite_future_variation` holds with `N = 2`.
* But suffixes of different lengths are almost never future-equivalent: choosing a left
  context of length `2^k' - k` makes the shorter suffix land exactly on a power of two
  while the longer one overshoots into the gap. Hence there are infinitely many
  future-equivalence classes and `finite_future_index` fails.

This is exactly the phenomenon that forced the relative-pointer encoding in
`finite_future_variation_iff_free_disclosure`: the number of *values* above each prefix is
bounded even though the number of *suffix classes* is not.
-/

namespace CellularAutomatas

open Classical

/-- The powers of two. -/
def isPow2 (n : ℕ) : Prop := ∃ k, n = 2 ^ k

/-- Nothing strictly between two consecutive powers of two is a power of two. -/
lemma not_isPow2_of_between {j d : ℕ} (hd : 0 < d) (hd' : d < 2 ^ j) :
    ¬ isPow2 (2 ^ j + d) := by
  rintro ⟨i, hi⟩
  have hlo : 2 ^ j < 2 ^ i := by omega
  have hhi : 2 ^ i < 2 ^ (j + 1) := by rw [← hi, pow_succ]; omega
  have h1 : j < i := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlo
  have h2 : i < j + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hhi
  omega

/-- The length-triggered mask advice. -/
noncomputable def lengthPow2Mask : Advice Bool Bool where
  f := fun w => if isPow2 w.length then w else List.replicate w.length false
  len := by intro w; split <;> simp

@[simp]
lemma lengthPow2Mask_apply (w : Word Bool) :
    lengthPow2Mask w = if isPow2 w.length then w else List.replicate w.length false :=
  rfl


/-! ## Only two advice prefixes are reachable above any prefix -/

/-- Above `p`, the suffix can only decide *whether* the mask fires, not what it reveals. -/
lemma rel_repr_lengthPow2Mask (p s : Word Bool) :
    rel_repr lengthPow2Mask p s =
      if isPow2 (p.length + s.length) then p else List.replicate p.length false := by
  show (lengthPow2Mask (p ++ s)).take p.length = _
  rw [lengthPow2Mask_apply, List.length_append]
  split
  · show (p ++ s).take p.length = p
    exact List.take_left
  · rw [List.take_replicate]
    congr 1
    omega

theorem lengthPow2Mask_finite_future_variation : lengthPow2Mask.finite_future_variation := by
  refine ⟨2, fun p => ?_⟩
  have hsub : (Set.univ.image (fun s : Word Bool => rel_repr lengthPow2Mask p s))
      ⊆ ({p, List.replicate p.length false} : Set (Word Bool)) := by
    rintro l ⟨s, -, rfl⟩
    simp only [rel_repr_lengthPow2Mask]
    split
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
  refine le_trans (Set.encard_mono hsub) ?_
  calc ({p, List.replicate p.length false} : Set (Word Bool)).encard
      ≤ ({List.replicate p.length false} : Set (Word Bool)).encard + 1 :=
        Set.encard_insert_le _ _
    _ = 2 := by rw [Set.encard_singleton]; rfl


/-! ## But there are infinitely many future-equivalence classes -/

/-- A shorter and a longer suffix are separated by the left context of length `2 ^ k' - k`:
it lands the shorter one exactly on a power of two and the longer one just past it. -/
lemma not_future_equivalent_of_lt {k k' : ℕ} (hlt : k < k') :
    ¬ lengthPow2Mask.future_equivalent
        (List.replicate k true) (List.replicate k' true) := by
  intro hfe
  have hk' : k' < 2 ^ k' := Nat.lt_two_pow_self
  -- the separating context
  obtain ⟨n, hn⟩ : ∃ n, 2 ^ k' - k = n + 1 := ⟨2 ^ k' - k - 1, by omega⟩
  set m := n + 1 with hm
  have hmk : m + k = 2 ^ k' := by omega
  have hmk' : m + k' = 2 ^ k' + (k' - k) := by omega
  have hcontext := hfe (List.replicate m true)
  -- the short suffix makes the total length a power of two, so the context survives
  have hfires : isPow2 ((List.replicate m true ++ List.replicate k true).length) := by
    simpa [hmk] using ⟨k', rfl⟩
  -- the long suffix overshoots into the gap, so the context is blanked out
  have hblank : ¬ isPow2 ((List.replicate m true ++ List.replicate k' true).length) := by
    have := not_isPow2_of_between (j := k') (d := k' - k) (by omega) (by omega)
    simpa [hmk'] using this
  rw [lengthPow2Mask_apply, lengthPow2Mask_apply, if_pos hfires, if_neg hblank] at hcontext
  rw [List.length_replicate] at hcontext
  rw [show (List.replicate m true ++ List.replicate k true).take m
      = List.replicate m true from List.take_left' (by simp)] at hcontext
  rw [List.take_replicate] at hcontext
  rw [show min m (List.replicate m true ++ List.replicate k' true).length = m by simp] at hcontext
  -- `true^m = false^m` is impossible for `m > 0`
  rw [hm, List.replicate_succ, List.replicate_succ] at hcontext
  simp at hcontext

theorem lengthPow2Mask_not_finite_future_index :
    IsEmpty lengthPow2Mask.finite_future_index := by
  constructor
  intro h
  obtain ⟨k, k', hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => h.index (List.replicate n true))
  have hfe : lengthPow2Mask.future_equivalent
      (List.replicate k true) (List.replicate k' true) := (h.index_eq_iff _ _).1 heq
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact not_future_equivalent_of_lt hlt hfe
  · refine not_future_equivalent_of_lt hgt (fun x => (hfe x).symm)


/-! ## The separation -/

/-- `finite_future_variation` — equivalently `finite_free_disclosure` — does **not** imply
`finite_future_index`. -/
theorem finite_future_variation_not_imp_finite_future_index :
    ¬ (∀ adv : Advice Bool Bool, adv.finite_future_variation → Nonempty adv.finite_future_index) :=
  fun h => (lengthPow2Mask_not_finite_future_index).elim'
    (h lengthPow2Mask lengthPow2Mask_finite_future_variation).some

end CellularAutomatas
