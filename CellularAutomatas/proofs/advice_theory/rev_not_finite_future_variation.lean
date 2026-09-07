import CellularAutomatas.proofs.advice_theory.rev_is_rt_advice
import CellularAutomatas.proofs.advice_theory.finite_future_variation_iff_free_disclosure

/-!
# Reversal has unbounded future variation

For a fixed prefix of length `n`, reversal exposes the reverse of every suffix of
length `n` as an advice prefix.  Two distinct alphabet symbols already give `n + 1`
distinct such suffixes, so no uniform finite-future-variation bound can exist.
-/

namespace CellularAutomatas

open Classical

variable {α : Type} [Alphabet α]

namespace RevNotFiniteFutureVariation

/-- A length-`n` word whose first `k` symbols are `a` and whose remaining symbols
are `b`. -/
def suffixFamily (a b : α) (n k : ℕ) : Word α :=
  List.replicate k a ++ List.replicate (n - k) b

lemma suffixFamily_length (a b : α) {n k : ℕ} (hk : k ≤ n) :
    (suffixFamily a b n k).length = n := by
  simp [suffixFamily]
  omega

lemma suffixFamily_injective (a b : α) (hab : a ≠ b) (n : ℕ) :
    Set.InjOn (suffixFamily a b n) (Set.Iic n) := by
  intro k₁ hk₁ k₂ hk₂ heq
  have hcount_b (m : ℕ) : List.count a (List.replicate m b) = 0 := by
    rw [List.count_eq_zero]
    simp [hab]
  have hcount := congrArg (List.count a) heq
  simp [suffixFamily, hcount_b] at hcount
  exact hcount

/-- If the suffix is as long as the prefix, the visible reversal advice prefix is
exactly the reversed suffix. -/
lemma rev_rel_repr_eq_reverse (p s : Word α) (hlen : s.length = p.length) :
    rel_repr (Advice.rev α) p s = s.reverse := by
  simp [rel_repr, Advice.rev, hlen]

end RevNotFiniteFutureVariation

/-- Over an alphabet with at least two symbols, reversal has no finite-future-variation
bound. -/
theorem Advice.rev_not_finite_future_variation
    (hcard : 2 ≤ Fintype.card α) : ¬ (Advice.rev α).finite_future_variation := by
  obtain ⟨a, b, hab⟩ : ∃ a b : α, a ≠ b := by
    simpa [Fintype.one_lt_card_iff] using (show 1 < Fintype.card α by omega)
  rintro ⟨N, hN⟩
  let p : Word α := List.replicate N default
  let suffixes : Finset (Word α) :=
    (Finset.range (N + 1)).image
      (fun k => (RevNotFiniteFutureVariation.suffixFamily a b N k).reverse)
  have hsubset : (suffixes : Set (Word α)) ⊆
      Set.univ.image (fun s : Word α => rel_repr (Advice.rev α) p s) := by
    intro v hv
    have hv' : v ∈ suffixes := hv
    rw [Finset.mem_image] at hv'
    obtain ⟨k, hk, rfl⟩ := hv'
    refine ⟨RevNotFiniteFutureVariation.suffixFamily a b N k, Set.mem_univ _, ?_⟩
    apply RevNotFiniteFutureVariation.rev_rel_repr_eq_reverse
    simp only [p, List.length_replicate]
    exact RevNotFiniteFutureVariation.suffixFamily_length a b (Nat.le_of_lt_succ
      (Finset.mem_range.1 hk))
  have hsuffixes_card : suffixes.card = N + 1 := by
    have hinj : Set.InjOn
        (fun k => (RevNotFiniteFutureVariation.suffixFamily a b N k).reverse)
        (Finset.range (N + 1) : Set ℕ) := by
      intro k₁ hk₁ k₂ hk₂ heq
      apply RevNotFiniteFutureVariation.suffixFamily_injective a b hab N
      · exact Nat.le_of_lt_succ (Finset.mem_range.1 hk₁)
      · exact Nat.le_of_lt_succ (Finset.mem_range.1 hk₂)
      · exact List.reverse_injective heq
    rw [show suffixes.card = (Finset.range (N + 1)).card from
      Finset.card_image_of_injOn hinj, Finset.card_range]
  have hlower : (↑(N + 1) : ℕ∞) ≤
      (Set.univ.image (fun s : Word α => rel_repr (Advice.rev α) p s)).encard := by
    rw [← hsuffixes_card, ← Set.encard_coe_eq_coe_finsetCard suffixes]
    exact Set.encard_mono hsubset
  have hupper := hN p
  have hcontra : (↑(N + 1) : ℕ∞) ≤ ↑N := le_trans hlower hupper
  have : N + 1 ≤ N := ENat.coe_le_coe.mp hcontra
  omega

/-- In particular, reversal cannot be presented as two-stage advice. -/
theorem Advice.rev_not_two_stage_advice
    (hcard : 2 ≤ Fintype.card α) : IsEmpty (Advice.rev α).is_two_stage_advice := by
  constructor
  intro h
  apply Advice.rev_not_finite_future_variation hcard
  exact Advice.finite_future_variation_of_finite_free_disclosure
    h.finite_rt_disclosure.finite_free_disclosure

end CellularAutomatas
