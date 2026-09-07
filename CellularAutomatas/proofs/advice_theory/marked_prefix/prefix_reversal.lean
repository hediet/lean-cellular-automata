import CellularAutomatas.proofs.advice_theory.marked_prefix.prefix_transform
import CellularAutomatas.proofs.advice_theory.rev_not_finite_future_variation
import CellularAutomatas.proofs.advice_theory.future_variation_closure

/-!
# Reversal on a selected prefix

At lengths `4 * 2^k`, a selector exposing exactly `2 * 2^k` input symbols
lets a suffix of length `2^k` control the first `2^k` output symbols after
reversal. This gives unbounded finite future variation.
-/

namespace CellularAutomatas.MarkedPrefix

open Classical

variable {α : Type}

/-- Reversal lifted into `Option`, reserving `none` for later padding. -/
def optionalReversal (α : Type) : Advice α (Option α) where
  f w := w.reverse.map some
  len w := by simp

@[simp]
theorem optionalReversal_apply (w : Word α) :
    optionalReversal α w = w.reverse.map some := rfl

/-- Reverse the selected input prefix and pad the remaining positions with `none`. -/
def prefixReversal (l : BoundedSelector) : Advice α (Option α) :=
  prefixTransform l (optionalReversal α) none

@[simp]
theorem prefixReversal_apply (l : BoundedSelector) (w : Word α) :
    prefixReversal l w =
      (w.take (l w.length)).reverse.map some ++
        List.replicate (w.length - l w.length) none := rfl

/-- At a dyadic witness length, the first block of prefix reversal is controlled
exactly by the reversed middle block `v`. -/
theorem prefixReversal_rel_repr_dyadic (l : BoundedSelector)
    (hdyadic : ∀ k, l (4 * 2 ^ k) = 2 * 2 ^ k)
    (k : ℕ) (p v : Word α) (pad : α)
    (hp : p.length = 2 ^ k) (hv : v.length = 2 ^ k) :
    rel_repr (prefixReversal l) p
        (v ++ List.replicate (2 * 2 ^ k) pad) =
      v.reverse.map some := by
  have htotal :
      (p ++ (v ++ List.replicate (2 * 2 ^ k) pad)).length =
        4 * 2 ^ k := by
    simp only [List.length_append, List.length_replicate, hp, hv]
    omega
  have htake :
      (p ++ (v ++ List.replicate (2 * 2 ^ k) pad)).take (2 * 2 ^ k) =
        p ++ v := by
    rw [← List.append_assoc]
    apply List.take_left'
    simp only [List.length_append, hp, hv]
    omega
  unfold rel_repr
  rw [prefixReversal_apply, htotal, hdyadic k, htake,
    List.reverse_append, List.map_append, hp]
  rw [List.append_assoc]
  apply List.take_left'
  simp [hv]

/-- Every selector with the stated dyadic values gives a prefix-reversal advice
with unbounded future variation. -/
theorem prefixReversal_not_finite_future_variation [Alphabet α]
    (l : BoundedSelector) (hdyadic : ∀ k, l (4 * 2 ^ k) = 2 * 2 ^ k)
    (hcard : 2 ≤ Fintype.card α) :
    ¬ (prefixReversal (α := α) l).finite_future_variation := by
  obtain ⟨a, b, hab⟩ : ∃ a b : α, a ≠ b := by
    simpa [Fintype.one_lt_card_iff] using
      (show 1 < Fintype.card α by omega)
  rintro ⟨N, hN⟩
  let r := 2 ^ N
  let p : Word α := List.replicate r default
  let suffixes : Finset (Word (Option α)) :=
    (Finset.range (r + 1)).image fun j =>
      (RevNotFiniteFutureVariation.suffixFamily a b r j).reverse.map some
  have hsubset : (suffixes : Set (Word (Option α))) ⊆
      Set.univ.image
        (fun s : Word α => rel_repr (prefixReversal l) p s) := by
    intro output houtput
    have houtput' : output ∈ suffixes := houtput
    rw [Finset.mem_image] at houtput'
    obtain ⟨j, hj, rfl⟩ := houtput'
    let v := RevNotFiniteFutureVariation.suffixFamily a b r j
    refine ⟨v ++ List.replicate (2 * r) default, Set.mem_univ _, ?_⟩
    have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
    have hv : v.length = r :=
      RevNotFiniteFutureVariation.suffixFamily_length a b hjr
    have hp : p.length = 2 ^ N := by simp [p, r]
    have hv' : v.length = 2 ^ N := by simpa only [r] using hv
    simpa only [r] using
      prefixReversal_rel_repr_dyadic l hdyadic N p v (default : α) hp hv'
  have hsuffixes_card : suffixes.card = r + 1 := by
    have hinj : Set.InjOn
        (fun j =>
          (RevNotFiniteFutureVariation.suffixFamily a b r j).reverse.map some)
        (Finset.range (r + 1) : Set ℕ) := by
      intro j₁ hj₁ j₂ hj₂ heq
      apply RevNotFiniteFutureVariation.suffixFamily_injective a b hab r
      · exact Nat.le_of_lt_succ (Finset.mem_range.1 hj₁)
      · exact Nat.le_of_lt_succ (Finset.mem_range.1 hj₂)
      · apply List.reverse_injective
        exact List.map_injective_iff.mpr (Option.some_injective α) heq
    rw [show suffixes.card = (Finset.range (r + 1)).card from
      Finset.card_image_of_injOn hinj, Finset.card_range]
  have hlower : (↑(r + 1) : ℕ∞) ≤
      (Set.univ.image
        (fun s : Word α => rel_repr (prefixReversal l) p s)).encard := by
    rw [← hsuffixes_card, ← Set.encard_coe_eq_coe_finsetCard suffixes]
    exact Set.encard_mono hsubset
  have hupper := hN p
  have hcontra : (↑(r + 1) : ℕ∞) ≤ ↑N := le_trans hlower hupper
  have hrN : r + 1 ≤ N := ENat.coe_le_coe.mp hcontra
  have hNr : N < r := by
    change N < 2 ^ N
    exact Nat.lt_two_pow_self
  omega

/-- Such prefix reversal cannot be represented by two-stage advice. -/
theorem prefixReversal_not_two_stage_advice [Alphabet α]
    (l : BoundedSelector) (hdyadic : ∀ k, l (4 * 2 ^ k) = 2 * 2 ^ k)
    (hcard : 2 ≤ Fintype.card α) :
    IsEmpty (prefixReversal (α := α) l).is_two_stage_advice := by
  constructor
  intro h
  exact prefixReversal_not_finite_future_variation l hdyadic hcard
    h.finite_future_variation

/-- Select half of the greatest power of two not exceeding `n`, with zero
selected at lengths below two. -/
def dyadicSelector : BoundedSelector where
  select n := if n < 2 then 0 else 2 ^ (Nat.log2 n - 1)
  bound n := by
    by_cases hn : n < 2
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      have hn0 : n ≠ 0 := by omega
      exact le_trans
        (Nat.pow_le_pow_right (by omega) (Nat.sub_le (Nat.log2 n) 1))
        (Nat.log2_self_le hn0)

@[simp]
theorem dyadicSelector_at_four_pow (k : ℕ) :
    dyadicSelector (4 * 2 ^ k) = 2 * 2 ^ k := by
  have hpow : 4 * 2 ^ k = 2 ^ (k + 2) := by
    simp [pow_add, Nat.mul_comm]
  have hlog : Nat.log2 (4 * 2 ^ k) = k + 2 := by
    rw [hpow, Nat.log2_eq_log_two]
    exact Nat.log_pow Nat.one_lt_two (k + 2)
  have hnot : ¬ 4 * 2 ^ k < 2 := by
    have hpos := Nat.two_pow_pos k
    omega
  change
    (if 4 * 2 ^ k < 2 then 0 else 2 ^ (Nat.log2 (4 * 2 ^ k) - 1)) =
      2 * 2 ^ k
  rw [if_neg hnot, hlog]
  have hexponent : k + 2 - 1 = k + 1 := by omega
  rw [hexponent, pow_succ]
  omega

/-- The canonical dyadic prefix-reversal advice. -/
def dyadicPrefixReversal (α : Type) : Advice α (Option α) :=
  prefixReversal dyadicSelector

theorem dyadicPrefixReversal_not_finite_future_variation [Alphabet α]
    (hcard : 2 ≤ Fintype.card α) :
    ¬ (dyadicPrefixReversal α).finite_future_variation := by
  exact prefixReversal_not_finite_future_variation dyadicSelector
    dyadicSelector_at_four_pow hcard

theorem dyadicPrefixReversal_not_two_stage_advice [Alphabet α]
    (hcard : 2 ≤ Fintype.card α) :
    IsEmpty (dyadicPrefixReversal α).is_two_stage_advice := by
  exact prefixReversal_not_two_stage_advice dyadicSelector
    dyadicSelector_at_four_pow hcard

end CellularAutomatas.MarkedPrefix
