/-
  # Non-regularity of the Powers-of-2 Length Language

  Main result: `exp_word_not_regular`
    The language `{ w : Word Unit | ∃ n, |w| = 2^n }` is **not** regular.

  ## Proof path

  Three layers, each named and independently meaningful:

  ```
                        Language.IsRegular L
                              │
            (Pumping → AP-rich, layer 2 — axiomatized)
                              ▼
                Λ(L) `ContainsInfiniteAP`
                              │
              (Λ(L) = {2^k}, layer 1)
                              ▼
                {2^k}  `ContainsInfiniteAP`
                              │
                (Arithmetic core, layer 3)
                              ▼
                   contradicts `IsAPFree`
  ```

  The arithmetic core is fully proved here:

      **No three powers of 2 form an arithmetic progression.**

  Combined with `oca_rt_unary_regular` and `exp_word_length_rt`, this yields
  the unconditional separation `ℒ(OCA_rt Unit) ⊊ ℒ(CA_rt Unit)`.
-/

import CellularAutomatas.defs
import Mathlib.Computability.DFA
import Mathlib.Data.List.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace CellularAutomatas

/-! ## Layer 0: Length set of a unary slice of a language -/

/-- The set of lengths `n` such that `aⁿ ∈ L`, for any letter `a : α`.
    Captures the unary "shadow" of `L` along the letter `a`. -/
def Language.lengthSet {α : Type} (a : α) (L : Language α) : Set ℕ :=
  { n | List.replicate n a ∈ L }

/-! ## Layer 3: Arithmetic — `ContainsInfiniteAP` vs `IsAPFree`

  Two opposite combinatorial properties of subsets of ℕ:

  - **`ContainsInfiniteAP S`**: `S` contains an infinite arithmetic
    progression `{a + i·p : i ∈ ℕ}` with step `p ≥ 1`.
  - **`IsAPFree S`**: `S` has no three-term arithmetic progression.

  These are clearly incompatible (any infinite AP gives `a, a+p, a+2p`
  as a 3-AP), and that incompatibility is the engine of the whole proof. -/

/-- A set `S ⊆ ℕ` **contains an infinite arithmetic progression**:
    there is a starting point `a` and step `p ≥ 1` such that every
    `a + i·p` lies in `S`. -/
def Set.ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a p, 1 ≤ p ∧ ∀ i, a + i * p ∈ S

/-- A set `S ⊆ ℕ` is **AP-free**: no three distinct elements `x < y < z`
    of `S` satisfy `y - x = z - y`. -/
def Set.IsAPFree (S : Set ℕ) : Prop :=
  ∀ x y z, x < y → y < z → x ∈ S → y ∈ S → z ∈ S → y - x ≠ z - y

/-- **The fundamental tension.** A set cannot simultaneously contain an
    infinite AP and be AP-free: the first three terms `a, a+p, a+2p`
    of the AP form a 3-AP. -/
theorem Set.not_containsInfiniteAP_of_isAPFree {S : Set ℕ}
    (h_AP : Set.ContainsInfiniteAP S) (h_free : Set.IsAPFree S) : False := by
  obtain ⟨a, p, hp, hAP⟩ := h_AP
  -- Take the three terms a, a+p, a+2p
  have h0 : a + 0 * p ∈ S := hAP 0
  have h1 : a + 1 * p ∈ S := hAP 1
  have h2 : a + 2 * p ∈ S := hAP 2
  -- Specialize IsAPFree to x = a, y = a+p, z = a+2p
  apply h_free a (a + p) (a + 2 * p) (by omega) (by omega)
    (by simpa using h0) (by simpa using h1) (by simpa using h2)
  -- Both gaps equal p
  omega

/-! ## Layer 3.b: Powers of 2 are AP-free

  The arithmetic heart of the proof: between any three powers of 2,
  the gaps must be unequal. The identity

      `2·2^b = 2^a + 2^c`  ⟹  `2·2^d = 1 + 2^e`  (after dividing by 2^a)

  collides with the bound `2·2^d ≤ 2^e` (since `e ≥ d + 1`). -/

/-- **No three powers of 2 form a 3-term arithmetic progression.**

    Suppose `2^a < 2^b < 2^c` with equal gaps `2^b - 2^a = 2^c - 2^b`.
    Setting `d = b - a ≥ 1` and `e = c - a > d`, the identity
    `2·2^b = 2^a + 2^c` divides by `2^a` to give `2·2^d = 1 + 2^e`.
    But `e ≥ d + 1` implies `2^e ≥ 2·2^d`, hence `1 + 2^e > 2·2^d`. ⊥ -/
theorem Set.IsAPFree.powers_of_two :
    Set.IsAPFree { n : ℕ | ∃ k, n = 2 ^ k } := by
  rintro _ _ _ hxy hyz ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ hgap
  -- 2^a < 2^b < 2^c implies a < b < c
  have h_one_lt : (1 : ℕ) < 2 := by norm_num
  have hab : a < b := (pow_lt_pow_iff_right₀ h_one_lt).mp hxy
  have hbc : b < c := (pow_lt_pow_iff_right₀ h_one_lt).mp hyz
  -- Rewrite gap equation as the symmetric form  2·2^b = 2^a + 2^c
  have h_sum : 2 * 2 ^ b = 2 ^ a + 2 ^ c := by
    have h_le1 : 2 ^ a ≤ 2 ^ b := le_of_lt hxy
    have h_le2 : 2 ^ b ≤ 2 ^ c := le_of_lt hyz
    omega
  -- Introduce gap exponents d = b - a, e = c - a, with 1 ≤ d < e
  set d := b - a with hd_def
  set e := c - a with he_def
  have hd_pos : 1 ≤ d := by omega
  have hde : d < e := by omega
  -- Substitute b = a + d, c = a + e and split the powers
  have h_sum' : 2 * (2 ^ a * 2 ^ d) = 2 ^ a + 2 ^ a * 2 ^ e := by
    have hb_eq : b = a + d := by omega
    have hc_eq : c = a + e := by omega
    rw [hb_eq, hc_eq, pow_add, pow_add] at h_sum
    exact h_sum
  -- Cancel 2^a > 0:  2·2^d = 1 + 2^e
  have h_pos : 0 < 2 ^ a := Nat.two_pow_pos a
  have h_div : 2 * 2 ^ d = 1 + 2 ^ e := by
    have h_eq : 2 ^ a * (2 * 2 ^ d) = 2 ^ a * (1 + 2 ^ e) := by linarith
    exact Nat.eq_of_mul_eq_mul_left h_pos h_eq
  -- Bound: 2^e ≥ 2^(d+1) = 2·2^d, since e ≥ d + 1
  have h_bound : 2 * 2 ^ d ≤ 2 ^ e := by
    have h_step : 2 ^ (d + 1) ≤ 2 ^ e :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ] at h_step
    linarith
  -- Now `2·2^d = 1 + 2^e` and `2·2^d ≤ 2^e` together are impossible
  omega

/-! ## Layer 1: The length set of the exp-language is `{2^k}` -/

/-- The length set (at `()`) of the powers-of-2 language is exactly `{2^k}`. -/
theorem exp_word_lengthSet :
    Language.lengthSet () ({ w : Word Unit | ∃ n, w.length = 2 ^ n } : Language Unit) =
      { n | ∃ k, n = 2 ^ k } := by
  ext n
  show List.replicate n () ∈ ({ w | ∃ k, w.length = 2 ^ k } : Language Unit) ↔
       ∃ k, n = 2 ^ k
  simp only [Set.mem_setOf_eq, List.length_replicate]

/-- The set `{2^k : k}` is infinite (the map `k ↦ 2^k` is injective into it). -/
theorem powers_of_two_infinite : Set.Infinite { n : ℕ | ∃ k, n = 2 ^ k } := by
  -- The map k ↦ 2^k is injective and lands in the set
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ k)
  · -- injectivity of k ↦ 2^k for base ≥ 2
    intro k₁ k₂ hk
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hk
  · -- 2^k is in the set
    intro k
    exact ⟨k, rfl⟩

/-! ## Layer 2: Pumping bridge — regular ⟹ AP-rich length set

  This is the **only** automata-theoretic step in the whole proof.

  **Proof strategy.** Let `M` be a DFA recognizing `L` over alphabet `α`,
  with state count `|σ|`. The pumping length is `|σ|`. Since `Λ_a(L)` is
  infinite, pick `n ≥ |σ|` with `aⁿ ∈ L`. Pumping decomposes
  `aⁿ = pre ++ mid ++ suf` with `mid ≠ []` and
  `{pre} · {mid}∗ · {suf} ⊆ M.accepts`. Since `aⁿ` consists entirely of
  `a`'s, so do `pre`, `mid`, `suf`. Hence the pumped word
  `pre ++ midⁱ⁺¹ ++ suf` equals `replicate (n + i·|mid|) a` and lies in
  `L` for every `i ∈ ℕ`, giving the AP `{n + i·|mid| : i ∈ ℕ}`. -/

/-- **Layer 2: regularity ⇒ infinite AP in length set.**

    For any regular `L : Language α` and letter `a : α` with infinite
    `Λ_a(L)`, the length set contains an infinite arithmetic progression.

    The pumping decomposition `aⁿ = pre ++ mid ++ suf` produces the AP
    `{n + i·|mid| : i ∈ ℕ}` with step `|mid| ≥ 1`. -/
theorem regular_infinite_lengthSet_contains_infinite_AP
    {α : Type} [Alphabet α] (a : α) (L : Language α)
    (hreg : L.IsRegular) (hinf : (Language.lengthSet a L).Infinite) :
    Set.ContainsInfiniteAP (Language.lengthSet a L) := by
  -- Step 1: Extract a DFA from regularity
  -- Use the same-universe formulation Language.IsRegular directly
  obtain ⟨σ, _, M, hM⟩ := hreg
  -- Step 2: An infinite ℕ-set has elements > any bound (specifically, > |σ|)
  have h_not_bdd : ¬ BddAbove (Language.lengthSet a L) := hinf.not_bddAbove
  rw [not_bddAbove_iff] at h_not_bdd
  obtain ⟨n, hn_mem, hn_gt⟩ := h_not_bdd (Fintype.card σ)
  -- Step 3: Apply the pumping lemma to aⁿ
  have hn_acc : List.replicate n a ∈ M.accepts := by
    rw [hM]; exact hn_mem
  have hn_len : Fintype.card σ ≤ (List.replicate n a).length := by
    rw [List.length_replicate]; exact le_of_lt hn_gt
  obtain ⟨pre, mid, suf, h_split, _, h_mid_ne, h_pump⟩ :=
    M.pumping_lemma hn_acc hn_len
  -- Step 4: From `replicate n a = pre ++ mid ++ suf`, every element is `a`
  have h_all_a : ∀ b, b ∈ pre ++ mid ++ suf → b = a := fun b hb =>
    List.eq_of_mem_replicate (h_split ▸ hb)
  have h_mid_pos : 1 ≤ mid.length := List.length_pos_iff_ne_nil.mpr h_mid_ne
  -- Step 5: |pre| + |mid| + |suf| = n
  have h_n_split : pre.length + mid.length + suf.length = n := by
    have h := congrArg List.length h_split
    simp at h
    omega
  -- Step 6: Build the infinite AP starting at n with step |mid|
  refine ⟨n, mid.length, h_mid_pos, ?_⟩
  intro i
  -- The pumped word: pre ++ midⁱ⁺¹ ++ suf
  set pumpedW := pre ++ (List.replicate (i + 1) mid).flatten ++ suf
    with h_pumpedW_def
  -- (a) pumpedW ∈ M.accepts via pumping
  have h_pumped_acc : pumpedW ∈ M.accepts := by
    apply h_pump
    -- pumpedW = pre ++ midⁱ⁺¹ ++ suf ∈ {pre} · {mid}∗ · {suf}
    refine ⟨pre ++ (List.replicate (i + 1) mid).flatten, ?_, suf, rfl, rfl⟩
    refine ⟨pre, rfl, (List.replicate (i + 1) mid).flatten, ?_, rfl⟩
    -- midⁱ⁺¹ = (replicate (i+1) mid).flatten ∈ {mid}∗
    apply Language.join_mem_kstar
    intro u hu
    rw [List.eq_of_mem_replicate hu]
    rfl
  -- (b) Every element of pumpedW is `a`
  have h_pumped_all_a : ∀ b ∈ pumpedW, b = a := by
    intro b hb
    rw [h_pumpedW_def, List.mem_append, List.mem_append] at hb
    rcases hb with (hbpre | hbflat) | hbsuf
    · exact h_all_a b (List.mem_append_left _ (List.mem_append_left _ hbpre))
    · -- b ∈ flatten(replicate (i+1) mid) ⇒ b ∈ mid
      rw [List.mem_flatten] at hbflat
      obtain ⟨ys, hys, hbys⟩ := hbflat
      rw [List.eq_of_mem_replicate hys] at hbys
      exact h_all_a b (List.mem_append_left _ (List.mem_append_right _ hbys))
    · exact h_all_a b (List.mem_append_right _ hbsuf)
  -- Helper: length of `(replicate k mid).flatten` is `k * |mid|`
  have h_flat_len : ∀ k, (List.replicate k mid).flatten.length = k * mid.length := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
      ring
  -- (c) Length is exactly n + i * |mid|
  have h_pumped_len : pumpedW.length = n + i * mid.length := by
    show (pre ++ (List.replicate (i + 1) mid).flatten ++ suf).length =
         n + i * mid.length
    rw [List.length_append, List.length_append, h_flat_len]
    -- pre.length + (i + 1) * mid.length + suf.length = n + i * mid.length
    have := h_n_split
    ring_nf
    omega
  -- (d) pumpedW = replicate (n + i * |mid|) a
  have h_pumped_eq : pumpedW = List.replicate (n + i * mid.length) a := by
    apply List.eq_replicate_iff.mpr
    exact ⟨h_pumped_len, h_pumped_all_a⟩
  -- Conclude: replicate (n + i*|mid|) a ∈ L
  show List.replicate (n + i * mid.length) a ∈ L
  rw [← h_pumped_eq, ← hM]
  exact h_pumped_acc

/-! ## Main theorem -/

/-- **The exponential-length unary language is not regular.**

    Walks the path: regular ⇒ AP-rich length set, `{2^k}` is AP-free,
    contradiction. -/
theorem exp_word_not_regular :
    ¬ Language.IsRegular
        ({ w : Word Unit | ∃ n, w.length = 2 ^ n } : Language Unit) := by
  set L : Language Unit := { w | ∃ n, w.length = 2 ^ n } with hL
  intro hreg
  -- Λ(L) = {2^k}
  have hΛ : Language.lengthSet () L = { n | ∃ k, n = 2 ^ k } := exp_word_lengthSet
  -- Λ(L) is infinite
  have hinf : (Language.lengthSet () L).Infinite := hΛ ▸ powers_of_two_infinite
  -- Pumping ⟹ AP-rich
  have h_AP : Set.ContainsInfiniteAP (Language.lengthSet () L) :=
    regular_infinite_lengthSet_contains_infinite_AP () L hreg hinf
  -- {2^k} is AP-free
  have h_free : Set.IsAPFree (Language.lengthSet () L) :=
    hΛ ▸ Set.IsAPFree.powers_of_two
  -- AP-rich and AP-free can't both hold
  exact Set.not_containsInfiniteAP_of_isAPFree h_AP h_free

end CellularAutomatas
