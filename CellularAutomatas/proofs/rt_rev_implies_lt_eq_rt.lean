import CellularAutomatas.lt_closed
import CellularAutomatas.proofs.lx_rt_implies_rt
import CellularAutomatas.proofs.lift_language

/-!
# ℒ(CA_rt) = ℒ_rev(CA_rt) ⟹ ℒ(CA_2n) ⊆ ℒ(CA_rt)

## Proof by double reversal

Given L ∈ ℒ(CA_2n), we show L ∈ ℒ(CA_rt) using reversal closure.

1. **Lift** L from Language β to Language (Option β) via `w ↦ w.map some`.
2. **Lift to CA_2n**: lifted L ∈ ℒ(CA_2n (Option β)) by `lift_mem_ca_2n`.
3. **Pad**: L_none(lifted(L)^R)^R ∈ ℒ(CA_rt (Option β)).
   Since `none` never appears in `w.map some`, the padding acts as pure border.
4. **First reversal**: L_none(lifted(L)^R) ∈ ℒ(CA_rt (Option β)) by reversal closure.
5. **Remove padding**: lifted(L)^R ∈ ℒ(CA_rt (Option β)) by `lx_rt_implies_rt`.
6. **Second reversal**: lifted(L) ∈ ℒ(CA_rt (Option β)) by reversal closure.
7. **Project back**: L ∈ ℒ(CA_rt β) via `map_embed`.

The corollary ℒ(CA_lt) = ℒ(CA_rt) follows by composing with Fischer's speedup
`ca_linear_time_eq_2n : ℒ(CA_lt) = ℒ(CA_2n)`.
-/

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

/-! ## Speedup: ℒ(CA_lt) = ℒ(CA_2n) -/

/-- Linear-time CAs can be sped up to time 2n.
    Fischer's speedup theorem. -/
theorem ca_linear_time_eq_2n : ℒ (CA_lt α) = ℒ (CA_2n α) := by
  sorry

/-! ## Key lemma: padded language over Option α is real-time recognizable

Since `none` never appears in any word of `(Language.lift L)`, padding with `none^m`
acts as pure border — the CA sees quiescent cells beyond the "real" word.
-/

/-- Extend a tCellAutomaton α to Option α by collapsing `none` to border.
    Uses `Option.join : Option (Option α) → Option α` as embedding map.
    For input `w.map(some) ++ none^m`:
    - `some(some a)` → `C.embed(some a)` (real symbol)
    - `some(none)` → `C.embed(none)` (padding = border)
    - `none` → `C.embed(none)` (outer border)
    So the embedded configuration matches C's config on ⟬w⟭. -/
private def padCA (C : tCellAutomaton α) (t' : ℕ → ℕ) : tCellAutomaton (Option α) where
  toCellAutomaton := C.toCellAutomaton.map_embed Option.join
  t := t'
  p := C.p

/-- Key config identity: for `u = w.map(some) ++ none^m`, the padCA config equals C's config on w.
    Both map positions 0..n-1 to `C.embed(some w[i])` and all others to `C.embed(none)`. -/
private lemma padCA_embed_config_eq (C : tCellAutomaton α) (t' : ℕ → ℕ) (w : Word α) (m : ℕ) :
    @CellAutomaton.embed_config _ _ (padCA C t').toCellAutomaton (word_to_config (w.map some ++ List.replicate m none))
    = @CellAutomaton.embed_config _ _ C.toCellAutomaton (word_to_config w) := by
  funext p
  simp only [CellAutomaton.embed_config, padCA, CellAutomaton.map_embed, Function.comp]
  -- Both sides apply C.embed to some config value.
  -- Show: Option.join (word_to_config (w.map some ++ replicate m none) p) = word_to_config w p
  congr 1
  simp only [word_to_config]
  split_ifs with h1 h2 h2
  · -- h1: p ≥ 0 ∧ p < |w.map some ++ replicate m none|, h2: p ≥ 0 ∧ p < |w|
    have hp_toNat_lt : p.toNat < (w.map some).length := by simp; omega
    have : (w.map some ++ List.replicate m none)[p.toNat] = some w[p.toNat] := by
      rw [List.getElem_append_left hp_toNat_lt]
      simp [List.getElem_map]
    simp [this]
  · -- h1: in padded word, h2: NOT in w → position is in the none-padding
    simp only [List.length_append, List.length_map, List.length_replicate] at h1
    push_neg at h2
    have hp_pos := h1.1
    have hp_ge_w : (w.map some).length ≤ p.toNat := by
      simp only [List.length_map]
      have := h2 hp_pos
      omega
    have : (w.map some ++ List.replicate m none)[p.toNat] = none := by
      rw [List.getElem_append_right hp_ge_w]
      simp
    simp [this]
  · -- h1: NOT in padded word, h2: in w → impossible
    simp only [List.length_append, List.length_map, List.length_replicate] at h1
    push_neg at h1
    omega
  · -- Both out of range → both none
    rfl

/-- Computation identity: padCA has the same evolution as C since map_embed preserves nextt. -/
private lemma padCA_comp_eq (C : tCellAutomaton α) (t' : ℕ → ℕ) (w : Word α) (m : ℕ)
    (t : ℕ) (p : ℤ) :
    (padCA C t').toCellAutomaton.comp
      (@CellAutomaton.embed_config _ _ (padCA C t').toCellAutomaton (word_to_config (w.map some ++ List.replicate m none))) t p
    = C.toCellAutomaton.comp
      (@CellAutomaton.embed_config _ _ C.toCellAutomaton (word_to_config w)) t p := by
  simp only [CellAutomaton.comp, Function.comp, CellAutomaton.project_config,
             padCA, CellAutomaton.map_embed_nextt]
  congr 1
  exact congrFun (congrArg _ (padCA_embed_config_eq C t' w m)) p

/-- If L ∈ ℒ(CA_2n α), then the padded language { w.map(some) ++ none^m | w ∈ L }
    is in ℒ(CA_rt (Option α)), provided m(n) ≥ n for all n.

**Proof idea (reduction via time extension):**
1. Given C ∈ CA_2n recognizing L at time 2*(n-1)
2. `padCA C` maps `none` to border via `Option.join` — padding is invisible
3. `padCA_comp_eq`: computation on `w.map(some) ++ none^m` matches C on `w` at all times
4. `2*(n-1)` is time-constructible (`linearTimeConstructible 2`)
5. Since the timer also sees effective length n (via `Option.join`), it fires at `2*(n-1)`
6. Apply `time_extension`: latch answer at `2*(n-1)`, read at `N - 1 = n + m - 1`
7. Since `m ≥ n`, we have `N - 1 ≥ 2n - 1 ≥ 2*(n-1)` ✓ -/
lemma ca_2n_padded_in_ca_rt (L : Language α) (hL : L ∈ ℒ (CA_2n α))
    (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) :
    { u | ∃ w ∈ L, u = w.map some ++ List.replicate (m w.length) none } ∈ ℒ (CA_rt (Option α)) := by
  -- Step 1: Get C ∈ CA_2n recognizing L
  obtain ⟨C, hC, hCL⟩ := hL
  -- Step 2-3: padCA with Option.join makes padding invisible
  -- padCA_comp_eq shows computation matches C on effective word w
  -- Step 4-6: Use time_extension to latch at 2*(n-1) and read at N-1
  -- The timer sees effective length n (not N) because Option.join maps none to border
  sorry

/-- nextPow2 n ≥ n for all n (including n = 0). -/
private lemma nextPow2_ge_all (n : ℕ) : n ≤ nextPow2 n := by
  by_cases hn : n ≥ 1
  · exact nextPow2_ge n hn
  · simp only [Nat.not_le, Nat.lt_one_iff] at hn
    simp [hn, nextPow2]

/-- For L ∈ ℒ(CA_2n), the padded reversal over Option α is in CA_rt.

The language `Language.rev (L_x none (Language.rev (Language.lift L)))` consists of words
`w.map(some) ++ none^m` with `w ∈ L` and `m = nextPow2(|w|) ≥ |w|`.

**Proof of language equality:**
- `u ∈ Language.rev (L_x none (Language.rev (Language.lift L)))`
- ⟺ `u.reverse ∈ L_x none (Language.rev (Language.lift L))`
- ⟺ `∃ v ∈ Language.rev (Language.lift L), u.reverse = none^m ++ v` where `m = nextPow2(|v|)`
- ⟺ `∃ v, v.reverse ∈ Language.lift L ∧ u.reverse = none^m ++ v`
- ⟺ `∃ v, (∃ w ∈ L, v.reverse = w.map some) ∧ u.reverse = none^(nextPow2 |v|) ++ v`
- With `v.reverse = w.map some`: `|v| = |w|` and `u = v.reverse ++ none^m = w.map some ++ none^m`

Follows from `ca_2n_padded_in_ca_rt` since `nextPow2(n) ≥ n`. -/
theorem lx_none_rev_rev_in_ca_rt (L : Language α)
    (hL : L ∈ ℒ (CA_2n α)) :
    Language.rev (L_x (none : Option α) (Language.rev (Language.lift L))) ∈ ℒ (CA_rt (Option α)) := by
  -- The target language is { w.map(some) ++ none^m | w ∈ L, m = nextPow2(|w|) }
  -- This matches ca_2n_padded_in_ca_rt with m = nextPow2
  have h := ca_2n_padded_in_ca_rt L hL nextPow2 nextPow2_ge_all
  -- Need to show the languages are equal
  convert h using 1
  ext u
  simp only [Set.mem_setOf_eq, Language.rev, L_x, Language.lift]
  constructor
  · -- u ∈ rev(L_x none (rev(lift L))) → ∃ w ∈ L, u = w.map(some) ++ none^m
    -- Means: u.reverse ∈ L_x none (rev(lift L))
    intro hu
    obtain ⟨v, hv_mem, hu_rev_eq⟩ := hu
    -- hv_mem : v ∈ rev(lift L), i.e., v.reverse ∈ lift L
    obtain ⟨w, hw, hv_rev_eq⟩ := hv_mem
    -- hw : w ∈ L, hv_rev_eq : v.reverse = w.map some
    refine ⟨w, hw, ?_⟩
    -- Goal: u = w.map some ++ none^(nextPow2 |w|)
    -- From hu_rev_eq: u.reverse = none^(nextPow2 |v|) ++ v
    -- So u = v.reverse ++ none^(nextPow2 |v|) = w.map some ++ none^(nextPow2 |v|)
    -- And |v| = |v.reverse| = |w.map some| = |w|
    have hv_len : v.length = w.length := by
      have : v.reverse.length = (w.map some).length := by rw [hv_rev_eq]
      simp only [List.length_reverse, List.length_map] at this
      exact this
    calc u = u.reverse.reverse := by simp
      _ = (List.replicate (nextPow2 v.length) none ++ v).reverse := by rw [hu_rev_eq]
      _ = v.reverse ++ List.replicate (nextPow2 v.length) none := by
          simp [List.reverse_append, List.reverse_replicate]
      _ = w.map some ++ List.replicate (nextPow2 w.length) none := by rw [hv_rev_eq, hv_len]
  · -- ∃ w ∈ L, u = w.map(some) ++ none^m → u ∈ rev(L_x none (rev(lift L)))
    intro hu
    obtain ⟨w, hw, hu_eq⟩ := hu
    -- Need: u.reverse ∈ L_x none (rev(lift L))
    -- i.e., ∃ v ∈ rev(lift L), u.reverse = none^(nextPow2 |v|) ++ v
    -- Take v = (w.map some).reverse
    refine ⟨(w.map some).reverse, ?_, ?_⟩
    · -- v.reverse ∈ lift L, i.e., ((w.map some).reverse).reverse ∈ lift L
      show ((w.map some).reverse).reverse ∈ Language.lift L
      rw [List.reverse_reverse]
      exact ⟨w, hw, rfl⟩
    · -- u.reverse = none^(nextPow2 |v|) ++ v
      subst hu_eq
      -- Goal: (w.map some ++ none^m).reverse = none^(nextPow2 |v|) ++ v
      -- where v = (w.map some).reverse and m = nextPow2 |w|
      rw [List.reverse_append, List.reverse_replicate]
      -- Goal: none^m ++ (w.map some).reverse = none^(nextPow2 |v|) ++ v
      -- |v| = |(w.map some).reverse| = |w.map some| = |w|
      show List.replicate (nextPow2 w.length) none ++ (w.map some).reverse =
           List.replicate (nextPow2 ((w.map some).reverse).length) none ++ (w.map some).reverse
      rw [List.length_reverse, List.length_map]

/-! ## RT ⊆ LT: real-time is a special case of linear-time -/

/-- ℒ(CA_rt α) ⊆ ℒ(CA_lt α).

With t_lt defined as t n = c * (n - 1), real-time (c = 1) is a special case. -/
lemma ca_rt_subset_ca_lt : ℒ (CA_rt α) ⊆ ℒ (CA_lt α) := by
  intro L ⟨C, hC, hCL⟩
  refine ⟨C, ?_, hCL⟩
  -- C ∈ CA_rt means C ∈ CA ∧ ∀ n, C.t n = n - 1
  -- Need C ∈ CA_lt, i.e., C ∈ CA ∧ ∃ c, ∀ n, C.t n = c * (n - 1)
  -- CA_rt = t_rt (CA α), CA_lt = t_lt (CA α)
  have hCA : C ∈ CA α := hC.1
  have hT : ∀ n, C.t n = n - 1 := hC.2
  show C ∈ t_lt α (CA α)
  exact ⟨hCA, 1, by simpa using hT⟩

/-! ## Main theorem: ℒ(CA_rt) = ℒ_rev(CA_rt) ⟹ ℒ(CA_2n) ⊆ ℒ(CA_rt)

The hypothesis is universally quantified over all alphabet types:
  ∀ γ [Alphabet γ], ∀ M ∈ ℒ(CA_rt γ), M^R ∈ ℒ(CA_rt γ)

This allows instantiating with γ = Option β to get reversal closure on the
lifted alphabet, which avoids the problem of the padding symbol appearing in words.
-/

/-- If ℒ(CA_rt) is closed under reversal for all alphabets,
    then ℒ(CA_2n β) ⊆ ℒ(CA_rt β).

**Proof.** Lift L from β to Option β, pad with none^m,
apply reversal closure twice (over Option β) and lx_rt_implies_rt,
then project back.
1. (Language.lift L) ∈ ℒ(CA_2n (Option β)) by lift.
2. rev(L_none(((Language.lift L))^R))  ∈ ℒ(CA_rt (Option β)) — padding lemma.
3. L_none(((Language.lift L))^R) ∈ ℒ(CA_rt (Option β)) — reversal closure (Option β).
4. ((Language.lift L))^R ∈ ℒ(CA_rt (Option β)) — lx_rt_implies_rt with x = none.
5. (Language.lift L) ∈ ℒ(CA_rt (Option β)) — reversal closure (Option β).
6. L ∈ ℒ(CA_rt β) — project back. -/
theorem rt_rev_closed_implies_ca_2n_subset_ca_rt (β : Type) [Alphabet β]
    (h_rev_closure : ∀ (γ : Type) [Alphabet γ], ∀ M ∈ ℒ (CA_rt γ), Language.rev M ∈ ℒ (CA_rt γ)) :
    ℒ (CA_2n β) ⊆ ℒ (CA_rt β) := by
  intro L hL_2n

  -- Step 1: lift to Option β
  have hL_2n_opt : (Language.lift L) ∈ ℒ (CA_2n (Option β)) := lift_mem_ca_2n L hL_2n

  -- Step 2: rev(L_none(((Language.lift L))^R)) ∈ ℒ(CA_rt (Option β))
  have h2 : Language.rev (L_x none (Language.rev (Language.lift L))) ∈ ℒ (CA_rt (Option β)) :=
    lx_none_rev_rev_in_ca_rt L hL_2n

  -- Step 3: L_none(((Language.lift L))^R) ∈ ℒ(CA_rt (Option β)) by reversal closure
  have h3 : L_x none (Language.rev (Language.lift L)) ∈ ℒ (CA_rt (Option β)) := by
    rw [← Language.rev_rev (L_x _ (Language.rev (Language.lift L)))]
    exact h_rev_closure (Option β) _ h2

  -- Step 4: ((Language.lift L))^R ∈ ℒ(CA_rt (Option β)) by lx_rt_implies_rt
  have h4 : Language.rev (Language.lift L) ∈ ℒ (CA_rt (Option β)) :=
    lx_rt_implies_rt none (Language.rev (Language.lift L)) h3

  -- Step 5: (Language.lift L) ∈ ℒ(CA_rt (Option β)) by reversal closure
  have h5 : (Language.lift L) ∈ ℒ (CA_rt (Option β)) := by
    rw [← Language.rev_rev (Language.lift L)]
    exact h_rev_closure (Option β) _ h4

  -- Step 6: L ∈ ℒ(CA_rt β) by projection
  show L ∈ ℒ (CA_rt β)
  exact unlift_mem_ca_rt L h5

/-- If ℒ(CA_rt) is closed under reversal for all alphabets,
    then ℒ(CA_lt β) = ℒ(CA_rt β).

Combines `ca_linear_time_eq_2n` (Fischer speedup) with `rt_rev_closed_implies_ca_2n_subset_ca_rt`. -/
theorem rt_closed_under_rev_implies_lt_eq_rt' (β : Type) [Alphabet β]
    (h_rev_closure : ∀ (γ : Type) [Alphabet γ], ∀ M ∈ ℒ (CA_rt γ), Language.rev M ∈ ℒ (CA_rt γ)) :
    ℒ (CA_lt β) = ℒ (CA_rt β) := by
  ext L
  constructor
  · -- LT ⊆ RT: L ∈ CA_lt → L ∈ CA_2n (by speedup) → L ∈ CA_rt
    intro hL_lt
    have hL_2n : L ∈ ℒ (CA_2n β) := (ca_linear_time_eq_2n (α := β)) ▸ hL_lt
    exact rt_rev_closed_implies_ca_2n_subset_ca_rt β h_rev_closure hL_2n
  · -- RT ⊆ LT
    intro hL_rt
    exact ca_rt_subset_ca_lt (α := β) hL_rt

end CellularAutomatas
