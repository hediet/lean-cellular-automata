import CellularAutomatas.lt_closed
import CellularAutomatas.proofs.lx_rt_implies_rt

/-!
# ℒ(CA_rt) = ℒ_rev(CA_rt) ⟹ ℒ(CA_lt) = ℒ(CA_rt)

## Proof by double reversal

Given L ∈ ℒ(CA_lt), we show L ∈ ℒ(CA_rt) using reversal closure.

1. **Lift** L from Language β to Language (Option β) via `w ↦ w.map some`.
2. **Speedup**: lifted L ∈ ℒ(CA_2n (Option β)) by `ca_linear_time_eq_2n` + `map_embed`.
3. **Pad**: L_none(lifted(L)^R)^R ∈ ℒ(CA_rt (Option β)).
   Since `none` never appears in `w.map some`, the padding acts as pure border.
4. **First reversal**: L_none(lifted(L)^R) ∈ ℒ(CA_rt (Option β)) by reversal closure.
5. **Remove padding**: lifted(L)^R ∈ ℒ(CA_rt (Option β)) by `lx_rt_implies_rt`.
6. **Second reversal**: lifted(L) ∈ ℒ(CA_rt (Option β)) by reversal closure.
7. **Project back**: L ∈ ℒ(CA_rt β) via `map_embed`.
-/

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

/-! ## Speedup: ℒ(CA_lt) = ℒ(CA_2n) -/

/-- Linear-time CAs can be sped up to time 2n.
    Fischer's speedup theorem. -/
theorem ca_linear_time_eq_2n : ℒ (CA_lt α) = ℒ (CA_2n α) := by
  sorry

/-! ## Language lifting -/

/-- Lift a language from α to Option α: { w.map some | w ∈ L }. -/
def Language.lift (L : Language α) : Language (Option α) :=
  { w | ∃ v ∈ L, w = v.map some }

/-- Lifting preserves membership. -/
lemma Language.mem_lift_iff (L : Language α) (w : Word (Option α)) :
    w ∈ (Language.lift L) ↔ ∃ v ∈ L, w = v.map some := Iff.rfl

/-- Lift a tCellAutomaton from α to Option α.
Product of:
- **Q-track**: simulates C, mapping `none` inputs to border (`C.embed none`).
- **Valid-track** (Bool): checks all input symbols are `some _`.
  Propagates right-to-left: `δ_valid(l, c, r) = c && r`.
  After n−1 steps at position 0, valid = ∧ᵢ (w[i] is some). -/
private def liftCA (C : tCellAutomaton α) : tCellAutomaton (Option α) where
  Q := C.Q × Bool
  δ l c r := (C.δ l.1 c.1 r.1, c.2 && r.2)
  embed x := match x with
    | none => (C.embed none, true)
    | some none => (C.embed none, false)
    | some (some a) => (C.embed (some a), true)
  project qv := C.project qv.1 && qv.2
  t := C.t
  p := C.p

/-- Helper: The Q-component of liftCA state equals C's state when inputs match.

At any time t and position p, if the input is `w.map some`, the Q-track of liftCA
evolves identically to C on `w`. -/
private lemma liftCA_Q_component (C : tCellAutomaton α) (w : Word α) (t : ℕ) (p : ℤ) :
    ((liftCA C).toCellAutomaton.nextt ⦋w.map some⦌ t p).1 =
    C.toCellAutomaton.nextt ⦋w⦌ t p := by
  -- The Q-track of liftCA has δ_Q(l, c, r) = C.δ l.1 c.1 r.1
  -- The embed function maps some (some a) → (C.embed (some a), _)
  -- So the Q-track evolves identically to C
  sorry

/-- Helper: For w = v.map some, the Bool component at position 0 at time t is true
    (as long as t < v.length, the Bool track sees only `some (some _)` inputs). -/
private lemma liftCA_Bool_true_for_map_some (C : tCellAutomaton α) (v : Word α) (t : ℕ) :
    ((liftCA C).toCellAutomaton.nextt ⦋v.map some⦌ t 0).2 = true := by
  -- The Bool track starts as `true` at all positions with `some (some _)` and at borders
  -- δ_bool(l, c, r) = c && r propagates right-to-left
  -- Since all initial Bools (at positions 0..n-1 with `some (some _)`) are true,
  -- the conjunction is always true
  sorry

/-- Helper: If w contains `none` at some position i (where i ≤ t),
    then the Bool component at position 0 at time t is false. -/
private lemma liftCA_Bool_false_for_none (C : tCellAutomaton α) (w : Word (Option α))
    (i : ℕ) (hi : i < w.length) (hn : w[i] = none) (ht : i ≤ t) :
    ((liftCA C).toCellAutomaton.nextt ⦋w⦌ t 0).2 = false := by
  -- The Bool at position i starts as `false` (since w[i] = none maps to (_, false))
  -- The Bool propagates right-to-left: δ_bool(l, c, r) = c && r
  -- After i steps, position 0 sees the `false` from position i
  -- Since i ≤ t, position 0's Bool at time t includes this `false`
  sorry

/-- liftCA C has the same language as Language.lift C.L.
The Q-track reproduces C's computation on the underlying word,
and the valid-track ensures only words of the form v.map some are accepted.

**Proof sketch:**
- **Forward:** If `(liftCA C).accepts w = true`, then the Bool component at position 0
  at time `t(n)` is true. This means all symbols `w[i]` for `i ≤ t(n)` are `some _`.
  So `w = v.map some` for some `v`. The Q-track simulates C on `v`, so `C.accepts v = true`.
- **Backward:** If `w = v.map some` for `v ∈ C.L`, the Bool track stays true (all inputs
  are `some (some _)`), and the Q-track computes C on `v`. So `(liftCA C).accepts w = true`. -/
private lemma liftCA_L_eq_lift (C : tCellAutomaton α) :
    (liftCA C).L = Language.lift C.L := by
  ext w
  simp only [tCellAutomaton.L, Language.lift, Set.mem_setOf_eq]
  constructor
  · -- (liftCA C).accepts w → ∃ v ∈ C.L, w = v.map some
    intro hw
    -- If w contains `none` at position i ≤ t(n), the Bool becomes false
    -- But hw implies Bool is true, so w = v.map some for some v
    -- Then v ∈ C.L because the Q-track simulates C
    sorry
  · -- ∃ v ∈ C.L, w = v.map some → (liftCA C).accepts w
    rintro ⟨v, hv, rfl⟩
    -- hv : v ∈ C.L means C.accepts v = true
    -- The Bool track stays true (all symbols are some (some _))
    -- The Q-track computes exactly as C on v
    -- So (liftCA C).accepts (v.map some) = C.accepts v && true = C.accepts v = true
    -- Technical details: use liftCA_Q_component and liftCA_Bool_true_for_map_some
    sorry

/-- If L ∈ ℒ(CA_rt β), then (Language.lift L) ∈ ℒ(CA_rt (Option β)). -/
lemma lift_mem_ca_rt (L : Language α) (hL : L ∈ ℒ (CA_rt α)) :
    (Language.lift L) ∈ ℒ (CA_rt (Option α)) := by
  obtain ⟨C, hC, hCL⟩ := hL
  refine ⟨liftCA C, ⟨⟨trivial, hC.1.2⟩, hC.2⟩, ?_⟩
  subst hCL; exact (liftCA_L_eq_lift C).symm

/-- If (Language.lift L) ∈ ℒ(CA_rt (Option β)), then L ∈ ℒ(CA_rt β).

Uses map_embed with f = some: (C.map_embed some).L = { w | w.map some ∈ C.L }.
Since C.L = lift(L) = { v.map some | v ∈ L }, membership reduces to
w.map some = v.map some for some v ∈ L, which by injectivity of some gives w = v. -/
lemma unlift_mem_ca_rt (L : Language α) (hL : (Language.lift L) ∈ ℒ (CA_rt (Option α))) :
    L ∈ ℒ (CA_rt α) := by
  obtain ⟨C, hC, hCL⟩ := hL
  refine ⟨C.map_embed some, c_map_embed_in_ca_rt_iff_c_in_ca_rt C some |>.mpr hC, ?_⟩
  ext w
  show w ∈ L ↔ w ∈ (C.map_embed some).L
  rw [map_embed_L]
  -- Goal: w ∈ L ↔ w.map some ∈ C.L
  -- hCL : Language.lift L = C.L (modulo DefinesLanguage)
  have : w.map some ∈ C.L ↔ w.map some ∈ Language.lift L := by
    constructor <;> intro h
    · rw [hCL]; exact h
    · rw [hCL] at h; exact h
  rw [this]
  simp only [Language.lift]
  constructor
  · intro hw; exact ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, heq⟩
    exact List.map_injective_iff.mpr (Option.some_injective α) heq ▸ hv

/-- If L ∈ ℒ(CA_2n β), then (Language.lift L) ∈ ℒ(CA_2n (Option β)). -/
lemma lift_mem_ca_2n (L : Language α) (hL : L ∈ ℒ (CA_2n α)) :
    (Language.lift L) ∈ ℒ (CA_2n (Option α)) := by
  obtain ⟨C, hC, hCL⟩ := hL
  refine ⟨liftCA C, ⟨⟨trivial, hC.1.2⟩, hC.2⟩, ?_⟩
  subst hCL; exact (liftCA_L_eq_lift C).symm

/-- Lifting commutes with reversal: lift(L^R) = (lift L)^R -/
lemma Language.lift_rev (L : Language α) :
    Language.lift (Language.rev L) = Language.rev (Language.lift L) := by
  ext w
  simp only [Language.lift, Language.rev]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.reverse, hv, by simp [List.map_reverse]⟩
  · rintro ⟨v, hv, hrev⟩
    refine ⟨v.reverse, ?_, ?_⟩
    · show v.reverse.reverse ∈ L; simp [hv]
    · have : w = w.reverse.reverse := by simp
      rw [this, hrev]; simp [List.map_reverse]

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

/-! ## Main theorem: (B) ⟹ (A)

The hypothesis is universally quantified over all alphabet types:
  ∀ γ [Alphabet γ], ∀ M ∈ ℒ(CA_rt γ), M^R ∈ ℒ(CA_rt γ)

This allows instantiating with γ = Option β to get reversal closure on the
lifted alphabet, which avoids the problem of the padding symbol appearing in words.
-/

/-- If ℒ(CA_rt) is closed under reversal for all alphabets,
    then ℒ(CA_lt β) = ℒ(CA_rt β).

**Proof.** For LT ⊆ RT, lift L from β to Option β, pad with none^m,
apply reversal closure twice (over Option β) and lx_rt_implies_rt,
then project back.
1. (Language.lift L) ∈ ℒ(CA_2n (Option β)) by speedup + lift.
2. rev(L_none(((Language.lift L))^R))  ∈ ℒ(CA_rt (Option β)) — padding lemma.
3. L_none(((Language.lift L))^R) ∈ ℒ(CA_rt (Option β)) — reversal closure (Option β).
4. ((Language.lift L))^R ∈ ℒ(CA_rt (Option β)) — lx_rt_implies_rt with x = none.
5. (Language.lift L) ∈ ℒ(CA_rt (Option β)) — reversal closure (Option β).
6. L ∈ ℒ(CA_rt β) — project back. -/
theorem rt_closed_under_rev_implies_lt_eq_rt' (β : Type) [Alphabet β]
    (h_rev_closure : ∀ (γ : Type) [Alphabet γ], ∀ M ∈ ℒ (CA_rt γ), Language.rev M ∈ ℒ (CA_rt γ)) :
    ℒ (CA_lt β) = ℒ (CA_rt β) := by
  ext L
  constructor
  · -- LT ⊆ RT
    intro hL_lt
    -- Step 1: L ∈ ℒ(CA_2n) by speedup, then lift to Option β
    have hL_2n : L ∈ ℒ (CA_2n β) := (ca_linear_time_eq_2n (α := β)) ▸ hL_lt
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

  · -- RT ⊆ LT
    intro hL_rt
    exact ca_rt_subset_ca_lt (α := β) hL_rt

end CellularAutomatas
