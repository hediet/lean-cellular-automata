import CellularAutomatas.lt_closed
import CellularAutomatas.proofs.lx_rt_implies_rt
import CellularAutomatas.proofs.lift_language
import CellularAutomatas.proofs.ca_rt_rev_eq_car_rt
import CellularAutomatas.proofs.car_rt_subset_ca_2n
import CellularAutomatas.proofs.time_constructible_latched_ca

/-!
# Theorem: ℒ(CA_rt) = ℒ(CA_2n) ⟺ ℒ(CA_rt) = ℒᴿ(CA_rt)

This file proves the equivalence between:
- (A) ℒ(CA_rt) = ℒ(CA_2n)
- (B) ℒ(CA_rt) = ℒᴿ(CA_rt)   (RT is closed under language reversal)

## Standing facts:
- ℒ_rev(CA_rt) = ℒ(CAr_rt)  — mirror δ and the word to switch reading position
- ℒ(CAr_rt) ⊆ ℒ(CA_2n)      — shift answer from position n-1 to 0 in n-1 steps
- ℒ(CA_rt) ⊆ ℒ(CA_2n)       — standard time extension

## Key lemma:
- `Lx(Lᴿ)ᴿ ∈ ℒ(CA_rt) ⟹ L ∈ ℒ(CA_rt)` — proved in `lx_rt_implies_rt`

## Direction (⇒): ℒ(CA_rt) = ℒ(CA_2n) implies RT closed under reversal

Take L ∈ ℒ(CA_rt). Then Lᴿ ∈ ℒ_rev(CA_rt) = ℒ(CAr_rt) ⊆ ℒ(CA_2n) = ℒ(CA_rt).
So Lᴿ ∈ ℒ(CA_rt), giving ℒᴿ(CA_rt) ⊆ ℒ(CA_rt). The reverse inclusion gives equality.

## Direction (⇐): RT closed under reversal implies ℒ(CA_rt) = ℒ(CA_2n)

We already have ℒ(CA_rt) ⊆ ℒ(CA_2n). For the other inclusion, take L ∈ ℒ(CA_2n).
1. L ∈ ℒ(CA_2n), so Lᴿ ∈ ℒ(CA_2n), so Lx(Lᴿ) ∈ ℒ(CA_rt) — prefix padding converts 2n to RT.
2. By closure under reversal: Lx(Lᴿ)ᴿ ∈ ℒ(CA_rt) — this is { w · x^padding : w ∈ L }, suffix-padded.
3. By the key lemma: L ∈ ℒ(CA_rt).

So ℒ(CA_2n) ⊆ ℒ(CA_rt). ∎
-/

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

/-! ## Section 1: Standing Facts

These are the base lemmas that form the foundation of the equivalence.
-/

/-- Right-reading CA classes (read at position n-1 instead of 0). -/
-- CAr_rt is imported from ca_rt_rev_eq_car_rt
abbrev CAr_2n (α : Type) [Alphabet α] := CAr α |> t_2n α

/-- ℒ(CA_rt) ⊆ ℒ(CA_2n): Real-time languages are contained in 2n-time languages.

**Proof**: Given C ∈ CA_rt (reads at time n-1, position 0), build a CA that:
1. Runs C with `latchedCA_k` using `identityTimeConstructible` (t(n) = n) and k = 1.
2. `latchedCA_k_spec` gives: at time n + t', output = C.comp at time n - 1.
3. Setting t' = n - 2 gives time 2*(n-1), output = C.comp at time n - 1. -/
theorem ca_rt_subset_ca_2n : ℒ (CA_rt α) ⊆ ℒ (CA_2n α) := by
  intro L ⟨C, hC_mem, hL_eq⟩
  -- Extract membership data from CA_rt
  have hC_CA : C ∈ CA α := by
    simp only [CA_rt, t_rt] at hC_mem; exact hC_mem.1
  have hC_t : ∀ n, C.t n = n - 1 := by
    simp only [CA_rt, t_rt] at hC_mem; exact hC_mem.2
  have hC_p : C.p = fun _ => 0 := by
    simp only [CA, tCellAutomata, Set.mem_univ, true_and] at hC_CA; exact hC_CA
  -- Build C' using latchedCA_k with t = id, k = 1
  refine ⟨{
    toCellAutomaton := latchedCA_k C.toCellAutomaton id identityTimeConstructible 1
    t := fun n => 2 * (n - 1)
    p := fun _ => 0
  }, ?_, ?_⟩
  · -- C' ∈ CA_2n α
    show _ ∈ CA_2n α
    simp only [CA_2n, t_2n, CA, tCellAutomata, Set.mem_univ, true_and]
    exact ⟨rfl, fun _ => rfl⟩
  · -- L = C'.L
    rw [hL_eq]
    ext w
    show C.accepts w = true ↔
      (latchedCA_k C.toCellAutomaton id identityTimeConstructible 1).comp
        ⦋⟬w⟭⦌ (2 * (w.length - 1)) 0 = true
    simp only [tCellAutomaton.accepts]
    rw [hC_t, congr_fun hC_p]
    -- latchedCA_k_spec: at time id(n) + t', output = C.comp at time n - 1
    -- We need 2*(n-1) = n + t' for some t', i.e., t' = n - 2
    -- This works for n ≥ 2; for n ≤ 1 both sides are time 0.
    by_cases hn : w.length ≥ 2
    · -- n ≥ 2: use latchedCA_k_spec with t' = n - 2
      have key := latchedCA_k_spec C.toCellAutomaton id identityTimeConstructible 1 w
                    (w.length - 2)
      simp only [id_eq] at key
      have h_time : w.length + (w.length - 2) = 2 * (w.length - 1) := by omega
      rw [h_time] at key
      rw [key]
    · -- n ≤ 1: both 2*(n-1) = 0 and n-1 = 0, so both sides are C.comp at time 0
      push_neg at hn
      have h_eq : 2 * (w.length - 1) = 0 := by omega
      have h_eq' : w.length - 1 = 0 := by omega
      rw [h_eq, h_eq']
      -- At time 0, both sides reduce to C.project (C.embed (word_to_config w 0)).
      -- latchedCA_k at time 0: nextt gives embed_config, latched = none,
      -- so project falls through to TraceKx → C.project of initial state.
      simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp,
                 CellAutomaton.nextt_zero]
      -- latchedCA_k = map_project of latchedCA of TraceKx.C
      unfold latchedCA_k CellAutomaton.map_project CellAutomaton.embed_config
      simp only [Function.comp, latchedCA, TraceKx.C]
      -- latched = none at time 0, so getD falls through
      simp only [Option.getD_none, Option.getD_some]

/-- ℒᴿ(CA_rt) ⊆ ℒ(CA_2n): Reversals of RT languages are contained in 2n-time languages.

**Proof**: Compose `ca_rt_rev_eq_car_rt` with `car_rt_subset_ca_2n`. -/
theorem ca_rt_rev_subset_ca_2n : ℒ_rev (CA_rt α) ⊆ ℒ (CA_2n α) := by
  calc ℒ_rev (CA_rt α) = ℒ (CAr_rt α) := ca_rt_rev_eq_car_rt
    _ ⊆ ℒ (CA_2n α) := car_rt_subset_ca_2n

/-! ## Section 2: Direction (⇒): ℒ(CA_rt) = ℒ(CA_2n) ⟹ ℒ(CA_rt) = ℒᴿ(CA_rt) -/

/-- Main direction (⇒): If ℒ(CA_rt) = ℒ(CA_2n), then ℒ(CA_rt) is closed under reversal.

**Proof**:
1. Take L ∈ ℒ(CA_rt).
2. Then Lᴿ ∈ ℒᴿ(CA_rt).
3. By `ca_rt_rev_subset_ca_2n`: Lᴿ ∈ ℒ(CA_2n).
4. By hypothesis: Lᴿ ∈ ℒ(CA_rt).
5. So ℒᴿ(CA_rt) ⊆ ℒ(CA_rt).
6. The reverse inclusion follows similarly, giving equality. -/
theorem rt_eq_2n_implies_rt_eq_rt_rev
    (h : ℒ (CA_rt α) = ℒ (CA_2n α)) :
    ℒ (CA_rt α) = ℒ_rev (CA_rt α) := by
  -- We prove both inclusions
  ext L
  simp only [ℒ_rev, LanguageClass.rev, Set.mem_image]
  constructor
  · -- L ∈ ℒ(CA_rt) → ∃ M ∈ ℒ(CA_rt), L = M^R
    intro hL
    -- Take M = L^R
    use Language.rev L
    constructor
    · -- L^R ∈ ℒ(CA_rt)
      -- L^R ∈ ℒ^R(CA_rt) ⊆ ℒ(CA_2n) = ℒ(CA_rt)
      have h1 : Language.rev L ∈ ℒ_rev (CA_rt α) := by
        simp only [ℒ_rev, LanguageClass.rev, Set.mem_image]
        exact ⟨L, hL, rfl⟩
      have h2 : Language.rev L ∈ ℒ (CA_2n α) := ca_rt_rev_subset_ca_2n h1
      exact h.symm ▸ h2
    · -- L = (L^R)^R
      exact Language.rev_rev L
  · -- ∃ M ∈ ℒ(CA_rt), L = M^R → L ∈ ℒ(CA_rt)
    intro ⟨M, hM, hL_eq⟩
    subst hL_eq
    -- M^R ∈ ℒ^R(CA_rt) ⊆ ℒ(CA_2n) = ℒ(CA_rt)
    have h1 : Language.rev M ∈ ℒ_rev (CA_rt α) := by
      simp only [ℒ_rev, LanguageClass.rev, Set.mem_image]
      exact ⟨M, hM, rfl⟩
    have h2 : Language.rev M ∈ ℒ (CA_2n α) := ca_rt_rev_subset_ca_2n h1
    exact h.symm ▸ h2

/-! ## Section 3: Direction (⇐): ℒ(CA_rt) = ℒᴿ(CA_rt) ⟹ ℒ(CA_rt) = ℒ(CA_2n)

The hard direction. Uses lifting to Option α to get a fresh padding symbol.
-/

/-! ### padCA: mapping padding to border via Option.join -/

/-- Extend a CellAutomaton α？ to (Option α)？ by collapsing `none` to border.
    Uses `Option.join : (Option α)？ → α？` as embedding map.
    For input `w.map(some) ++ none^m`:
    - `some(some a)` → `C.embed(some a)` (real symbol)
    - `some(none)` → `C.embed(none)` (padding = border)
    - `none` → `C.embed(none)` (outer border)
    So the embedded configuration matches C's config on ⟬w⟭. -/
def padLCA (C : CellAutomaton α？ β) : CellAutomaton (Option α)？ β :=
  C.map_embed Option.join

/-- Key config identity: for `u = w.map(some) ++ none^m`, the padLCA config
    equals C's config on w. Both map positions 0..n-1 to `C.embed(some w[i])`
    and all others to `C.embed(none)`. -/
lemma padLCA_embed_config_eq (C : CellAutomaton α？ β) (w : Word α) (m : ℕ) :
    (padLCA C).embed_config (word_to_config (w.map some ++ List.replicate m none))
    = C.embed_config (word_to_config w) := by
  funext p
  simp only [CellAutomaton.embed_config, padLCA, CellAutomaton.map_embed, Function.comp]
  congr 1
  simp only [word_to_config]
  split_ifs with h1 h2 h2
  · -- Both in range
    have hp_toNat_lt : p.toNat < (w.map some).length := by simp; omega
    have : (w.map some ++ List.replicate m none)[p.toNat] = some w[p.toNat] := by
      rw [List.getElem_append_left hp_toNat_lt]
      simp [List.getElem_map]
    simp [this]
  · -- In padded word but not in w → in the none-padding
    simp only [List.length_append, List.length_map, List.length_replicate] at h1
    push_neg at h2
    have hp_ge_w : (w.map some).length ≤ p.toNat := by
      simp only [List.length_map]; have := h2 h1.1; omega
    have : (w.map some ++ List.replicate m none)[p.toNat] = none := by
      rw [List.getElem_append_right hp_ge_w]; simp
    simp [this]
  · -- Not in padded word but in w → impossible
    simp only [List.length_append, List.length_map, List.length_replicate] at h1
    push_neg at h1; omega
  · -- Both out of range
    rfl

/-- Computation identity: padLCA computes identically to C on effective word w. -/
lemma padLCA_comp_eq (C : CellAutomaton α？ β) (w : Word α) (m : ℕ)
    (t : ℕ) (p : ℤ) :
    (padLCA C).comp ⦋(w.map some ++ List.replicate m none : Word (Option α))⦌ t p =
    C.comp ⦋w⦌ t p := by
  simp only [CellAutomaton.comp, Function.comp, CellAutomaton.project_config,
             padLCA, CellAutomaton.map_embed_nextt]
  congr 1
  exact congrFun (congrArg _ (padLCA_embed_config_eq C w m)) p

/-- Suffix-padded lifted language: Lrev_x(L) = { w.map some ++ none^k | w ∈ L, k ≥ |w| }.
    This is the "dual" of L_x (prefix-padded) — padding comes after the word.
    The padding length is relaxed: any k ≥ |w| is valid.
    The split is unique since none and some _ are disjoint. -/
def Lrev_x {α : Type} (L : Language α) : Language (Option α) :=
  { u | ∃ (w : Word α) (k : ℕ), w ∈ L ∧ k ≥ w.length ∧
        u = w.map some ++ List.replicate k none }

/-! ### Helper lemmas for the construction -/

/-- CA_rt is closed under intersection.
    Proof: product CA with `&&` on outputs. -/
private lemma ca_rt_inter_two {β : Type} [Alphabet β] (L₁ L₂ : Language β)
    (h₁ : L₁ ∈ ℒ (CA_rt β)) (h₂ : L₂ ∈ ℒ (CA_rt β)) :
    (L₁ ∩ L₂ : Set (Word β)) ∈ ℒ (CA_rt β) := by
  rw [ℒ_CA_rt_iff] at h₁ h₂ ⊢
  obtain ⟨C₁, hC₁_rt, hC₁_L⟩ := h₁
  obtain ⟨C₂, hC₂_rt, hC₂_L⟩ := h₂
  let C' := toRtCa ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && b))
  refine ⟨C'.val, C'.property, ?_⟩
  ext w
  rw [Set.mem_inter_iff, ← hC₁_L, ← hC₂_L]
  rw [CA_rt_L_iff (C := C'), CA_rt_L_iff2 hC₁_rt, CA_rt_L_iff2 hC₂_rt]
  change ((C₁.toCellAutomaton ⨂ C₂.toCellAutomaton).map_project (fun (a, b) => a && b)).comp ⦋w⦌ (w.length - 1) 0 = true
    ↔ C₁.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true ∧ C₂.toCellAutomaton.comp ⦋w⦌ (w.length - 1) 0 = true
  simp only [comp_of_map_project, ca_zip_comp, Bool.and_eq_true]

/-- Monotone format: words of the form `some^* ++ none^*` over Option α. -/
def MonotoneFormat (α : Type) : Language (Option α) :=
  { u | ∃ (w : Word α) (k : ℕ), u = w.map some ++ List.replicate k none }

/-- Padded format: monotone-format words with at least as many nones as somes.
    This is `some^n ++ none^k` where `k ≥ n`. -/
def PaddedFormat (α : Type) : Language (Option α) :=
  { u | ∃ (w : Word α) (k : ℕ), k ≥ w.length ∧ u = w.map some ++ List.replicate k none }

/-- Padded bool format: true^i ++ false^j where j ≥ i.
    This is the "erased" version of PaddedFormat that ignores the actual values. -/
def PaddedBoolFormat : Language Bool :=
  { u | ∃ i j : ℕ, j ≥ i ∧ u = List.replicate i true ++ List.replicate j false }

/-- **Axiom**: The padded bool format language `true^i false^j` with `j ≥ i` is in CA_rt.

    **Construction sketch**: Intersect two CA_rt languages:
    1. `true* false*` (monotone, 3-state DFA)
    2. `{ w | #false ≥ #true }`: A signal from position 0 travels right at speed 1.
       At RT time n-1, it's at position n-1. The boundary (first false) is at position i.
       A signal from the boundary travels left. They meet iff i ≤ (n-1)/2, i.e., j ≥ i. -/
axiom padded_bool_format_in_ca_rt : PaddedBoolFormat ∈ ℒ (CA_rt Bool)

omit [Alphabet α] in
/-- PaddedFormat α is the preimage of PaddedBoolFormat under Option.isSome. -/
lemma paddedFormat_eq_preimage :
    PaddedFormat α = { w | w.map Option.isSome ∈ PaddedBoolFormat } := by
  ext u
  simp only [PaddedFormat, PaddedBoolFormat]
  constructor
  · -- PaddedFormat → preimage: straightforward map computation
    intro ⟨w, k, hk, hu⟩
    refine ⟨w.length, k, hk, ?_⟩
    subst hu
    have : (Option.isSome ∘ @some α) = fun _ => true := funext (fun _ => rfl)
    simp [List.map_append, List.map_map, List.map_replicate, this]
  · -- preimage → PaddedFormat: extract values from true^i ++ false^j
    intro ⟨i, j, hj, hu_map⟩
    have h_len : u.length = i + j := by simpa using congrArg List.length hu_map
    -- Element-wise: u[p].isSome matches (true^i ++ false^j)[p]
    have h_elem (p : ℕ) (hp : p < i + j) :
        (u[p]'(by omega)).isSome =
        (List.replicate i true ++ List.replicate j false)[p]'(by simp; omega) := by
      have : (u.map Option.isSome)[p]'(by simp; omega) =
          (List.replicate i true ++ List.replicate j false)[p]'(by simp; omega) := by congr 1
      simpa using this
    -- First i elements are some _
    have h_some (p : ℕ) (hp : p < i) : (u[p]'(by omega)).isSome = true := by
      rw [h_elem p (by omega),
          List.getElem_append_left (show p < (List.replicate i true).length by simp; omega)]
      simp
    -- Remaining j elements are none
    have h_none (p : ℕ) (hp1 : i ≤ p) (hp2 : p < i + j) : u[p]'(by omega) = none := by
      have h1 := h_elem p hp2
      rw [List.getElem_append_right (show (List.replicate i true).length ≤ p by simp; omega)] at h1
      simp at h1
      cases hx : u[p] <;> simp_all
    -- Build w by extracting values from the first i elements
    let w : Word α := List.ofFn fun (k : Fin i) =>
      (u[k.val]'(by omega)).get (h_some k.val k.isLt)
    exact ⟨w, j, by simp [w]; exact hj, List.ext_getElem (by simp [w, h_len]) fun p hp1 hp2 => by
      simp only [List.length_append, List.length_map, List.length_replicate, w,
                  List.length_ofFn] at hp2
      by_cases hp : p < i
      · -- p in the some-part: (w.map some)[p] = some (u[p].get _) = u[p]
        rw [List.getElem_append_left (by simp [w]; omega)]
        rw [List.getElem_map, List.getElem_ofFn]
        exact (Option.some_get _).symm
      · -- p in the none-part: none^j[p-i] = none = u[p]
        push_neg at hp
        rw [List.getElem_append_right (by simp [w]; omega), List.getElem_replicate]
        simp [(h_none p hp (by omega)).symm]
        ⟩

/-- The padded format language is in CA_rt.

    Uses the preimage characterization and lifts from CA_rt Bool via map_embed. -/
lemma padded_format_in_ca_rt : PaddedFormat α ∈ ℒ (CA_rt (Option α)) := by
  rw [paddedFormat_eq_preimage]
  obtain ⟨C, hC_rt, hC_L⟩ := padded_bool_format_in_ca_rt
  let C' : tCellAutomaton (Option α) := C.map_embed Option.isSome
  refine ⟨C', ?_, ?_⟩
  · rw [c_map_embed_in_ca_rt_iff_c_in_ca_rt]
    exact hC_rt
  · ext w
    show w.map Option.isSome ∈ PaddedBoolFormat ↔ w ∈ (C.map_embed Option.isSome).L
    simp only [map_embed_L, hC_L]
    rfl

/-- A variant of `latchedCA` that outputs a default value `d` before the latch fires,
    instead of the current CA output. This ensures no false positives before the timer.
    Shares Q/δ/embed with `latchedCA`, so state evolution (`nextt`) is identical. -/
def latchedCA_strict {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t) (d : β)
    : CellAutomaton α？ β where
  Q := LatchedState C.Q tc.timer.Q β
  δ := fun left mid right =>
    let ca_next := C.δ left.ca_state mid.ca_state right.ca_state
    let timer_next := tc.timer.δ left.timer_state mid.timer_state right.timer_state
    let timer_signal := tc.timer.project timer_next
    let new_latched :=
      if mid.latched.isSome then mid.latched
      else if timer_signal then some (C.project ca_next)
      else none
    ⟨ca_next, timer_next, new_latched⟩
  embed := fun a =>
    let ca_emb := C.embed a
    let timer_emb := tc.timer.embed (a.map fun _ => ())
    ⟨ca_emb, timer_emb, none⟩
  project := fun s => s.latched.getD d

/-- After the latch fires (at time ≥ t(n)), `latchedCA_strict` outputs the same
    value as the original CA at time t(n).
    Reuses `latch_triggered_at_t` and `latch_persists` from `latchedCA`. -/
theorem latchedCA_strict_correct {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t) (d : β)
    (w : Word α) (t' : ℕ) :
    (latchedCA_strict C t tc d).comp ⦋⟬w⟭⦌ (t w.length + t') 0 =
    C.comp ⦋⟬w⟭⦌ (t w.length) 0 := by
  -- latchedCA_strict shares Q/δ/embed with latchedCA, only project differs.
  change ((latchedCA C t tc).nextt
    (CellAutomaton.embed_config (word_to_config w)) (t w.length + t') 0).latched.getD d =
    C.project (C.nextt (CellAutomaton.embed_config (word_to_config w)) (t w.length) 0)
  have h_persist := LatchedCA.latch_persists C t tc w (t w.length) (t w.length + t') rfl (by omega)
  have h_trig := LatchedCA.latch_triggered_at_t C t tc w
  rw [h_persist, h_trig]
  simp

/-- Before the latch fires (at time < t(n)), `latchedCA_strict` outputs the default `d`.
    Reuses `latched_none_before_signal` from `latchedCA` — since `nextt` is the same
    (by `rfl`), the latched field is `none` before the timer fires. -/
theorem latchedCA_strict_before {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α？ β) (t : ℕ → ℕ) (tc : TimeConstructible t) (d : β)
    (w : Word α) (j : ℕ) (hj : j < t w.length) :
    (latchedCA_strict C t tc d).comp ⦋⟬w⟭⦌ j 0 = d := by
  -- latchedCA_strict shares Q/δ/embed with latchedCA, only project differs.
  -- comp = project ∘ nextt, so the goal reduces to latched.getD d for latchedCA's nextt.
  change ((latchedCA C t tc).nextt
    (CellAutomaton.embed_config (word_to_config w)) j 0).latched.getD d = d
  rw [LatchedCA.latched_none_before_signal C t tc w j hj]
  rfl

/-- For C ∈ CA_2n, padLCA(latchedCA_strict C (2*(n-1)) false) is a CA_rt that on
    padded-format words `w.map some ++ none^k` with `k ≥ |w|` accepts iff `w ∈ C.L`.

    **Construction**: `padLCA(latchedCA_strict C.toCellAutomaton (2*(n-1)) false)`:
    - `latchedCA_strict` latches at time `2*(n-1)`, outputs `false` before latch fires
    - `padLCA` maps none-padding to border (timer sees effective length n)

    At RT time `n + k - 1` with `k ≥ n`:
    - `n+k-1 ≥ 2*(n-1)`, so latch has fired → output = `C.accepts w`

    **Depends on**: `latchedCA_strict_correct`. -/
lemma exists_main_ca_for_Lrev_x (C : tCellAutomaton α) (hC : C ∈ CA_2n α) :
    ∃ D ∈ CA_rt (Option α), ∀ (w : Word α) (k : ℕ), k ≥ w.length →
      ((w.map some ++ List.replicate k none) ∈ D.L ↔ w ∈ C.L) := by
  have hC_t : ∀ n, C.t n = 2 * (n - 1) := hC.2
  have hC_p : C.p = fun _ => 0 := by
    have := hC.1; simp only [CA, tCellAutomata, Set.mem_univ, true_and] at this; exact this

  -- Build CA: padLCA(latchedCA_strict C 2*(n-1) false)
  let tc2 := linearTimeConstructible 2 (by omega)
  let D_inner := latchedCA_strict C.toCellAutomaton (fun n => 2 * (n - 1)) tc2 false
  let D := toRtCa (padLCA D_inner)

  -- Helper: padLCA collapses padding → D_inner sees effective word w
  have h_pad : ∀ (w : Word α) (k t : ℕ) (p : ℤ),
      (padLCA D_inner).comp ⦋(w.map some ++ List.replicate k none : Word (Option α))⦌ t p =
      D_inner.comp ⦋w⦌ t p :=
    fun w k t p => padLCA_comp_eq D_inner w k t p

  -- Helper: D membership unfolded for monotone-format words
  have h_D_mono : ∀ (w : Word α) (k : ℕ),
      (w.map some ++ List.replicate k none) ∈ D.val.L ↔
      D_inner.comp ⦋w⦌ (w.length + k - 1) 0 = true := by
    intro w k
    rw [CA_rt_L_iff (C := D)]
    simp only [List.length_append, List.length_map, List.length_replicate]
    constructor
    · intro h
      change (padLCA D_inner).comp _ _ _ = _ at h
      rwa [h_pad w k (w.length + k - 1) 0] at h
    · intro h
      change (padLCA D_inner).comp _ _ _ = _
      rwa [h_pad w k (w.length + k - 1) 0]

  -- Helper: latch-to-C connection (after latch fires at time 2*(n-1) + t')
  have h_latch_C : ∀ (w : Word α) (t' : ℕ),
      D_inner.comp ⦋⟬w⟭⦌ (2 * (w.length - 1) + t') 0 = true ↔ w ∈ C.L := by
    intro w t'
    rw [latchedCA_strict_correct]
    show C.toCellAutomaton.comp ⦋⟬w⟭⦌ (2 * (w.length - 1)) 0 = true ↔ w ∈ C.L
    rw [show (w ∈ C.L) ↔ (w ∈ tCellAutomaton.L C) from Iff.rfl,
        tCellAutomaton.elem_L_iff, hC_t, congr_fun hC_p]

  refine ⟨D.val, D.property, ?_⟩
  intro w k hk
  rw [h_D_mono]
  -- k ≥ |w|, so |w| + k - 1 ≥ 2*(|w|-1). Write as 2*(|w|-1) + remainder.
  by_cases hn : w.length = 0
  · rw [show w.length + k - 1 = 2 * (w.length - 1) + (w.length + k - 1) from by omega]
    exact h_latch_C w _
  · have h_eq : w.length + k - 1 = 2 * (w.length - 1) + (k - w.length + 1) := by omega
    rw [h_eq]
    exact h_latch_C w _

/-- If L ∈ ℒ(CA_2n α), then Lrev_x(L) ∈ ℒ(CA_rt (Option α)).

    **Proof**: Intersect two CA_rt languages:
    1. `D.L` from `exists_main_ca_for_Lrev_x` — on padded-format words (`k ≥ |w|`),
       accepts iff `w ∈ L`
    2. `PaddedFormat α` — restricts to `some^n none^k` with `k ≥ n`

    Their intersection is exactly `Lrev_x L`.

    Note: We need `PaddedFormat` (not just `MonotoneFormat`) because `latchedCA_strict`
    only guarantees `false` output strictly before latch time `2*(n-1)`. At the boundary
    `k = n-1`, RT time equals the latch time exactly, causing a false positive. -/
lemma ca_2n_padded_in_ca_rt (L : Language α) (hL : L ∈ ℒ (CA_2n α)) :
    Lrev_x L ∈ ℒ (CA_rt (Option α)) := by
  obtain ⟨C, hC_mem, hL_eq⟩ := hL
  subst hL_eq

  -- Get the two component CAs
  obtain ⟨D, hD_rt, hD_spec⟩ := exists_main_ca_for_Lrev_x C hC_mem
  have h_padded := padded_format_in_ca_rt (α := α)

  -- Lrev_x C.L = D.L ∩ PaddedFormat
  suffices h_eq : Lrev_x (DefinesLanguage.L C) = (D.L ∩ PaddedFormat α : Set (Word (Option α))) by
    rw [h_eq]
    exact ca_rt_inter_two D.L (PaddedFormat α)
      ⟨D, hD_rt, rfl⟩ h_padded

  -- Prove language equality
  ext u
  simp only [Lrev_x, PaddedFormat]
  constructor
  · -- Lrev_x → D.L ∩ PaddedFormat
    intro ⟨w, k, hw_mem, hk_ge, hu_eq⟩
    constructor
    · -- u ∈ D.L: by hD_spec since k ≥ |w| and w ∈ C.L
      rw [hu_eq]; exact (hD_spec w k hk_ge).mpr hw_mem
    · -- u ∈ PaddedFormat
      exact ⟨w, k, hk_ge, hu_eq⟩
  · -- D.L ∩ PaddedFormat → Lrev_x
    intro ⟨hu_D, w, k, hk_ge, hu_eq⟩
    -- u = w.map some ++ none^k with k ≥ |w| (from PaddedFormat)
    -- u ∈ D.L, so by hD_spec: w ∈ C.L
    rw [hu_eq] at hu_D
    have hw_mem := (hD_spec w k hk_ge).mp hu_D
    exact ⟨w, k, hw_mem, hk_ge, hu_eq⟩

omit [Alphabet α] in
/-- Lrev_x L = rev(L_x(rev(L))) by language algebra.

The suffix-padded lifted language equals the reversed prefix-padded reversed language:
- Lrev_x L: { w.map some ++ none^k | w ∈ L, k ≥ |w| }
- rev(L_x(rev L)): reverse { none^k ++ v.map some | v ∈ rev L, k ≥ |v| }
                 = { (v.map some).reverse ++ none^k | v.reverse ∈ L, k ≥ |v| }
                 = { w.map some ++ none^k | w ∈ L, k ≥ |w| } -/
lemma Lrev_x_eq_rev_Lx_rev (L : Language α) :
    Lrev_x L = Language.rev (L_x (Language.rev L)) := by
  ext u
  simp only [Lrev_x, L_x, Language.rev]
  constructor
  · -- Lrev_x → rev(L_x(rev L))
    intro ⟨w, k, hw_mem, hk_ge, hu_eq⟩
    -- u = w.map some ++ none^k with w ∈ L, k ≥ nextPow2 |w|
    -- Need: u.reverse ∈ L_x (rev L)
    -- i.e., ∃ v ∈ rev L, k' ≥ nextPow2 |v|, u.reverse = none^k' ++ v.map some
    use w.reverse, k
    refine ⟨?_, ?_, ?_⟩
    · -- w.reverse ∈ rev L, i.e., w.reverse.reverse ∈ L
      show w.reverse.reverse ∈ L
      simp only [List.reverse_reverse]
      exact hw_mem
    · -- k ≥ |w.reverse| = |w|
      simp only [List.length_reverse]
      exact hk_ge
    · -- u.reverse = none^k ++ (w.reverse).map some
      subst hu_eq
      simp only [List.reverse_append, List.reverse_replicate, List.map_reverse]
  · -- rev(L_x(rev L)) → Lrev_x
    intro ⟨v, k, hv_mem, hk_ge, hu_rev_eq⟩
    -- u.reverse = none^k ++ v.map some with v ∈ rev L (i.e., v.reverse ∈ L)
    use v.reverse, k
    constructor
    · -- v.reverse ∈ L
      exact hv_mem
    · constructor
      · -- k ≥ |v.reverse| = |v|
        simp only [List.length_reverse]
        exact hk_ge
      · -- u = (v.reverse).map some ++ none^k
        have : u = u.reverse.reverse := by simp
        rw [this, hu_rev_eq]
        simp only [List.reverse_append, List.reverse_replicate, List.map_reverse]

/-- For L ∈ ℒ(CA_2n), the suffix-padded lifted language is in CA_rt.
    Alias for `ca_2n_padded_in_ca_rt`. -/
theorem ca_2n_suffix_padded_in_ca_rt (L : Language α) (hL : L ∈ ℒ (CA_2n α)) :
    Lrev_x L ∈ ℒ (CA_rt (Option α)) :=
  ca_2n_padded_in_ca_rt L hL

/-- If ℒ_rev(CA_rt) ⊆ ℒ(CA_rt) for all alphabets,
    then ℒ(CA_2n β) ⊆ ℒ(CA_rt β).

**Proof** (double reversal):
1. Pad: Lrev_x L ∈ ℒ(CA_rt (Option β)) — `ca_2n_suffix_padded_in_ca_rt`
2. Rewrite: = rev(L_x(rev L)) — `Lrev_x_eq_rev_Lx_rev`
3. First reversal: L_x(rev L) ∈ ℒ(CA_rt (Option β)) — via ℒ_rev ⊆ ℒ
4. Remove padding: rev L ∈ ℒ(CA_rt β) — `lx_rt_implies_rt`
5. Second reversal: L ∈ ℒ(CA_rt β) — via ℒ_rev ⊆ ℒ -/
theorem rt_rev_closed_implies_ca_2n_subset_ca_rt (β : Type) [Alphabet β]
    (h_rev_closure : ∀ (γ : Type) [Alphabet γ], ℒ_rev (CA_rt γ) ⊆ ℒ (CA_rt γ)) :
    ℒ (CA_2n β) ⊆ ℒ (CA_rt β) := by
  intro L hL_2n

  -- Step 1: Lrev_x L ∈ ℒ(CA_rt (Option β))
  have h1 : Lrev_x L ∈ ℒ (CA_rt (Option β)) :=
    ca_2n_suffix_padded_in_ca_rt L hL_2n

  -- Step 2: Rewrite to rev form for reversal closure
  rw [Lrev_x_eq_rev_Lx_rev] at h1

  -- Step 3: L_x(rev L) ∈ ℒ(CA_rt (Option β)) by reversal closure
  have h3 : L_x (Language.rev L) ∈ ℒ (CA_rt (Option β)) := by
    rw [← Language.rev_rev (L_x (Language.rev L))]
    apply h_rev_closure
    simp only [ℒ_rev, LanguageClass.rev, Set.mem_image]
    exact ⟨_, h1, rfl⟩

  -- Step 4: rev L ∈ ℒ(CA_rt β) by lx_rt_implies_rt
  have h4 : Language.rev L ∈ ℒ (CA_rt β) :=
    lx_rt_implies_rt (Language.rev L) h3

  -- Step 5: L ∈ ℒ(CA_rt β) by reversal closure
  rw [← Language.rev_rev L]
  apply h_rev_closure
  simp only [ℒ_rev, LanguageClass.rev, Set.mem_image]
  exact ⟨_, h4, rfl⟩

/-- Main direction (⇐): If ℒ_rev(CA_rt) ⊆ ℒ(CA_rt) for all alphabets,
    then ℒ(CA_rt) = ℒ(CA_2n).

Combines `ca_rt_subset_ca_2n` with `rt_rev_closed_implies_ca_2n_subset_ca_rt`. -/
theorem rt_eq_rt_rev_implies_rt_eq_2n (β : Type) [Alphabet β]
    (h_rev_closure : ∀ (γ : Type) [Alphabet γ], ℒ_rev (CA_rt γ) ⊆ ℒ (CA_rt γ)) :
    ℒ (CA_rt β) = ℒ (CA_2n β) := by
  ext L
  constructor
  · -- RT ⊆ 2n
    exact fun hL => ca_rt_subset_ca_2n hL
  · -- 2n ⊆ RT (the hard direction)
    exact fun hL => rt_rev_closed_implies_ca_2n_subset_ca_rt β h_rev_closure hL

/-! ## Section 4: The Equivalence -/

/-- **Main Theorem**: ℒ(CA_rt) = ℒ(CA_2n) ⟺ ℒ(CA_rt) = ℒᴿ(CA_rt)

The equivalence between:
- Real-time equals 2n-time
- Real-time is closed under language reversal

Note: Direction (⇐) requires reversal closure for all alphabets (to use Option β),
while direction (⇒) only needs it for α. -/
theorem rt_eq_2n_iff_rt_eq_rt_rev :
    (∀ (β : Type) [Alphabet β], ℒ (CA_rt β) = ℒ (CA_2n β)) ↔
    (∀ (γ : Type) [Alphabet γ], ℒ (CA_rt γ) = ℒ_rev (CA_rt γ)) := by
  constructor
  · -- (⇒) ℒ(CA_rt) = ℒ(CA_2n) for all β implies reversal closure
    intro h γ _
    exact rt_eq_2n_implies_rt_eq_rt_rev (h γ)
  · -- (⇐) Reversal closure implies ℒ(CA_rt) = ℒ(CA_2n)
    intro h β _
    -- Convert ℒ(CA_rt) = ℒ_rev(CA_rt) to ℒ_rev(CA_rt) ⊆ ℒ(CA_rt)
    have h_rev : ∀ (γ : Type) [Alphabet γ], ℒ_rev (CA_rt γ) ⊆ ℒ (CA_rt γ) := by
      intro γ _
      rw [← h γ]
    exact rt_eq_rt_rev_implies_rt_eq_2n β h_rev

#print axioms rt_eq_2n_iff_rt_eq_rt_rev

end CellularAutomatas
