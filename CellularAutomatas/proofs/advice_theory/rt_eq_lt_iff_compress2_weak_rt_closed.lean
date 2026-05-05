/-
  # ℒ(CA_rt) = ℒ(CA_lt) ↔ compress2 weak-rt-closed

  This file splits the theorem `ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed`
  into its two directions:

  - `ca_rt_eq_ca_lt_of_compress2_weak_rt_closed` (`←`):
      `compress2 weak-rt-closed ⟹ ℒ(CA_rt α) = ℒ(CA_lt α)`.

      Proof outline:
      * `ℒ(CA_rt α) ⊆ ℒ(CA_lt α)`: every CA_rt is a CA_lt with `c = 1`.
      * `ℒ(CA_lt α) ⊆ ℒ(CA_rt α)`: by `ca_2n_eq_ca_lt` (sorry'd) we reduce
        to `ℒ(CA_2n α) ⊆ ℒ(CA_rt α)`. Then `compress2` weak-rt-closure
        + the `k = 2` `SpeedupKx` construction gives us a CA_rt over the
        compress2-annotated alphabet that simulates the CA_2n in real time.

  - `compress2_weak_rt_closed_of_ca_rt_eq_ca_lt` (`→`): currently `sorry`.

  - `ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed` (the iff): just packages the two.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.ca_rt_utils
import CellularAutomatas.proofs.constructions.speedup_compressed
import CellularAutomatas.verification_candidates

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

open CellAutomaton

/-! ## Trivial direction: `ℒ(CA_rt α) ⊆ ℒ(CA_lt α)` -/

/-- Any real-time CA is a linear-time CA with `c = 1`: the schemas
    `.rt_center` and `.lt_center 1` produce the same `t` and `p`. -/
theorem ca_rt_subset_ca_lt : ℒ (CA_rt α) ⊆ ℒ (CA_lt α) := by
  intro L ⟨C, hL⟩
  -- Wrap C as a tCellAutomaton with schema `.lt_center 1`.
  -- The schemas `.rt_center` and `.lt_center 1` give the same `t` and `p`,
  -- so the same underlying CellAutomaton accepts the same words.
  refine ⟨⟨1, { toCellAutomaton := C.toCellAutomaton }⟩, ?_⟩
  show L = (⟨1, _⟩ : CA_lt α).2.L
  rw [hL]
  ext w
  show C.accepts w ↔ _
  simp only [tCellAutomaton.accepts, tCellAutomaton.L,
             AcceptanceSchema.rt_center, AcceptanceSchema.lt_center, one_mul]
  rfl

/-! ## Key lemma: `compress2 weak-rt-closed ⟹ ℒ(CA_2n α) ⊆ ℒ(CA_rt α)`

    Proof idea (using `SpeedupKx` with `k = 2`):

    Given `C₀ : CA_2n α`, view its underlying `LCellAutomaton α` (a
    `CellAutomaton α？ Bool`) and apply `SpeedupKx` with `k = 2` to obtain a
    speedup CA `SP.C : CellAutomaton (Fin 2 → α？) (Fin 2 → Bool)` satisfying
    `SP.C.trace (compress 2 c) t = C₀.trace c (2 * t)` (`SpeedupKx.spec1`).

    We then wrap `SP.C` as a CA_rt over the compress2-annotated alphabet
    `α × (Option α × Option α)`:
    * embed `(a, (l, r))` as `SP.C.embed (i ↦ if i = 0 then l else r)`
      (we discard `a`; the pair from compress2 carries the original cells);
    * embed border `none` as `SP.C.embed (fun _ ↦ none)`;
    * project a state by reading index `0` of the speedup's `Fin 2 → Bool`
      output.

    On a word `w` of length `n`, the embedded annotated config matches
    `compress 2 ⟬w⟭` cell-by-cell, so by `SpeedupKx.spec1` running for
    `n − 1` steps yields the same answer as `C₀` after `2 (n − 1)` steps —
    which is exactly `C₀.accepts w`.

    Finally, `compress2.weak_rt_closed` converts the wrapped CA into a CA_rt
    over the base alphabet `α` recognising `L(C₀)`.
-/

namespace Compress2Sim

/-- Decode an annotated symbol back to a `Fin 2 → α？` (the speedup-CA cell
    contents). The α component is discarded; the two cells come from the
    compress2 advice. Border (`none`) maps to `(none, none)`. -/
def extract2 : (α × (Option α × Option α))？ → (Fin 2 → α？)
  | none           => fun _ => none
  | some (_, l, r) => fun i => if i = 0 then l else r

/-- Build the speedup-`k=2` simulator of a CA_2n. -/
def SP (C₀ : CA_2n α) : SpeedupKx where
  k := 2
  α := α？
  β := Bool
  C_orig := C₀.toCellAutomaton

/-- The wrapped speedup CA, with input alphabet `(α × (Option α × Option α))？`
    and output `Bool` — i.e. an `LCellAutomaton (α × (Option α × Option α))`. -/
def simCA (C₀ : CA_2n α) :
    CellAutomaton (α × (Option α × Option α))？ Bool :=
  ((SP C₀).C.map_embed extract2).map_project (· 0)

/-- The simulator as a CA_rt over the annotated alphabet. -/
def simRtCA (C₀ : CA_2n α) :
    CA_rt (α × (Option α × Option α)) :=
  toRtCa (simCA C₀)

/-- Pointwise: `extract2 ∘ ⟬annotate w⟭ = SpeedupKx.compress 2 ⟬w⟭`. This is
    the alignment between the simulator's input view and the speedup CA's
    compressed config.

    Proof: both sides reduce to a function of `(p, i : Fin 2)` returning
    `⟬w⟭ (p * 2 + i)`. -/
lemma extract2_word_to_config_eq_compress2 (w : Word α) (p : ℤ) :
    extract2 (⟬(Advice.compress2 α).annotate w⟭ p) =
      SpeedupKx.compress 2 ⟬w⟭ p := by
  have h_ann_len : ((Advice.compress2 α).annotate w).length = w.length := by
    simp [Advice.annotate]
  -- Step 1: rewrite ⟬annotate w⟭ p into a clean dite-free form.
  funext i
  -- After unfolding `SpeedupKx.compress`, RHS = ⟬w⟭ (p * 2 + ↑↑i).
  show extract2 _ i = ⟬w⟭ (p * 2 + ((i : ℕ) : ℤ))
  by_cases hp : 0 ≤ p ∧ p < (w : List α).length
  · -- In-range p.
    obtain ⟨hp0, hpn⟩ := hp
    have hpt : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp0
    have hpn' : p.toNat < w.length := by omega
    -- Compute the in-range length of the annotated word.
    have hpn_ann : p < (((Advice.compress2 α).annotate w) : List _).length := by
      rw [h_ann_len]; exact hpn
    -- The lookup at position p.toNat in the annotated word.
    have h_lookup_eq :
        ((Advice.compress2 α).annotate w)[p.toNat]'(by rw [h_ann_len]; exact hpn') =
          (w[p.toNat], w[2 * p.toNat]?, w[2 * p.toNat + 1]?) := by
      simp [Advice.annotate, Advice.compress2]
    -- Decode the LHS lookup: `⟬annotate w⟭ p = some (w[p], (w[2p]?, w[2p+1]?))`.
    have h_lhs :
        ⟬(Advice.compress2 α).annotate w⟭ p =
          some (w[p.toNat], w[2 * p.toNat]?, w[2 * p.toNat + 1]?) := by
      rw [word_to_config_apply, dif_pos ⟨hp0, hpn_ann⟩, h_lookup_eq]
    rw [h_lhs]
    -- Now LHS = `if i = 0 then w[2p]? else w[2p+1]?`. Case on i.
    fin_cases i
    · -- i = 0: both sides reduce to ⟬w⟭ (p * 2).
      show w[2 * p.toNat]? = ⟬w⟭ (p * 2 + 0)
      rw [add_zero, word_to_config_apply]
      have h_idx_eq : (p * 2).toNat = 2 * p.toNat := by omega
      split_ifs with h
      · -- p * 2 in range: both sides = some w[2 * p.toNat].
        obtain ⟨_, h_ub⟩ := h
        -- Convert the `some w[(p*2).toNat]` on RHS back to `w[(p*2).toNat]?`,
        -- then rewrite the index using `h_idx_eq`.
        rw [← List.getElem?_eq_getElem (by omega : (p * 2).toNat < w.length),
            h_idx_eq]
      · -- p * 2 out of range on the right: both sides = none.
        push_neg at h
        have h_oor : 2 * p.toNat ≥ w.length := by
          have := h (by linarith); omega
        exact List.getElem?_eq_none h_oor
    · -- i = 1: both sides reduce to ⟬w⟭ (p * 2 + 1).
      show w[2 * p.toNat + 1]? = ⟬w⟭ (p * 2 + 1)
      rw [word_to_config_apply]
      have h_idx_eq : (p * 2 + 1).toNat = 2 * p.toNat + 1 := by omega
      split_ifs with h
      · obtain ⟨_, h_ub⟩ := h
        rw [← List.getElem?_eq_getElem (by omega : (p * 2 + 1).toNat < w.length),
            h_idx_eq]
      · push_neg at h
        have h_oor : 2 * p.toNat + 1 ≥ w.length := by
          have := h (by linarith); omega
        exact List.getElem?_eq_none h_oor
  · -- Out-of-range p: both sides are `none`.
    push_neg at hp
    rw [show ⟬(Advice.compress2 α).annotate w⟭ p = none from by
          rw [word_to_config_apply]
          refine dif_neg ?_
          rintro ⟨h1, h2⟩
          rw [h_ann_len] at h2
          exact absurd h2 (not_lt.mpr (hp h1))]
    show (none : α？) = ⟬w⟭ (p * 2 + ((i : ℕ) : ℤ))
    rw [word_to_config_apply]
    have hi_nn : 0 ≤ ((i : ℕ) : ℤ) := Int.natCast_nonneg _
    have hi_lt : ((i : ℕ) : ℤ) < 2 := by exact_mod_cast i.isLt
    rcases lt_or_ge p 0 with hp_neg | hp_pos
    · -- p < 0 ⟹ p * 2 + i < 0 (since i ≤ 1, p ≤ -1, so p*2 ≤ -2, p*2+i ≤ -1).
      symm
      refine dif_neg ?_
      rintro ⟨h1, _⟩
      omega
    · -- p ≥ |w| ⟹ p * 2 + i ≥ |w|.
      have hp_ge : (w : List α).length ≤ p := hp hp_pos
      symm
      refine dif_neg ?_
      rintro ⟨_, h2⟩
      nlinarith

/-- Simulator correctness: `simRtCA C₀` accepts the compress2-annotated word
    iff `C₀` accepts `w`.

    Proof outline (using `SpeedupKx.spec1`):
    1. Reduce both sides via `tCellAutomaton.accepts` to plain `comp` calls
       at appropriate times (`n − 1` on the left, `2(n − 1)` on the right).
    2. Show the simulator's embedded annotated config equals
       `(SP C₀).C` evaluated on the compressed config
       `SpeedupKx.compress 2 ⟬w⟭` — this is
       `extract2_word_to_config_eq_compress2`.
    3. Apply `SpeedupKx.spec1` (k = 2) to rewrite
       `(SP C₀).C.trace (compress 2 ⟬w⟭) (n−1) 0` as
       `(SP C₀).C_orig.trace ⟬w⟭ (2(n−1))`, which equals `C₀.accepts w`. -/
lemma simRtCA_accepts_iff (C₀ : CA_2n α) (w : Word α) :
    (simRtCA C₀).accepts ((Advice.compress2 α).annotate w) = C₀.accepts w := by
  have h_ann_len : ((Advice.compress2 α).annotate w).length = w.length := by
    simp [Advice.annotate]
  -- The embedded annotated config (under simCA's embed) equals the compressed config
  -- (under (SP C₀).C's embed). This is the conceptual content of the proof.
  have h_emb :
      (CellAutomaton.embed_config (C := (SP C₀).C.map_embed extract2)
          ⟬(Advice.compress2 α).annotate w⟭ : Config _) =
        CellAutomaton.embed_config (C := (SP C₀).C) (SpeedupKx.compress 2 ⟬w⟭) := by
    funext p
    show (SP C₀).C.embed (extract2 _) = (SP C₀).C.embed _
    rw [extract2_word_to_config_eq_compress2]
  -- Reduce `accepts` to `comp ⟦…⟧ t p` on both sides; the LHS schema gives `n − 1`,
  -- the RHS schema gives `2 (n − 1)`.
  show (simRtCA C₀).comp _ (((Advice.compress2 α).annotate w).length - 1) 0 =
       C₀.toCellAutomaton.comp _ (2 * (w.length - 1)) 0
  rw [h_ann_len]
  -- Unfold simRtCA = toRtCa (simCA C₀); simCA = (SP C₀).C.map_embed extract2 |>.map_project (·0).
  -- After these unfoldings, LHS = (·0) ((SP C₀).C.project ((SP C₀).C.nextt ⦋⟬annotate w⟭⦌ (n-1) 0)).
  show ((SP C₀).C.map_embed extract2 |>.map_project (· 0)).comp
        ⟬(Advice.compress2 α).annotate w⟭ (w.length - 1) 0 = _
  -- Reduce comp via map_project: project_config of map_project = (·0) ∘ project_config of C.
  -- Reduce nextt via map_embed: nextt of map_embed = nextt of C.
  rw [show ((SP C₀).C.map_embed extract2 |>.map_project (· 0)).comp
        ⟬(Advice.compress2 α).annotate w⟭ (w.length - 1) 0 =
      ((SP C₀).C.comp
        (CellAutomaton.embed_config (C := (SP C₀).C.map_embed extract2)
          ⟬(Advice.compress2 α).annotate w⟭) (w.length - 1) 0) 0 from rfl]
  -- Now LHS uses ⦋⟬annotate w⟭⦌ (under map_embed); rewrite via h_emb to ⦋compress 2 ⟬w⟭⦌ (under (SP C₀).C).
  rw [h_emb]
  -- Goal: ((SP C₀).C.project ((SP C₀).C.nextt ⦋compress 2 ⟬w⟭⦌ (n-1) 0)) 0
  --     = C₀.toCellAutomaton.comp ⦋⟬w⟭⦌ (2 * (n - 1)) 0
  -- The LHS = (SP C₀).C.trace (compress 2 ⟬w⟭) (n-1) 0 by definition of trace.
  -- Apply SpeedupKx.spec1 to swap to C_orig at time 2 (n - 1).
  have hspec :
      ((SP C₀).C.trace (SpeedupKx.compress 2 ⟬w⟭) (w.length - 1)) 0 =
        (SP C₀).C_orig.trace ⟬w⟭ (2 * (w.length - 1)) := by
    have := (SP C₀).spec1 (c := ⟬w⟭) (t1 := w.length - 1)
    simpa [SP] using this
  -- Both sides of the goal are the corresponding trace evaluations.
  -- LHS as a trace:
  show ((SP C₀).C.trace (SpeedupKx.compress 2 ⟬w⟭) (w.length - 1)) 0 = _
  rw [hspec]
  -- (SP C₀).C_orig = C₀.toCellAutomaton; trace = comp ⦋·⦌ … 0.
  rfl

end Compress2Sim


lemma ca_2n_subset_ca_rt_of_compress2_weak_rt_closed
    (h : (Advice.compress2 α).weak_rt_closed) :
    ℒ (CA_2n α) ⊆ ℒ (CA_rt α) := by
  -- Take L ∈ ℒ(CA_2n α), get a witnessing CA_2n C₀.
  intro L ⟨C₀, hL⟩
  -- The annotated CA_rt C₂ that simulates C₀ via SpeedupKx (k = 2).
  let C₂ : CA_rt (α × (Option α × Option α)) := Compress2Sim.simRtCA C₀
  -- By compress2 weak-rt-closure, the language of `C₂ + compress2` (advised)
  -- lies in ℒ(CA_rt α).
  have h_in : (C₂ + Advice.compress2 α).L ∈ ℒ (CA_rt α) := by
    rw [← h.language_eq]
    exact Advised.L_mem_ℒ ⟨C₂.toCellAutomaton⟩ (Advice.compress2 α)
  -- The advised language equals L(C₀) by the simulator-correctness lemma.
  have h_eq : (C₂ + Advice.compress2 α).L = C₀.L := by
    ext w
    show C₂.accepts ((Advice.compress2 α).annotate w) = true ↔ _
    rw [Compress2Sim.simRtCA_accepts_iff]
    rfl
  show L ∈ ℒ (CA_rt α)
  rw [hL]
  show C₀.L ∈ ℒ (CA_rt α)
  exact h_eq ▸ h_in

/-! ## (←) direction: `compress2 weak-rt-closed ⟹ ℒ(CA_rt α) = ℒ(CA_lt α)` -/

theorem ca_rt_eq_ca_lt_of_compress2_weak_rt_closed
    (h : Nonempty (Advice.compress2 α).weak_rt_closed) :
    ℒ (CA_rt α) = ℒ (CA_lt α) := by
  obtain ⟨h⟩ := h
  apply Set.Subset.antisymm
  · -- ℒ(CA_rt α) ⊆ ℒ(CA_lt α): trivial (c = 1)
    show ℒ (CA_rt α) ⊆ ℒ (CA_lt α)
    exact ca_rt_subset_ca_lt
  · -- ℒ(CA_lt α) ⊆ ℒ(CA_rt α): via ca_2n_eq_ca_lt + compress2 simulation
    show ℒ (CA_lt α) ⊆ ℒ (CA_rt α)
    calc ℒ (CA_lt α)
        = ℒ (CA_2n α) := (verification_candidates.ca_2n_eq_ca_lt).symm
      _ ⊆ ℒ (CA_rt α) := ca_2n_subset_ca_rt_of_compress2_weak_rt_closed h

/-! ## (→) direction (currently unproven) -/

/-- Given `ℒ(CA_rt α) = ℒ(CA_lt α)`, the compress2 advice is weak-rt-closed.
    A CA_rt over the compress2-annotated alphabet has language in `ℒ(CA_lt α)`
    (it can compute the compress2 layout in linear time and then run the inner CA);
    the equality then yields a witnessing CA_rt over the base alphabet. -/
theorem compress2_weak_rt_closed_of_ca_rt_eq_ca_lt
    (h : ℒ (CA_rt α) = ℒ (CA_lt α)) :
    Nonempty (Advice.compress2 α).weak_rt_closed := by
  sorry

/-! ## The iff, packaging the two directions. -/

theorem ca_rt_eq_ca_lt_iff_compress2_weak_rt_closed :
    ℒ (CA_rt α) = ℒ (CA_lt α) ↔ Nonempty (Advice.compress2 α).weak_rt_closed :=
  ⟨compress2_weak_rt_closed_of_ca_rt_eq_ca_lt,
   ca_rt_eq_ca_lt_of_compress2_weak_rt_closed⟩

end CellularAutomatas
