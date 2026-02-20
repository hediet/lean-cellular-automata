import CellularAutomatas.defs
import CellularAutomatas.internal_defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.composition.speedup_compressed

namespace CellularAutomatas

open CellAutomaton


structure CompressToDiag where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α？ β

attribute [instance] CompressToDiag._inst_α
attribute [instance] CompressToDiag._inst_β

namespace CompressToDiag

  variable (e: CompressToDiag)

  /-- The underlying CAgfSpeedup construction -/
  def speedup : CAgfSpeedup where
    C_orig := e.C_orig

  /-- State tracks:
      - self: 4 time steps of speedup.C at our position
      - rightHist: 4 time steps from right neighbor (for extracting i+1 info)
      At time t, position i:
      - self[k] = speedup.C state at (t-3+k, i)
      - rightHist[k] = speedup.C state at (t-4+k, i+1) -/
  def C: CellAutomaton e.α？ (Option (e.β³)) := {
    Q := (Fin 4 → e.speedup.C.Q) × (Fin 4 → e.speedup.C.Q)
    δ := fun a b c =>
      let aS := a.1  -- speedup.C history at position i-1
      let bS := b.1  -- speedup.C history at position i
      let cS := c.1  -- speedup.C history at position i+1
      -- Compute new speedup.C state at position i
      let newState := e.speedup.C.δ (aS ⟨3, by decide⟩) (bS ⟨3, by decide⟩) (cS ⟨3, by decide⟩)
      -- Shift history and add new state
      let newSelf : Fin 4 → e.speedup.C.Q := fun j =>
        if h : j.val < 3 then bS ⟨j.val + 1, by omega⟩ else newState
      -- Copy right neighbor's current history for extraction
      (newSelf, cS)
    embed := fun x =>
      let q := e.speedup.C.embed x
      (fun _ => q, fun _ => q)
    project := fun s =>
      let self := s.1
      let rightHist := s.2
      -- At time T, position i:
      --   self[0] = speedup.C at (T-3, i) → for p=i when T=2i+3: time 2i
      --   self[1] = speedup.C at (T-2, i) → time 2i+1
      --   rightHist[3] = speedup.C at (T-1, i+1) → time 2i+2
      let o0 := e.speedup.C.project (self ⟨0, by decide⟩)
      let o1 := e.speedup.C.project (self ⟨1, by decide⟩)
      let o2 := e.speedup.C.project (rightHist ⟨3, by decide⟩)
      -- Extract trace values using g1 and g2:
      --   g2(speedup.C at (2p, p)).2 = trace(3p)
      --   g1(speedup.C at (2p+1, p)) = trace(3p+1)
      --   g2(speedup.C at (2p+2, p+1)).1 = trace(3p+2)
      let v0 := (e.speedup.g2 o0).2
      let v1 := e.speedup.g1 o1
      let v2 := (e.speedup.g2 o2).1
      some (fun j => match j with
        | ⟨0, _⟩ => v0
        | ⟨1, _⟩ => v1
        | ⟨2, _⟩ => v2)
  }

  /-- The δ function at index k<3 returns the previous self at k+1 -/
  private lemma C_δ_fst_lt (a b c : e.C.Q) (k : Fin 4) (hk : k.val < 3) :
      (e.C.δ a b c).1 k = b.1 ⟨k.val + 1, by omega⟩ := by
    simp only [C, dif_pos hk]

  /-- The δ function at index 3 computes the speedup transition -/
  private lemma C_δ_fst_3 (a b c : e.C.Q) :
      (e.C.δ a b c).1 ⟨3, by omega⟩ = e.speedup.C.δ (a.1 ⟨3, by omega⟩) (b.1 ⟨3, by omega⟩) (c.1 ⟨3, by omega⟩) := by
    simp only [C, show ¬(3 < 3) by omega, dif_neg, not_false_eq_true]

  /-- Helper: at time t, the state at position i has form (history, rightHist) where history tracks speedup states -/
  private lemma C_embed_eq (w: Word e.α) (i: ℤ):
      e.C.nextt (w) 0 i =
      (fun _ => e.speedup.C.nextt (w) 0 i, fun _ => e.speedup.C.nextt (w) 0 i) := by
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, word_to_config, C]

  /-- At time t and position i, self[k] = speedup.C.nextt at (t-3+k, i).
      Proof idea: By induction on t.
      - Base case t=3: After 3 transitions, self = [S(0), S(1), S(2), S(3)] at position i.
      - Inductive step: The transition function shifts history, so self[k] = prev.self[k+1] for k<3,
        and self[3] = speedup.δ(prev neighbors). By IH, prev.self[k+1] = speedup.nextt(t-3+(k+1)) = speedup.nextt(t-2+k). -/
  private lemma C_self_tracks_speedup (w: Word e.α) (t: ℕ) (i: ℤ) (k: Fin 4) (ht: t ≥ 3):
      (e.C.nextt (w) t i).1 k =
      e.speedup.C.nextt (w) (t - 3 + k) i := by
    -- Induction on t starting from t = 3
    match t with
    | 0 | 1 | 2 => omega
    | 3 =>
      -- Base case: unfold 3 transitions from time 0
      -- Match on k and compute both sides by unfolding
      match k with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
    | t' + 4 =>
      -- Inductive case: t = t' + 4 ≥ 4, so t - 1 = t' + 3 ≥ 3
      have ht' : t' + 3 ≥ 3 := by omega
      have step : e.C.nextt (w) (t' + 4) i =
        e.C.next (e.C.nextt (w) (t' + 3)) i := by
        rw [show t' + 4 = (t' + 3) + 1 by ring, CellAutomaton.nextt_succ]
      -- Unfold to C.next which is C.δ applied to neighbors
      simp only [step, CellAutomaton.next]
      -- Now goal: (e.C.δ a b c).1 k = e.speedup.C.nextt ... (t'+4-3+k) i
      -- Use helper lemmas for C.δ behavior (without unfolding C)
      match k with
      | ⟨0, h0⟩ =>
        -- 0 < 3, so we get b.1 ⟨1,...⟩
        have hk0 : (0 : ℕ) < 3 := by decide
        rw [e.C_δ_fst_lt _ _ _ ⟨0, h0⟩ hk0]
        have ih := C_self_tracks_speedup w (t' + 3) i ⟨1, by omega⟩ ht'
        simp only [show (t' + 3 - 3 + ↑1: ℕ) = t' + 1 by omega] at ih
        simp only [show (t' + 4 - 3 + ↑0: ℕ) = t' + 1 by omega]
        exact ih
      | ⟨1, h1⟩ =>
        -- 1 < 3, so we get b.1 ⟨2,...⟩
        have hk1 : (1 : ℕ) < 3 := by decide
        rw [e.C_δ_fst_lt _ _ _ ⟨1, h1⟩ hk1]
        have ih := C_self_tracks_speedup w (t' + 3) i ⟨2, by omega⟩ ht'
        simp only [show (t' + 3 - 3 + ↑2: ℕ) = t' + 2 by omega] at ih
        simp only [show (t' + 4 - 3 + ↑1: ℕ) = t' + 2 by omega]
        exact ih
      | ⟨2, h2⟩ =>
        -- 2 < 3, so we get b.1 ⟨3,...⟩
        have hk2 : (2 : ℕ) < 3 := by decide
        rw [e.C_δ_fst_lt _ _ _ ⟨2, h2⟩ hk2]
        have ih := C_self_tracks_speedup w (t' + 3) i ⟨3, by omega⟩ ht'
        simp only [show (t' + 3 - 3 + ↑3: ℕ) = t' + 3 by omega] at ih
        simp only [show (t' + 4 - 3 + ↑2: ℕ) = t' + 3 by omega]
        exact ih
      | ⟨3, _⟩ =>
        -- ¬(3 < 3), so we get speedup.δ(a.1 3, b.1 3, c.1 3)
        rw [e.C_δ_fst_3]
        -- By IH, prev.self[3] at positions i-1, i, i+1 are S(t'+3)
        have ih_a := C_self_tracks_speedup w (t' + 3) (i - 1) ⟨3, by omega⟩ ht'
        have ih_b := C_self_tracks_speedup w (t' + 3) i ⟨3, by omega⟩ ht'
        have ih_c := C_self_tracks_speedup w (t' + 3) (i + 1) ⟨3, by omega⟩ ht'
        simp only [show (t' + 3 - 3 + ↑3: ℕ) = t' + 3 by omega] at ih_a ih_b ih_c
        simp only [show (t' + 4 - 3 + ↑3: ℕ) = t' + 4 by omega]
        -- Goal: speedup.δ (a.1 3) (b.1 3) (c.1 3) = nextt (t'+4) i
        -- Rewrite using IH, then unfold nextt on RHS
        conv_lhs => rw [ih_a, ih_b, ih_c]
        conv_rhs => rw [show t' + 4 = (t' + 3) + 1 by ring, CellAutomaton.nextt_succ, CellAutomaton.next]

  /-- At time t and position i, rightHist[k] = speedup.C.nextt at (t-4+k, i+1).
      Follows from C_self_tracks_speedup since rightHist copies the previous step's self from position i+1. -/
  private lemma C_right_tracks_speedup (w: Word e.α) (t: ℕ) (i: ℤ) (k: Fin 4) (ht: t ≥ 4):
      (e.C.nextt (w) t i).2 k =
      e.speedup.C.nextt (w) (t - 4 + k) (i + 1) := by
    -- After transition, rightHist = c.self where c is at position i+1
    -- Use C_self_tracks_speedup at position i+1 and time t-1
    match t with
    | 0 | 1 | 2 | 3 => omega
    | t' + 4 =>
      have ht' : t' + 3 ≥ 3 := by omega
      rw [show t' + 4 = (t' + 3) + 1 by ring, CellAutomaton.nextt_succ]
      simp only [CellAutomaton.next, C]
      -- rightHist after transition is c.self from time t'+3
      have h_self := e.C_self_tracks_speedup w (t' + 3) (i + 1) k ht'
      convert h_self using 2


  theorem spec (w: Word e.α) (hw : w.length > 0) (p: ℕ):
      e.C.comp w (2*p + 3) p =
        some (triple_at (e.C_orig.trace w) (3 * p)) := by
    simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply, C]

    have h_self0 := e.C_self_tracks_speedup w (2*p+3) p ⟨0, by decide⟩ (by omega)
    have h_self1 := e.C_self_tracks_speedup w (2*p+3) p ⟨1, by decide⟩ (by omega)

    have ht0 : 2*p + 3 - 3 + 0 = 2*p := by omega
    have ht1 : 2*p + 3 - 3 + 1 = 2*p + 1 := by omega
    simp only [ht0] at h_self0
    simp only [ht1] at h_self1

    -- rightHist[3]: for p ≥ 1, use C_right_tracks_speedup; for p = 0, compute directly
    have h_right3 : (e.C.nextt (w) (2*p+3) p).2 ⟨3, by decide⟩ =
        e.speedup.C.nextt (w) (2*p + 2) (p + 1) := by
      by_cases hp : p = 0
      · subst hp; rfl
      · have hp' : p ≥ 1 := Nat.one_le_iff_ne_zero.mpr hp
        have h := e.C_right_tracks_speedup w (2*p+3) p ⟨3, by decide⟩ (by omega)
        simp only [show 2*p + 3 - 4 + 3 = 2*p + 2 by omega] at h
        convert h using 3

    congr 1
    funext j
    match j with
    | ⟨0, _⟩ =>
      simp only [triple_at, Nat.add_zero, CellAutomaton.trace]
      show (e.speedup.g2 (e.speedup.C.project ((e.C.nextt (w) (2 * p + 3) ↑p).1 ⟨0, _⟩))).2
          = e.C_orig.comp (w) (3 * p) 0
      rw [h_self0]
      simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply]
      have h_eq : e.speedup.C_orig = e.C_orig := rfl
      -- For p = 0: use g2_initial_spec; for p > 0: use g2_spec(p-1)
      by_cases hp : p = 0
      · subst hp
        simp only [mul_zero, Nat.cast_zero]
        have := e.speedup.g2_initial_spec w hw
        simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply] at this
        rw [h_eq] at this; exact this
      · have hp' : p > 0 := Nat.pos_of_ne_zero hp
        have hg2 := e.speedup.g2_spec w hw (p - 1)
        simp only [show 2 * (p - 1) + 2 = 2 * p by omega,
          show 3 * (p - 1) + 3 = 3 * p by omega,
          Nat.cast_sub hp', Nat.cast_one, show (p - 1 : ℤ) + 1 = p by omega] at hg2
        simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply] at hg2
        rw [h_eq] at hg2; exact congrArg Prod.snd hg2
    | ⟨1, _⟩ =>
      simp only [triple_at, CellAutomaton.trace]
      have hg1 := e.speedup.g1_spec w hw p
      show (e.speedup.g1 (e.speedup.C.project ((e.C.nextt (w) (2 * p + 3) ↑p).1 ⟨1, _⟩)))
          = e.C_orig.comp (w) (3 * p + 1) 0
      rw [h_self1]
      simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply] at hg1 ⊢
      have h_eq : e.speedup.C_orig = e.C_orig := rfl
      rw [h_eq] at hg1; exact hg1
    | ⟨2, _⟩ =>
      simp only [triple_at, CellAutomaton.trace]
      have hg2 := e.speedup.g2_spec w hw p
      show (e.speedup.g2 (e.speedup.C.project ((e.C.nextt (w) (2 * p + 3) ↑p).2 ⟨3, _⟩))).1
          = e.C_orig.comp (w) (3 * p + 2) 0
      rw [h_right3]
      simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply] at hg2 ⊢
      have h_eq : e.speedup.C_orig = e.C_orig := rfl
      rw [h_eq] at hg2; exact congrArg Prod.fst hg2

end CompressToDiag

end CellularAutomatas
