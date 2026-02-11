import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.left_indep_speedup
import CellularAutomatas.proofs.passive_border
import CellularAutomatas.proofs.left_indep_to_regular
import CellularAutomatas.proofs.regular_to_left_indep

namespace CellularAutomatas

open CellAutomaton


def cast α (x: α := by rfl) := x


structure CAgfSpeedup where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β  -- Takes optional alphabet for finite words

attribute [instance] CAgfSpeedup._inst_α
attribute [instance] CAgfSpeedup._inst_β

namespace CAgfSpeedup

variable (e : CAgfSpeedup)

def step1 := RegularToLeftIndep.mk e.C_orig

def step2 := LeftIndepSpeedup.mk e.step1.C 3 (by decide) e.step1.C_left_independent

def step3 := LeftIndepToRegular.mk e.step2.C e.step2.C_left_indep

def C := e.step3.C

def g1 (q: Fin 3 → e.step2.β): e.β := match q 2 with
  | BetaUnionSq.single s => s
  | BetaUnionSq.pair _ _ => default

lemma g1_spec (w: Word e.α) (h: w.length > 0) (p: ℕ):
    e.g1 (e.C.comp w (2 * p + 1) (p)) = e.C_orig.comp w (3 * p + 1) 0 := by
  rw [C]
  unfold embed_word
  rw [e.step3.spec]

  have : e.step3.C_orig = e.step2.C := by rfl
  rw [this]

  rw [<-embed_word]
  rw [<-embed_word]
  unfold g1
  rw [e.step2.spec (hi := by ring_nf; grind) (hw := h) (hi2 := by grind)]

  rw [cast $ e.step2.C_orig = e.step1.C]

  simp only [cast $ e.step2.k = 3]

  erw [e.step1.spec]
  simp [cast $ e.step2.k = 3]
  ring_nf

  have : (2 + (p: ℤ) * 6).toNat % 2 = 0 := by grind
  simp only [this, ↓reduceIte]

  rw [cast $ e.step1.C_orig = e.C_orig]
  congr
  grind
  grind



def g2 (q: Fin 3 → e.step2.β): e.β × e.β :=
  (
    match q 1 with
    | BetaUnionSq.single _ => default
    | BetaUnionSq.pair s _ => s,
    match q 0 with
    | BetaUnionSq.single s => s
    | BetaUnionSq.pair _ _ => default
  )


lemma g2_spec (w: Word e.α) (h: w.length > 0) (p: ℕ) :
    e.g2 (e.C.comp w (2 * p + 2) (p + 1)) = (e.C_orig.comp w (3 * p + 2) 0, e.C_orig.comp w (3 * p + 3) 0) := by
  rw [C]
  unfold embed_word
  rw [e.step3.spec]

  have : e.step3.C_orig = e.step2.C := by rfl
  rw [this]

  rw [<-embed_word]
  rw [<-embed_word]
  unfold g2
  rw [e.step2.spec (hi := by ring_nf; grind) (hw := h) (hi2 := by grind)]
  rw [e.step2.spec (hi := by ring_nf; grind) (hw := h) (hi2 := by grind)]


  rw [cast $ e.step2.C_orig = e.step1.C]

  simp only [cast $ e.step2.k = 3]

  erw [e.step1.spec]
  erw [e.step1.spec]
  simp [cast $ e.step2.k = 3]
  ring_nf

  have : ((6 + (p: ℤ) * 6).toNat - 1) % 2 = 1 := by grind
  simp only [this, one_ne_zero, ↓reduceIte]

  have : ((6 + (p: ℤ) * 6).toNat) % 2 = 0 := by grind
  simp only [this, ↓reduceIte]

  rw [cast $ e.step1.C_orig = e.C_orig]

  constructor

  congr
  grind
  grind

  congr
  grind
  grind


end CAgfSpeedup


notation:max x "³"  => Fin 3 → x


def triple_at {Q} (c: ℕ → Q) (i: ℕ): Q³ := fun o => c (i + o)



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
  lemma C_δ_fst_lt (a b c : e.C.Q) (k : Fin 4) (hk : k.val < 3) :
      (e.C.δ a b c).1 k = b.1 ⟨k.val + 1, by omega⟩ := by
    simp only [C, dif_pos hk]

  /-- The δ function at index 3 computes the speedup transition -/
  lemma C_δ_fst_3 (a b c : e.C.Q) :
      (e.C.δ a b c).1 ⟨3, by omega⟩ = e.speedup.C.δ (a.1 ⟨3, by omega⟩) (b.1 ⟨3, by omega⟩) (c.1 ⟨3, by omega⟩) := by
    simp only [C, show ¬(3 < 3) by omega, dif_neg, not_false_eq_true]

  /-- Helper: at time t, the state at position i has form (history, rightHist) where history tracks speedup states -/
  lemma C_embed_eq (w: Word e.α) (i: ℤ):
      e.C.nextt (embed_word w) 0 i =
      (fun _ => e.speedup.C.nextt (embed_word w) 0 i, fun _ => e.speedup.C.nextt (embed_word w) 0 i) := by
    simp only [CellAutomaton.nextt_zero, embed_word, CellAutomaton.embed_config, C]

  /-- At time t and position i, self[k] = speedup.C.nextt at (t-3+k, i).
      Proof idea: By induction on t.
      - Base case t=3: After 3 transitions, self = [S(0), S(1), S(2), S(3)] at position i.
      - Inductive step: The transition function shifts history, so self[k] = prev.self[k+1] for k<3,
        and self[3] = speedup.δ(prev neighbors). By IH, prev.self[k+1] = speedup.nextt(t-3+(k+1)) = speedup.nextt(t-2+k). -/
  lemma C_self_tracks_speedup (w: Word e.α) (t: ℕ) (i: ℤ) (k: Fin 4) (ht: t ≥ 3):
      (e.C.nextt (embed_word w) t i).1 k =
      e.speedup.C.nextt (embed_word w) (t - 3 + k) i := by
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
      have step : e.C.nextt (embed_word w) (t' + 4) i =
        e.C.next (e.C.nextt (embed_word w) (t' + 3)) i := by
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
  lemma C_right_tracks_speedup (w: Word e.α) (t: ℕ) (i: ℤ) (k: Fin 4) (ht: t ≥ 4):
      (e.C.nextt (embed_word w) t i).2 k =
      e.speedup.C.nextt (embed_word w) (t - 4 + k) (i + 1) := by
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


  theorem spec (w: Word e.α) (hw : w.length > 0) (p: ℕ) (hp : p > 0):
      e.C.comp w (2*p + 3) p =
        some (triple_at (e.C_orig.trace w) (3 * p)) := by
    simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply, C]

    -- At time t = 2p+3 and position i = p, we extract:
    --   self[0] = speedup.C at time 2p+3-3+0 = 2p, position p
    --   self[1] = speedup.C at time 2p+3-3+1 = 2p+1, position p
    --   rightHist[3] = speedup.C at time 2p+3-4+3 = 2p+2, position p+1

    -- First, get the state components
    have h_self0 := e.C_self_tracks_speedup w (2*p+3) p ⟨0, by decide⟩ (by omega)
    have h_self1 := e.C_self_tracks_speedup w (2*p+3) p ⟨1, by decide⟩ (by omega)
    have h_right3 := e.C_right_tracks_speedup w (2*p+3) p ⟨3, by decide⟩ (by omega)

    -- Simplify the time calculations
    have ht0 : 2*p + 3 - 3 + 0 = 2*p := by omega
    have ht1 : 2*p + 3 - 3 + 1 = 2*p + 1 := by omega
    have ht2 : 2*p + 3 - 4 + 3 = 2*p + 2 := by omega

    simp only [ht0] at h_self0
    simp only [ht1] at h_self1
    simp only [ht2] at h_right3

    -- The projected outputs match the inputs to g1/g2 specs
    -- o0 = speedup.C.project(self[0]) = speedup.C.comp w (2p) p
    -- By g2_spec at (p-1): g2(speedup.C.comp w (2(p-1)+2) ((p-1)+1)) = (trace(3p-1), trace(3p))
    --   Since 2(p-1)+2 = 2p and (p-1)+1 = p, g2(o0) = (trace(3p-1), trace(3p))
    --   So g2(o0).2 = trace(3p)

    -- o1 = speedup.C.project(self[1]) = speedup.C.comp w (2p+1) p
    -- By g1_spec at p: g1(speedup.C.comp w (2p+1) p) = trace(3p+1)
    --   So g1(o1) = trace(3p+1)

    -- o2 = speedup.C.project(rightHist[3]) = speedup.C.comp w (2p+2) (p+1)
    -- By g2_spec at p: g2(speedup.C.comp w (2p+2) (p+1)) = (trace(3p+2), trace(3p+3))
    --   So g2(o2).1 = trace(3p+2)

    congr 1
    funext j
    match j with
    | ⟨0, _⟩ =>
      simp only [triple_at, Nat.add_zero, CellAutomaton.trace]
      -- Need: g2(project(self[0])).2 = C_orig.comp w (3*p) 0
      -- g2_spec at p-1: g2(speedup.C.comp w (2*(p-1)+2) ((p-1)+1)) = (trace(3*(p-1)+2), trace(3*(p-1)+3))
      -- Simplify: 2*(p-1)+2 = 2p, (p-1)+1 = p, 3*(p-1)+3 = 3p
      have hg2 := e.speedup.g2_spec w hw (p - 1)
      have htime : 2 * (p - 1) + 2 = 2 * p := by omega
      have hpos : (p - 1 : ℤ) + 1 = p := by omega
      have hout2 : 3 * (p - 1) + 3 = 3 * p := by omega
      simp only [htime, hout2, Nat.cast_sub hp, Nat.cast_one, hpos] at hg2
      -- Now hg2: g2(speedup.C.comp w (2*p) p) = (_, C_orig.comp w (3*p) 0)
      show (e.speedup.g2 (e.speedup.C.project ((e.C.nextt (embed_word w) (2 * p + 3) ↑p).1 ⟨0, _⟩))).2
          = e.C_orig.comp (embed_word w) (3 * p) 0
      rw [h_self0]
      simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply] at hg2 ⊢
      -- speedup.C_orig = C_orig by definition
      have h_eq : e.speedup.C_orig = e.C_orig := rfl
      rw [h_eq] at hg2
      exact congrArg Prod.snd hg2
    | ⟨1, _⟩ =>
      simp only [triple_at, CellAutomaton.trace]
      -- Need: g1(project(self[1])) = C_orig.comp w (3*p+1) 0
      have hg1 := e.speedup.g1_spec w hw p
      show (e.speedup.g1 (e.speedup.C.project ((e.C.nextt (embed_word w) (2 * p + 3) ↑p).1 ⟨1, _⟩)))
          = e.C_orig.comp (embed_word w) (3 * p + 1) 0
      rw [h_self1]
      simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply] at hg1 ⊢
      have h_eq : e.speedup.C_orig = e.C_orig := rfl
      rw [h_eq] at hg1
      exact hg1
    | ⟨2, _⟩ =>
      simp only [triple_at, CellAutomaton.trace]
      -- Need: g2(project(rightHist[3])).1 = C_orig.comp w (3*p+2) 0
      have hg2 := e.speedup.g2_spec w hw p
      show (e.speedup.g2 (e.speedup.C.project ((e.C.nextt (embed_word w) (2 * p + 3) ↑p).2 ⟨3, _⟩))).1
          = e.C_orig.comp (embed_word w) (3 * p + 2) 0
      rw [h_right3]
      simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply] at hg2 ⊢
      have h_eq : e.speedup.C_orig = e.C_orig := rfl
      rw [h_eq] at hg2
      exact congrArg Prod.fst hg2

end CompressToDiag
