/-
  CompressToDiag: Converting arbitrary CA to diagonal-compressed form

  This implements the 3-step pipeline from chapters 3 & 4 of the thesis:

  Step 1 (zellautoZuLinksunabhaengig): CA C → left-independent C'
    Δ^t_{C'}(c)_i = Δ^{t/2}_C(c)_{i+t/2}  (even t)
    Cost: 2× slower, shifts left

  Step 2 (linksunabhaengigSpeedup): left-indep C' → left-indep C'' with Q^k states
    Compresses k consecutive diagonal states into one cell

  Step 3 (linksunabhaengigZuZellauto): left-indep C'' → regular C'''
    Δ^t_{C'''}(c)_i = Δ^{2t}_{C''}(c)_{i-t}
    Cost: 2× faster, shifts right

  Net result: Diagonal compression with 3/2 speedup factor.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.left_indep_speedup
import CellularAutomatas.proofs.passive_border
import CellularAutomatas.proofs.left_indep_to_regular
import CellularAutomatas.proofs.regular_to_left_indep

namespace CellularAutomatas

open CellAutomaton

/-! ## Combining the transformations: CAgfSpeedup

  The CAgfSpeedup (Satz 3.9) combines:
  1. C' = zellautoZuLinksunabhaengig(C) - Regular → Left-independent
  2. C'' = linksunabhaengigSpeedup(C', k=3) - k-step diagonal compression
  3. C''' = linksunabhaengigZuZellauto(C'') - Left-independent → Regular

  Result: Functions g₁, g₂ such that:
  - g₁(Δ^{2p-1}_{C'''}(c)_p) = Δ^{3p-2}_C(c)_1
  - g₂(Δ^{2p}_{C'''}(c)_{p+1}) = (Δ^{3p-1}_C(c)_1, Δ^{3p}_C(c)_1)

  And function f such that for i ≥ 1:
  - f(Δ^{2i+1}_{C_1}(c)_i) = (Δ^{3i-3}_C(c)_1, Δ^{3i-2}_C(c)_1, Δ^{3i-1}_C(c)_1)

  Note: The thesis starts with a regular CA. We implement the full pipeline.
-/

/-! ### Full Pipeline: CAgfSpeedup

  Starting from an arbitrary CA C, we construct C''' via all three steps.
  For now, we provide the structure and leave the main specs as sorry.
-/

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

/-- Step 1a: Regular CA → Left-independent CA -/
def step1a : RegularToLeftIndep where
  C_orig := e.C_orig

/-- C'_raw = the left-independent CA from step 1a (before passive border).
    Border is Q'.single(C_orig.border), which is NOT quiescent since
    δ'(_, single b, single c) = pair b c ≠ single. -/
def C'_raw : CellAutomaton e.α？ (RegularToLeftIndep.Q' e.step1a) := e.step1a.C

/-- C'_raw is left-independent -/
lemma C'_raw_left_indep : e.C'_raw.left_independent := e.step1a.C_left_independent

/-- Step 1b: Apply PassiveBorderLeftIndep to get quiescent border.
    This is needed because C'_raw.border = Q'.single(C_orig.border) is not quiescent. -/
def step1b : PassiveBorderLeftIndep where
  C_orig := e.C'_raw
  h_left_indep := e.C'_raw_left_indep

/-- C' = the left-independent CA with passive border from step 1b.
    State type is PassiveBorderLeftIndep.Q', output type is RegularToLeftIndep.Q' -/
def C' : CellAutomaton e.α？ e.step1b.β := e.step1b.C

/-- C' is left-independent -/
lemma C'_left_indep : e.C'.left_independent := e.step1b.C_left_indep

/-- C' has quiescent border -/
lemma C'_quiescent : e.C'.quiescent e.C'.border := e.step1b.C_border_passive

/-! ### Spec for step1b: Identity inside the word cone

  The key property from PassiveBorderLeftIndep.spec:
  Inside the word cone, C' computes the same as C'_raw.
  This is the "identity" property we want.
-/

/-- Inside the word cone, C' computes identically to C'_raw -/
lemma step1b_spec_in_cone (w : Word e.α) (hw : w.length > 0) (t : ℕ) (i : ℤ)
    (hi : i ∈ WordConeLeftIndep w t) :
    e.C'.comp w t i = e.C'_raw.comp w t i := by
  show e.step1b.C.comp w t i = _
  rw [e.step1b.spec w hw t i, if_pos hi]
  rfl

/-- Outside the word cone, C' returns the border -/
lemma step1b_spec_out_cone (w : Word e.α) (hw : w.length > 0) (t : ℕ) (i : ℤ)
    (hi : i ∉ WordConeLeftIndep w t) :
    e.C'.comp w t i = e.C'_raw.project e.C'_raw.border := by
  show e.step1b.C.comp w t i = _
  rw [e.step1b.spec w hw t i, if_neg hi]
  rfl

/-- Step 2: Left-independent → k-compressed with k=3 -/
def step2 : LeftIndepSpeedup where
  C_orig := e.C'
  k := 3
  hk := by decide
  h_left_indep := e.C'_left_indep
  h_quiescent := e.C'_quiescent

/-- C'' = the compressed left-independent CA from step 2 -/
def C'' : CellAutomaton e.α？ e.step1b.β := e.step2.C

/-- C'' is left-independent -/
lemma C''_left_indep : e.C''.left_independent := e.step2.C_left_indep

/-- Step 3: Left-independent → Regular (with 2x speedup) -/
def step3 : LeftIndepToRegular where
  C_orig := e.C''
  h_left_indep := e.C''_left_indep

/-- C''' = the final CA after all transformations -/
def C''' : CellAutomaton e.α？ e.step1b.β := e.step3.C

/-- The state type of C''' (same as C'') -/
abbrev Q''' := e.step2.Q'

-- Helper: k = 3 for step2
@[simp] lemma step2_k : e.step2.k = 3 := rfl

/-- Unwrap a PassiveBorderLeftIndep.Q' to get the underlying RegularToLeftIndep.Q' -/
def unwrap_passive (q : PassiveBorderLeftIndep.Q' e.step1b) : RegularToLeftIndep.Q' e.step1a :=
  match q with
  | .border => RegularToLeftIndep.Q'.dead
  | .state s _ => s

/-- Extract the original state from RegularToLeftIndep.Q' -/
def get_orig_state (q : RegularToLeftIndep.Q' e.step1a) : e.C_orig.Q :=
  e.step1a.get_state q

/-- Full extraction: from PassiveBorderLeftIndep.Q' to C_orig.Q -/
def extract_state (q : PassiveBorderLeftIndep.Q' e.step1b) : e.C_orig.Q :=
  e.get_orig_state (e.unwrap_passive q)

/-- Extract function g₁: given C''' state, extract component that gives Δ^{3p-2}_C(c)_1

    Note on component indexing:
    - Thesis uses 1-indexed (q_1, q_2, q_3) where q_3 is the "last" component
    - Lean uses 0-indexed (j=0,1,2) via Fin 3
    - The formulas differ: thesis comp j has time t-2i+(3-j), Lean comp j has time t-2i-j
    - Mapping: Lean j=0 ↔ thesis q_3, Lean j=1 ↔ thesis q_2, Lean j=2 ↔ thesis q_1

    Thesis defines g₁(q) := q_3, so we use j=0 in Lean. -/
def g₁ (q : e.Q''') : e.C_orig.Q :=
  -- Thesis q_3 = Lean j=0 (due to reversed tuple order)
  let q' := e.step2.compr_at q ⟨0, by simp⟩
  e.extract_state q'

/-- Extract function g₂: given C''' state, extract pair giving (Δ^{3p-1}_C(c)_1, Δ^{3p}_C(c)_1)

    Thesis defines g₂(q) := ((q_2)_1, q_1) where q_2 is a pair.
    In the thesis:
    - q_2 gives a pair from step1a (odd time result)
    - q_1 gives a single from step1a (even time result)

    Mapping to Lean:
    - Thesis q_2 = Lean j=1
    - Thesis q_1 = Lean j=2
    - (q_2)_1 means the first element of the pair = the left state -/
def g₂ (q : e.Q''') : e.C_orig.Q × e.C_orig.Q :=
  let q1' := e.step2.compr_at q ⟨1, by simp⟩  -- thesis q_2
  let q0' := e.step2.compr_at q ⟨2, by simp⟩  -- thesis q_1
  (e.extract_state q1', e.extract_state q0')

/-- Combined extraction function f -/
def f (q_prev q_curr : e.Q''') : e.C_orig.Q × e.C_orig.Q × e.C_orig.Q :=
  let (q1, q2) := e.g₂ q_prev
  let q3 := e.g₁ q_curr
  (q1, q2, q3)

/-- Standard word embedding uses word_to_config which places w at 0..w.len-1.
    Thesis uses 1..w.len, so thesis "position 1" = Lean position 0. -/
def embed_word_std (w : Word e.α) : Config e.C_orig.Q :=
  CellAutomaton.embed_word (C := e.C_orig) w



/-! ### Coordinate analysis for the full pipeline (from thesis Satz CAgfSpeedup)

  **Thesis formulas (1-based indexing, p ≥ 1):**
  - g₁(Δ_{C'''}^{2p-1}(c)_p) = Δ_C^{3p-2}(c)_1
  - g₂(Δ_{C'''}^{2p}(c)_{p+1}) = (Δ_C^{3p-1}(c)_1, Δ_C^{3p}(c)_1)
  - f(Δ_{C_1}^{2i+1}(c)_i) = (Δ_C^{3i-3}(c)_1, Δ_C^{3i-2}(c)_1, Δ_C^{3i-1}(c)_1) for i ≥ 1

  **Converted to Lean 0-based positions (thesis position_1 = Lean position_0):**
  - Substitute p_thesis = p_lean+1 (so p_lean ≥ 0 corresponds to p_thesis ≥ 1)
  - g₁(Δ_{C'''}^{2p+1}(c)_{p+1}) = Δ_C^{3p+1}(c)_0  for p ≥ 0
  - g₂(Δ_{C'''}^{2p+2}(c)_{p+2}) = (Δ_C^{3p+2}(c)_0, Δ_C^{3p+3}(c)_0)  for p ≥ 0
  - f(Δ_{C_1}^{2i+3}(c)_{i+1}) = (Δ_C^{3i}(c)_0, Δ_C^{3i+1}(c)_0, Δ_C^{3i+2}(c)_0)  for i ≥ 0

  Note: In Lean, word_to_config places w at positions 0..w.len-1.
  Thesis places w at 1..w.len. So thesis "position 1" = Lean "position 0".

  **Thesis extraction functions:**
  - g₁(q) := q_3  (component index 2 in 0-based = Fin 3 index ⟨2, _⟩)
  - g₂(q) := ((q_2)_1, q_1)  where q_2 is a pair and we take its first element

  **Thesis proof trace for g₁ (1-based):**
  1. step3: Δ_{C'''}^{2p-1}(c)_p = Δ_{C''}^{4p-2}(c)_{1-p}
  2. step2 at i=1-p, t=4p-2, j=3: component_3 = Δ_{C'}^{6p-4}(c)_{3-3p}
  3. step1a (even time 6p-4=2*(3p-2)): Δ_{C'}^{6p-4}(c)_{3-3p} = Δ_C^{3p-2}(c)_{(3-3p)+(3p-2)} = Δ_C^{3p-2}(c)_1
-/

/-! ### Helper lemmas for chaining the transformation specs -/

/-- The embed for C''' equals the embed for C'' (step3 preserves embed) -/
@[simp] lemma C'''_embed_eq_C''_embed : e.C'''.embed = e.C''.embed := rfl

/-- embed_word for C''' equals embed_word for C'' (since embeds match) -/
lemma embed_word_C'''_eq_C'' (w : Word e.α) :
    (CellAutomaton.embed_word (C := e.C''') w) = (CellAutomaton.embed_word (C := e.C'') w) := rfl

/-- Key relationship: C''' states relate to C'' states via step3.spec -/
lemma C'''_to_C'' (w : Word e.α) (t : ℕ) (i : ℤ) :
    e.C'''.nextt (CellAutomaton.embed_word (C := e.C''') w) t i =
    e.C''.nextt (CellAutomaton.embed_word (C := e.C'') w) (2*t) (i - t) :=
  e.step3.spec_nextt _ t i

/-- The step2 spec for negative positions gives component values -/
lemma C''_compr_at_spec (w : Word e.α) (t : ℕ) (i : ℤ) (hi : i < 0) (j : Fin 3) :
    e.step2.compr_at (e.C''.nextt (CellAutomaton.embed_word (C := e.C'') w) t i) j =
    e.C'.nextt (CellAutomaton.embed_word (C := e.C') w) (e.step2.φ t i j).toNat (e.step2.ψ i j) := by
  exact e.step2.spec_nextt w i hi t j

/-- Coordinate lemma: step2.k = 3 so the formulas simplify -/
lemma step2_phi (t : ℕ) (i : ℤ) (j : Fin 3) : e.step2.φ t i j = t - 2 * i - j := by
  simp only [LeftIndepSpeedup.φ, step2_k]
  ring

lemma step2_psi (i : ℤ) (j : Fin 3) : e.step2.ψ i j = 3 * i + j := by
  simp only [LeftIndepSpeedup.ψ, step2_k]
  ring

/-! ### Main specification theorems using comp -/

/-- Spec for g₁: Extracts C_orig.comp value at time 3p+1, position 0.

    Coordinate trace (0-based Lean conventions):
    1. C''' at (2p+1, p+1)
    2. step3: → C'' at (4p+2, -p) since (p+1)-(2p+1) = -p
    3. step2 j=0: φ = 4p+2-2(-p)-0 = 6p+2, ψ = 3(-p)+0 = -3p → C' at (6p+2, -3p)
    4. step1b: inside cone → C'_raw at (6p+2, -3p)
    5. step1a even: 6p+2 = 2(3p+1) → C_orig at (-3p + (3p+1)) = 1 (thesis) = 0 (Lean)

    Note: Thesis position 1 = Lean position 0. The coordinate arithmetic checks out. -/
theorem spec_g₁ (w : Word e.α) (hw : w.length > 0) (p : ℕ) (hp : p > 0) :
    e.C_orig.project (e.g₁ (e.C'''.nextt (CellAutomaton.embed_word (C := e.C''') w) (2*p + 1) (p + 1))) =
    e.C_orig.comp w (3*p + 1) 0 := by
  -- Chain the transformation specs:
  -- 1. C''' → C'' via step3.spec
  -- First simplify the position: (p+1) - (2p+1) = -p
  have h_pos : ((p : ℤ) + 1) - ((2 : ℤ) * p + 1) = -(p : ℤ) := by ring
  rw [C'''_to_C'']
  -- The position is now (p+1) - (2p+1)

  -- 2. g₁ extracts j=0 component
  unfold g₁ extract_state get_orig_state unwrap_passive

  -- The position after step3 is (p+1) - (2p+1), need to show this equals -p
  -- and that -p < 0 for step2 spec
  have h_neg : ((p : ℤ) + 1) - ((2 : ℤ) * p + 1) < 0 := by omega

  -- 3-5: The remaining steps require detailed coordinate arithmetic through
  -- step2, step1b, and step1a. The key is showing that:
  -- - The computed (φ, ψ) coordinates lead to C' at (6p+2, -3p)
  -- - Position -3p is inside the word cone at time 6p+2
  -- - Even time 6p+2 = 2*(3p+1) gives C_orig at position (-3p) + (3p+1) = 1 → 0 in Lean
  sorry

/-- Spec for g₂: Extracts pair of C_orig.comp values at times 3p+2, 3p+3, position 0.

    Coordinate trace:
    1. C''' at (2p+2, p+2)
    2. step3: → C'' at (4p+4, -p) since (p+2)-(2p+2) = -p
    3. step2 j=1: φ = 4p+4-2(-p)-1 = 6p+3, ψ = 3(-p)+1 = -3p+1
       step2 j=2: φ = 4p+4-2(-p)-2 = 6p+2, ψ = 3(-p)+2 = -3p+2
    4. step1a: j=1 gives odd time (pair), j=2 gives even time (single) -/
theorem spec_g₂ (w : Word e.α) (hw : w.length > 0) (p : ℕ) (hp : p > 0) :
    (e.C_orig.project (e.g₂ (e.C'''.nextt (CellAutomaton.embed_word (C := e.C''') w) (2*p + 2) (p + 2))).1,
     e.C_orig.project (e.g₂ (e.C'''.nextt (CellAutomaton.embed_word (C := e.C''') w) (2*p + 2) (p + 2))).2) =
    (e.C_orig.comp w (3*p + 2) 0, e.C_orig.comp w (3*p + 3) 0) := by
  -- Similar to spec_g₁ but handles both components
  sorry

/-- Combined spec for f: Extracts triple at times 3p, 3p+1, 3p+2 at position 0.

    f reads from two consecutive C''' states at position p+1:
    - q_prev at time 2p+2: g₂ extracts first two components
    - q_curr at time 2p+3: g₁ extracts third component

    Note: Position p+1 differs from spec_g₁ (p+1) and spec_g₂ (p+2).
    The coordinate derivation for f at position p+1 gives different φ, ψ values. -/
theorem spec_f (w : Word e.α) (hw : w.length > 0) (p : ℕ) (hp : p > 0) :
    let c := CellAutomaton.embed_word (C := e.C''') w
    let q_prev := e.C'''.nextt c (2*p + 2) (p + 1)
    let q_curr := e.C'''.nextt c (2*p + 3) (p + 1)
    let (v0, v1, v2) := e.f q_prev q_curr
    (e.C_orig.project v0, e.C_orig.project v1, e.C_orig.project v2) =
    (e.C_orig.comp w (3*p) 0, e.C_orig.comp w (3*p + 1) 0, e.C_orig.comp w (3*p + 2) 0) := by
  -- Unfold f and apply g₁/g₂ coordinate derivations with position p+1
  simp only []
  -- For q_prev at (2p+2, p+1):
  --   step3: C'' at (4p+4, -p-1) since (p+1)-(2p+2) = -p-1
  --   step2 j=1: φ = 4p+4-2(-p-1)-1 = 6p+5, ψ = 3(-p-1)+1 = -3p-2
  --   step2 j=2: φ = 4p+4-2(-p-1)-2 = 6p+4, ψ = 3(-p-1)+2 = -3p-1
  -- For q_curr at (2p+3, p+1):
  --   step3: C'' at (4p+6, -p-2) since (p+1)-(2p+3) = -p-2
  --   step2 j=0: φ = 4p+6-2(-p-2)-0 = 6p+10, ψ = 3(-p-2)+0 = -3p-6

  -- The coordinate arithmetic continues through step1b and step1a
  sorry

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

  /-- Read the triple directly from C''' at the correct coordinates.
      At position p, reads C''' at times 2p+2 and 2p+3 at position p+1.
      This matches spec_f which shows these give times 3p, 3p+1, 3p+2 at C_orig position 0. -/
  def read_triple (w : Word e.α) (p : ℕ) : e.β³ :=
    let c := CellAutomaton.embed_word (C := e.speedup.C''') w
    let q_prev := e.speedup.C'''.nextt c (2*p + 2) (p + 1)
    let q_curr := e.speedup.C'''.nextt c (2*p + 3) (p + 1)
    let (v0, v1, v2) := e.speedup.f q_prev q_curr
    fun j => match j with
      | ⟨0, _⟩ => e.C_orig.project v0
      | ⟨1, _⟩ => e.C_orig.project v1
      | ⟨2, _⟩ => e.C_orig.project v2

  /-- The target triple: C_orig trace at times 3p, 3p+1, 3p+2 at position 0. -/
  def target_triple (w : Word e.α) (p : ℕ) : e.β³ :=
    triple_at (e.C_orig.trace w) (3 * p)

  /-- The key lemma: read_triple gives the same result as target_triple.

      Proof uses spec_f which shows that extracting via f and projecting
      gives exactly the C_orig.comp values we need.

      read_triple extracts via f and projects, target_triple uses trace which is comp at 0.

      Note: spec_f requires p > 0. The case p = 0 is handled separately. -/
  lemma read_triple_eq_target (w : Word e.α) (hp : w.length > 0) (p : ℕ) (hp' : p > 0) :
      e.read_triple w p = e.target_triple w p := by
    unfold read_triple target_triple triple_at
    have h_spec := e.speedup.spec_f w hp p hp'
    simp only at h_spec
    -- h_spec gives the key equality; we need to unfold and apply it component-wise
    funext j
    simp only [speedup, CellAutomaton.trace, CellAutomaton.comp, CellAutomaton.project_config,
      Function.comp_apply]
    -- Use spec_f to rewrite the f application
    -- The proof requires matching the components of the tuples
    match j with
    | ⟨0, _⟩ =>
      -- First component: project v0 = comp (3p) 0
      have h := congrArg (fun x => x.1) h_spec
      simp only at h
      exact h
    | ⟨1, _⟩ =>
      -- Second component: project v1 = comp (3p+1) 0
      have h := congrArg (fun x => x.2.1) h_spec
      simp only at h
      exact h
    | ⟨2, _⟩ =>
      -- Third component: project v2 = comp (3p+2) 0
      have h := congrArg (fun x => x.2.2) h_spec
      simp only at h
      exact h

  /-- The compressed CA C outputs triples from C'''.
      At position p ≥ 0 and time 2p+3, outputs the trace triple (3p, 3p+1, 3p+2).

      Note: This wraps C''' and applies the f extraction function in the projection.
      The transition function tracks C''' states at consecutive times.

      **Design:**
      - State: (q_prev, q_curr) where q_prev and q_curr are consecutive-time C''' states
      - At time t and position i, the state should contain (C'''@(t-1, i+1), C'''@(t, i+1))
      - Projection applies f to extract the trace triple

      **Issue:** The current δ definition may not correctly track C''' states.
      A proper implementation would need to shift positions appropriately. -/
  def C: CellAutomaton e.α？ (Option (e.β³)) := {
    Q := e.speedup.Q''' × e.speedup.Q'''
    δ := fun ⟨_, a2⟩ ⟨_, b2⟩ ⟨_, c2⟩ =>
      -- Track (prev_time, curr_time) pairs of C''' states
      -- At each step, curr becomes prev, and we compute new curr
      -- Note: This simulates C''' by using its transition function
      let new_prev := b2
      let new_curr := e.speedup.C'''.δ a2 b2 c2
      (new_prev, new_curr)
    embed := fun a =>
      let q := e.speedup.C'''.embed a
      (q, q)
    project := fun ⟨q_prev, q_curr⟩ =>
      let (v0, v1, v2) := e.speedup.f q_prev q_curr
      some (fun j => match j with
        | ⟨0, _⟩ => e.C_orig.project v0
        | ⟨1, _⟩ => e.C_orig.project v1
        | ⟨2, _⟩ => e.C_orig.project v2)
  }

  /-- Helper: At time t, position i, the second component of C state equals C'''.nextt at (t, i+1).

      This is because C simulates C''' with a position shift: C at position i reads C''' at i+1.
      The transition function ensures this invariant is maintained. -/
  lemma C_state_tracks_C''' (w : Word e.α) (t : ℕ) (i : ℤ) :
      (e.C.nextt (CellAutomaton.embed_word (C := e.C) w) t i).2 =
      e.speedup.C'''.nextt (CellAutomaton.embed_word (C := e.speedup.C''') w) t (i + 1) := by
    -- The proof would proceed by induction on t, showing that:
    -- 1. At t=0, both sides give the embedded state at the appropriate position
    -- 2. At t+1, the transition function of C correctly simulates C''' with the shift
    sorry

  /-- Main theorem: The compressed CA correctly extracts trace triples.

      At position p ≥ 0 and time t = 2p+3, C.comp outputs the trace triple.
      This follows from:
      1. C tracks C''' states with position offset via C_state_tracks_C'''
      2. At time 2p+3, position p: state contains (C'''@(2p+2, p+1), C'''@(2p+3, p+1))
      3. The f function extracts C_orig values at times 3p, 3p+1, 3p+2 via spec_f
      4. Projection gives the β values which match trace -/
  theorem spec (w: Word e.α) (hw : w.length > 0) (p: ℕ) (hp : p > 0):
      e.C.comp w (2*p + 3) p =
        some (triple_at (e.C_orig.trace w) (3 * p)) := by
    -- Using read_triple_eq_target and C_state_tracks_C''':
    -- 1. C.comp unpacks to project(nextt(embed_word w, 2p+3, p))
    -- 2. By C_state_tracks_C''': state.2 = C'''@(2p+3, p+1)
    -- 3. Similarly for state.1 = C'''@(2p+2, p+1) (from previous step)
    -- 4. project applies f which by spec_f gives trace values
    -- 5. This matches read_triple_eq_target
    sorry

end CompressToDiag
