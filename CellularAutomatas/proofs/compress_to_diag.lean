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
import CellularAutomatas.proofs.composition
import CellularAutomatas.proofs.left_indep_speedup

namespace CellularAutomatas

open CellAutomaton

/-! ## Step 3: Left-Independent to Regular CA (linksunabhaengigZuZellauto)

  This is the simplest transformation. Given a left-independent CA C,
  we construct C' such that:
    Δ^t_{C'}(c)_i = Δ^{2t}_C(c)_{i-t}

  Key idea: Since C is left-independent, δ(a,b,c) = δ(q,b,c) for any q.
  Define δ'(a,b,c) := δ(q, δ(q,a,b), δ(q,b,c))
  This computes TWO steps of C in ONE step of C', shifting right by 1.
-/

structure LeftIndepToRegular where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α β
  h_left_indep : C_orig.left_independent

attribute [instance] LeftIndepToRegular._inst_α
attribute [instance] LeftIndepToRegular._inst_β

namespace LeftIndepToRegular

variable (e : LeftIndepToRegular)

/-- Since C is left-independent, we can substitute any value for the left neighbor. -/
lemma left_indep_subst (a a' b c : e.C_orig.Q) :
    e.C_orig.δ a b c = e.C_orig.δ a' b c :=
  e.h_left_indep a b c a'

/-- The transition function for C': δ'(a,b,c) = δ(q, δ(q,a,b), δ(q,b,c)) -/
def δ' (a b c : e.C_orig.Q) : e.C_orig.Q :=
  e.C_orig.δ a (e.C_orig.δ a a b) (e.C_orig.δ a b c)

/-- The compressed CA C'. -/
def C : CellAutomaton e.α e.β := {
  Q := e.C_orig.Q
  δ := e.δ'
  embed := e.C_orig.embed
  project := e.C_orig.project
}

/-- One step of C' equals two steps of C_orig, shifted by 1 position. -/
lemma one_step_shift (c : Config e.C_orig.Q) (i : ℤ) :
    e.C.next c i = e.C_orig.nextt c 2 (i - 1) := by
  unfold CellAutomaton.next C δ'
  simp only [CellAutomaton.nextt_succ, CellAutomaton.nextt_zero]
  unfold CellAutomaton.next
  -- LHS: δ(c(i-1), δ(c(i-1), c(i-1), c(i)), δ(c(i-1), c(i), c(i+1)))
  -- RHS: δ(δ(c(i-3), c(i-2), c(i-1)), δ(c(i-2), c(i-1), c(i)), δ(c(i-1), c(i), c(i+1)))
  -- By left-independence, can substitute left arguments freely
  rw [left_indep_subst e (c (i-1)) (e.C_orig.δ (c (i-1-1-1)) (c (i-1-1)) (c (i-1)))]
  rw [left_indep_subst e (c (i-1)) (c (i-1-1)) (c (i-1)) (c i)]
  ring_nf

/-- Main theorem: t steps of C' at i = 2t steps of C_orig at i-t -/
theorem spec (c : Config e.C_orig.Q) (t : ℕ) (i : ℤ) :
    e.C.nextt c t i = e.C_orig.nextt c (2 * t) (i - t) := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, one_step_shift]
    have h_eq : ∀ j, e.C.nextt c t j = e.C_orig.nextt c (2*t) (j - t) := fun j => ih j
    have h_config : e.C.nextt c t = fun j => e.C_orig.nextt c (2*t) (j - t) := by
      funext j; exact h_eq j
    rw [h_config]
    -- Goal: nextt (fun j => nextt c (2*t) (j - t)) 2 (i-1) = nextt c (2*(t+1)) (i-(t+1))
    -- Step 1: Use nextt_shift to rewrite LHS config
    have h1 : (fun j => e.C_orig.nextt c (2*t) (j - t)) =
              e.C_orig.nextt (fun i => c (i - t)) (2*t) := by
      funext j
      have := nextt_shift e.C_orig c (2*t) j (-t)
      simp at this
      exact this
    rw [h1]
    -- Step 2: Use nextt_add to combine steps
    rw [← nextt_add]
    -- Step 3: Use nextt_shift to match RHS
    have h2 : (i : ℤ) - (t + 1 : ℕ) = (i - 1) + (-t : ℤ) := by push_cast; ring
    rw [h2, show 2 * (t + 1) = 2 * t + 2 by ring]
    rw [nextt_shift]
    apply nextt_locality
    intro y _
    ring_nf

/-- Corollary for embedded configurations. -/
theorem spec_comp (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c t i = e.C_orig.comp c (2 * t) (i - t) := by
  unfold CellAutomaton.comp CellAutomaton.project_config
  simp only [Function.comp_apply]
  congr 1
  exact spec e ⦋c⦌ t i

end LeftIndepToRegular

/-! ## Step 1: Regular CA to Left-Independent CA (zellautoZuLinksunabhaengig)

  Given any CA C, construct left-independent C' where:
    Δ^t_{C'}(c)_i = Δ^{t/2}_C(c)_{i+t/2}     (if t even)
                  = (Δ^{(t-1)/2}_C, Δ^{(t-1)/2}_C)_{i+(t-1)/2, i+(t+1)/2}  (if t odd)

  Q' = Q ∪ Q×Q
  δ'(_, b, c) = (b, c)           when b, c ∈ Q
  δ'(_, (b₁,b₂), (c₁,c₂)) = δ(b₁, b₂, c₂)  when inputs are pairs
-/

structure RegularToLeftIndep where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α β

attribute [instance] RegularToLeftIndep._inst_α
attribute [instance] RegularToLeftIndep._inst_β

namespace RegularToLeftIndep

variable (e : RegularToLeftIndep)

/-- State space: Either a single state, a pair of states, or a dead (quiescent) border state -/
inductive Q'
  | single : e.C_orig.Q → Q'
  | pair : e.C_orig.Q → e.C_orig.Q → Q'
  | dead : Q'  -- Quiescent border state: δ'(dead, dead, dead) = dead
  deriving DecidableEq

instance : Inhabited (Q' e) := ⟨Q'.dead⟩

instance : Fintype (Q' e) :=
  Fintype.ofEquiv (e.C_orig.Q ⊕ (e.C_orig.Q × e.C_orig.Q) ⊕ Unit)
    { toFun := fun
        | .inl q => Q'.single q
        | .inr (.inl (q1, q2)) => Q'.pair q1 q2
        | .inr (.inr ()) => Q'.dead
      invFun := fun
        | Q'.single q => .inl q
        | Q'.pair q1 q2 => .inr (.inl (q1, q2))
        | Q'.dead => .inr (.inr ())
      left_inv := fun x => by rcases x with _ | (_ | _) <;> rfl
      right_inv := fun x => by cases x <;> rfl }

/-- Transition function: left-independent by construction.
    The dead state is quiescent: δ'(_, dead, dead) = dead -/
def δ' : Q' e → Q' e → Q' e → Q' e
  | _, .dead, .dead => .dead  -- Quiescent border
  | _, .single b, .single c => .pair b c
  | _, .pair b1 b2, .pair _ c2 => .single (e.C_orig.δ b1 b2 c2)
  | _, _, _ => .dead  -- Invalid transitions go to dead state

/-- The left-independent CA C' -/
def C : CellAutomaton e.α (Q' e) := {
  Q := Q' e
  δ := e.δ'
  embed := fun a => .single (e.C_orig.embed a)
  project := id
}

/-- C' is left-independent -/
lemma C_left_independent : e.C.left_independent := by
  intro q1 q2 q3 q1'
  unfold C δ'
  cases q2 <;> cases q3 <;> rfl

/-- Extract the first component from Q' when we know the time parity.
    For dead state, returns default (shouldn't happen in valid word computation). -/
def get_state : Q' e → e.C_orig.Q
  | .single q => q
  | .pair q _ => q
  | .dead => default

/-- Combined spec: even times give single with shifted value, odd times give pairs -/
theorem spec_combined (c : Config e.C_orig.Q) (t : ℕ) (i : ℤ) :
    (e.C.nextt (fun j => Q'.single (c j)) (2*t) i = Q'.single (e.C_orig.nextt c t (i + t))) ∧
    (e.C.nextt (fun j => Q'.single (c j)) (2*t + 1) i =
      Q'.pair (e.C_orig.nextt c t (i + t)) (e.C_orig.nextt c t (i + t + 1))) := by
  induction t generalizing i with
  | zero =>
    constructor
    · simp only [mul_zero, Nat.cast_zero, CellAutomaton.nextt_zero, add_zero]
    · simp only [mul_zero, Nat.cast_zero, CellAutomaton.nextt_zero, add_zero, zero_add]
      rfl
  | succ t ih =>
    -- Get both even and odd IH for needed positions
    have hL_odd := (ih (i - 1)).2
    have hM_odd := (ih i).2
    have hR_odd := (ih (i + 1)).2
    constructor
    · -- Even case: 2(t+1) = 2t + 2
      -- At time 2t+1, we have pairs. Applying δ' to pairs gives single.
      rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring]
      rw [CellAutomaton.nextt_succ]
      show e.δ' (e.C.nextt _ (2*t+1) (i-1)) (e.C.nextt _ (2*t+1) i) (e.C.nextt _ (2*t+1) (i+1)) = _
      rw [hL_odd, hM_odd, hR_odd]
      show Q'.single (e.C_orig.δ _ _ _) = Q'.single (e.C_orig.nextt c (t+1) (i + (t+1)))
      rw [CellAutomaton.nextt_succ]
      show Q'.single (e.C_orig.δ _ _ _) = Q'.single (e.C_orig.next (e.C_orig.nextt c t) _)
      unfold CellAutomaton.next
      congr 2 <;> ring_nf
    · -- Odd case: 2(t+1)+1 = (2(t+1)) + 1
      -- At time 2(t+1), we have singles. Applying δ' to singles gives pairs.
      rw [show 2 * (t + 1) + 1 = (2 * (t + 1)) + 1 by ring]
      rw [CellAutomaton.nextt_succ]

      -- Show that at time 2(t+1), neighboring cells are singles
      have h_step : ∀ j, e.C.nextt (fun j => Q'.single (c j)) (2*(t+1)) j =
          Q'.single (e.C_orig.nextt c (t+1) (j + (t+1))) := by
        intro j
        rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring, CellAutomaton.nextt_succ]
        show e.δ' _ _ _ = _
        rw [(ih (j-1)).2, (ih j).2, (ih (j+1)).2]
        show Q'.single _ = _
        rw [CellAutomaton.nextt_succ]
        unfold CellAutomaton.next
        congr 2 <;> ring_nf

      show e.δ' _ _ _ = Q'.pair _ _
      rw [h_step (i-1), h_step i, h_step (i+1)]
      show Q'.pair _ _ = Q'.pair _ _
      congr 1
      push_cast
      ring_nf

/-- Main spec for even times -/
theorem spec_even (c : Config e.C_orig.Q) (t : ℕ) (i : ℤ) :
    e.get_state (e.C.nextt (fun j => Q'.single (c j)) (2*t) i) = e.C_orig.nextt c t (i + t) := by
  rw [(spec_combined e c t i).1]
  rfl

/-- Main spec for odd times -/
theorem spec_odd (c : Config e.C_orig.Q) (t : ℕ) (i : ℤ) :
    e.C.nextt (fun j => Q'.single (c j)) (2*t + 1) i =
      Q'.pair (e.C_orig.nextt c t (i + t)) (e.C_orig.nextt c t (i + t + 1)) :=
  (spec_combined e c t i).2

end RegularToLeftIndep

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
  C_orig : CellAutomaton α β

attribute [instance] CAgfSpeedup._inst_α
attribute [instance] CAgfSpeedup._inst_β

namespace CAgfSpeedup

variable (e : CAgfSpeedup)

/-- Step 1: Regular CA → Left-independent CA -/
def step1 : RegularToLeftIndep where
  C_orig := e.C_orig

/-- C' = the left-independent CA from step 1 -/
def C' : CellAutomaton e.α (RegularToLeftIndep.Q' e.step1) := e.step1.C

/-- C' is left-independent -/
lemma C'_left_indep : e.C'.left_independent := e.step1.C_left_independent

/-- C' with optional alphabet wrapper for step 2.
    The border is the dead state which is quiescent by construction.
-/
def C'_opt : CellAutomaton e.α？ (RegularToLeftIndep.Q' e.step1) := {
  Q := e.C'.Q
  δ := e.C'.δ
  embed := fun a => match a with
    | some a' => e.C'.embed a'
    | none => RegularToLeftIndep.Q'.dead  -- border = embed none = dead (quiescent)
  project := e.C'.project
}

/-- C'_opt is left-independent -/
lemma C'_opt_left_indep : e.C'_opt.left_independent := by
  intro a b c a'
  exact e.C'_left_indep a b c a'

/-- C'_opt has quiescent border (dead state is quiescent by construction) -/
lemma C'_opt_quiescent : e.C'_opt.quiescent e.C'_opt.border := by
  unfold CellAutomaton.quiescent CellAutomaton.quiescent_set CellAutomaton.border
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  simp only [Set.mem_singleton_iff] at ha hb hc
  subst ha hb hc
  simp only [C'_opt, C', step1, RegularToLeftIndep.C, RegularToLeftIndep.δ']
  -- δ'(dead, dead, dead) = dead by definition
  rfl

/-- Step 2: Left-independent → k-compressed with k=3 -/
def step2 : LeftIndepSpeedup where
  C_orig := e.C'_opt
  k := 3
  hk := by decide
  h_left_indep := e.C'_opt_left_indep
  h_quiescent := e.C'_opt_quiescent

/-- C'' = the compressed left-independent CA from step 2 -/
def C'' : CellAutomaton e.α？ (RegularToLeftIndep.Q' e.step1) := e.step2.C

/-- C'' is left-independent -/
lemma C''_left_indep : e.C''.left_independent := e.step2.C_left_indep

/-- Step 3: Left-independent → Regular (with 2x speedup) -/
def step3 : LeftIndepToRegular where
  C_orig := e.C''
  h_left_indep := e.C''_left_indep

/-- C''' = the final CA after all transformations -/
def C''' : CellAutomaton e.α？ (RegularToLeftIndep.Q' e.step1) := e.step3.C

/-- The state type of C''' (same as C'') -/
abbrev Q''' := e.step2.Q'

-- Helper: k = 3 for step2
@[simp] lemma step2_k : e.step2.k = 3 := rfl

/-- Extract function g₁: given C''' state, extract component that gives Δ^{3p-2}_C(c)_1 -/
def g₁ (q : e.Q''') : e.C_orig.Q :=
  -- Takes the 3rd component (j=2), then extracts from the pair
  let q' := e.step2.compr_at q ⟨2, by simp⟩
  e.step1.get_state q'

/-- Extract function g₂: given C''' state, extract pair giving (Δ^{3p-1}_C(c)_1, Δ^{3p}_C(c)_1) -/
def g₂ (q : e.Q''') : e.C_orig.Q × e.C_orig.Q :=
  let q1' := e.step2.compr_at q ⟨1, by simp⟩
  let q0' := e.step2.compr_at q ⟨0, by simp⟩
  (e.step1.get_state q1', e.step1.get_state q0')

/-- Combined extraction function f -/
def f (q_prev q_curr : e.Q''') : e.C_orig.Q × e.C_orig.Q × e.C_orig.Q :=
  let (q1, q2) := e.g₂ q_prev
  let q3 := e.g₁ q_curr
  (q1, q2, q3)

/-- Helper: embed a word into C_orig's state space -/
def embed_word_orig (w : Word e.α) : Config e.C_orig.Q :=
  e.C_orig.embed_config (fun i => if 0 ≤ i ∧ i < w.length then w.getD i.toNat default else default)

/-- Main spec theorem for g₁: g₁(Δ^{2p-1}_{C'''}(c)_p) = Δ^{3p-2}_C(c)_1 for p ≥ 1

  The full proof requires composing the three specs:
  1. step1.spec_even: relates C' to C_orig
  2. step2.spec: relates C'' to C'
  3. step3.spec: relates C''' to C''
-/
theorem spec_g₁ (w : Word e.α) (p : ℕ) (hp : p ≥ 1) :
    e.g₁ (e.C'''.nextt (CellAutomaton.embed_word (C := e.C''') w) (2*p - 1) p) =
    e.C_orig.nextt (e.embed_word_orig w) (3*p - 2) 1 := by
  sorry

/-- Main spec theorem for g₂ -/
theorem spec_g₂ (w : Word e.α) (p : ℕ) (hp : p ≥ 1) :
    e.g₂ (e.C'''.nextt (CellAutomaton.embed_word (C := e.C''') w) (2*p) (p + 1)) =
    (e.C_orig.nextt (e.embed_word_orig w) (3*p - 1) 1,
     e.C_orig.nextt (e.embed_word_orig w) (3*p) 1) := by
  sorry

/-- Combined spec: f extracts three consecutive values at position 1 -/
theorem spec_f (w : Word e.α) (i : ℕ) (hi : i ≥ 1) :
    e.f (e.C'''.nextt (CellAutomaton.embed_word (C := e.C''') w) (2*i) i)
        (e.C'''.nextt (CellAutomaton.embed_word (C := e.C''') w) (2*i + 1) i) =
    (e.C_orig.nextt (e.embed_word_orig w) (3*i - 3) 1,
     e.C_orig.nextt (e.embed_word_orig w) (3*i - 2) 1,
     e.C_orig.nextt (e.embed_word_orig w) (3*i - 1) 1) := by
  sorry

end CAgfSpeedup
