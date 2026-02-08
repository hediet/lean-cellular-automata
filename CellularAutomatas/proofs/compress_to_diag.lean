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
import CellularAutomatas.proofs.left_indep_speedup2

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

/-- State space: Either a single state or a pair of states -/
inductive Q'
  | single : e.C_orig.Q → Q'
  | pair : e.C_orig.Q → e.C_orig.Q → Q'
  deriving DecidableEq

instance : Inhabited (Q' e) := ⟨Q'.single default⟩

instance : Fintype (Q' e) :=
  Fintype.ofEquiv (e.C_orig.Q ⊕ (e.C_orig.Q × e.C_orig.Q))
    { toFun := fun
        | .inl q => Q'.single q
        | .inr (q1, q2) => Q'.pair q1 q2
      invFun := fun
        | Q'.single q => .inl q
        | Q'.pair q1 q2 => .inr (q1, q2)
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun x => by cases x <;> rfl }

/-- Transition function: left-independent by construction -/
def δ' : Q' e → Q' e → Q' e → Q' e
  | _, .single b, .single c => .pair b c
  | _, .pair b1 b2, .pair _ c2 => .single (e.C_orig.δ b1 b2 c2)
  | _, _, _ => .pair default default  -- shouldn't happen in valid execution

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

/-- Extract the first component from Q' when we know the time parity -/
def get_state : Q' e → e.C_orig.Q
  | .single q => q
  | .pair q _ => q

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
      congr 2 <;> (push_cast; ring)
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
        congr 2 <;> (push_cast; ring)

      show e.δ' _ _ _ = Q'.pair _ _
      rw [h_step (i-1), h_step i, h_step (i+1)]
      show Q'.pair _ _ = Q'.pair _ _
      congr 1 <;> (push_cast; ring)

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

/-! ## Combining the transformations: The Full Pipeline

  For an arbitrary CA C, the full pipeline is:

  C  --Step1-->  C'  --Step2-->  C''  --Step3-->  C'''

  Where:
  - Step 1: C → left-independent C' (2× slower, shifts left)
  - Step 2: C' → left-independent C'' with Q^k states (k× compression)
  - Step 3: C'' → regular C''' (2× faster, shifts right)

  The final result C''' satisfies (for k=3):
    g₁(Δ^{2p-1}_{C'''}(c)_p) = Δ^{3p-2}_C(c)_1
    g₂(Δ^{2p}_{C'''}(c)_{p+1}) = (Δ^{3p-1}_C(c)_1, Δ^{3p}_C(c)_1)

  This gives a 3/2 speedup with diagonal movement.
-/

/-- Full pipeline: Regular CA → compressed diagonal form (Steps 1 + 3 only for now) -/
def compressToDiagonal {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) : CellAutomaton α (RegularToLeftIndep.Q' ⟨C⟩) :=
  let step1 : RegularToLeftIndep := ⟨C⟩
  let step3 : LeftIndepToRegular := ⟨step1.C, step1.C_left_independent⟩
  step3.C

/-- The embedding from input alphabet to Q' states -/
def compressToDiagonal_embed {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config α) : Config (RegularToLeftIndep.Q' ⟨C⟩) :=
  fun j => RegularToLeftIndep.Q'.single (C.embed (c j))

/-- Full pipeline specification:
    t steps of the compressed CA at position i equals t steps of original CA at position i.
    The left-shift from Step 1 exactly cancels the right-shift from Step 3!

    Proof is by composing:
    - Step 3 spec: C'''.nextt c' t i = C'.nextt c' (2*t) (i - t)
    - Step 1 spec: C'.nextt (embed c) (2*t) i = single(C.nextt c t (i + t))

    Substituting i' = i - t in Step 1:
      C'.nextt (embed c) (2*t) (i - t) = single(C.nextt c t (i - t + t)) = single(C.nextt c t i)
-/
theorem compressToDiagonal_spec {α β : Type} [Alphabet α] [Alphabet β]
    (C : CellAutomaton α β) (c : Config α) (t : ℕ) (i : ℤ) :
    (compressToDiagonal C).nextt (compressToDiagonal_embed C c) t i =
    RegularToLeftIndep.Q'.single (C.nextt ⦋c⦌ t i) := by
  -- Unfold the pipeline construction
  let step1 : RegularToLeftIndep := ⟨C⟩
  let step3 : LeftIndepToRegular := ⟨step1.C, step1.C_left_independent⟩

  -- The compressed CA is step3.C
  show step3.C.nextt (fun j => RegularToLeftIndep.Q'.single (C.embed (c j))) t i =
       RegularToLeftIndep.Q'.single (C.nextt ⦋c⦌ t i)

  -- Step 3 spec: t steps of step3.C = 2*t steps of step1.C shifted right by t
  rw [step3.spec]

  -- Now we need: step1.C.nextt (embed c) (2*t) (i - t) = single(C.nextt (embed c) t i)
  -- This follows from step1.spec_combined with position (i - t)
  have h := (step1.spec_combined ⦋c⦌ t (i - t)).1
  -- h says: step1.C.nextt (embed c) (2*t) (i - t) = single(C.nextt (embed c) t (i - t + t))
  simp only [sub_add_cancel] at h
  exact h

end CellularAutomatas
