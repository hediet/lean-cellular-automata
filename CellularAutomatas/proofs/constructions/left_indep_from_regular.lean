/-
  RegularToLeftIndep: Regular CA to Left-Independent CA (zellautoZuLinksunabhaengig)

  Given any CA C, construct left-independent C' where:
    Δ^t_{C'}(c)_i = Δ^{t/2}_C(c)_{i+t/2}     (if t even)
                  = (Δ^{(t-1)/2}_C, Δ^{(t-1)/2}_C)_{i+(t-1)/2, i+(t+1)/2}  (if t odd)

  Q' = Q ∪ Q×Q
  δ'(_, b, c) = (b, c)           when b, c ∈ Q
  δ'(_, (b₁,b₂), (c₁,c₂)) = δ(b₁, b₂, c₂)  when inputs are pairs
-/

import CellularAutomatas.defs
import CellularAutomatas.internal_defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

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

/-- Project Q' to BetaUnionSq β. Dead maps to single with default value. -/
def projectQ' : Q' e → BetaUnionSq e.β
  | .single q => .single (e.C_orig.project q)
  | .pair q1 q2 => .pair (e.C_orig.project q1) (e.C_orig.project q2)
  | .dead => .single default

/-- The left-independent CA C' -/
def C : CellAutomaton e.α (BetaUnionSq e.β) := {
  Q := Q' e
  δ := e.δ'
  embed := fun a => .single (e.C_orig.embed a)
  project := e.projectQ'
}

/-- C' is left-independent -/
lemma C_left_independent : e.C.left_independent := by
  intro q1 q2 q3 q1'
  unfold C δ'
  cases q2 <;> cases q3 <;> rfl

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

theorem spec_even (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c (2*t) i = .single (e.C_orig.comp c t (i + t)) := by
  have eq_config : (embed_config (C := e.C) c) = fun j => Q'.single (embed_config (C := e.C_orig) c j) := rfl
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold, Function.comp_apply, C, projectQ',
    eq_config]
  have h := (spec_combined e (embed_config c) t i).1
  simp only [C] at h
  rw [h]

theorem spec_odd (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c (2*t + 1) i = .pair (e.C_orig.comp c t (i + t)) (e.C_orig.comp c t (i + t + 1)) := by
  have eq_config : (embed_config (C := e.C) c) = fun j => Q'.single (embed_config (C := e.C_orig) c j) := rfl
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold, Function.comp_apply, C, projectQ',
    eq_config]
  have h := (spec_combined e (embed_config c) t i).2
  simp only [C] at h
  rw [h]


theorem spec (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c t i =
      if t % 2 = 0 then
        .single (e.C_orig.comp c (t / 2) (i + t / 2))
      else
        .pair (e.C_orig.comp c (t / 2) (i + t / 2)) (e.C_orig.comp c (t / 2) (i + t / 2 + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · -- t % 2 = 0 (even case)
    simp only [h, ↓reduceIte]
    have hk : t = 2 * (t / 2) := by omega
    conv_lhs => rw [hk]
    exact spec_even e c (t / 2) i
  · -- t % 2 = 1 (odd case)
    simp only [h, one_ne_zero, ↓reduceIte]
    have hk : t = 2 * (t / 2) + 1 := by omega
    conv_lhs => rw [hk]
    exact spec_odd e c (t / 2) i

end RegularToLeftIndep

end CellularAutomatas
