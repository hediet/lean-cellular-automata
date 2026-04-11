/-
  LeftIndepToRegular: Left-Independent to Regular CA (linksunabhaengigZuZellauto)

  This is the simplest transformation. Given a left-independent CA C,
  we construct C' such that:
    Δ^t_{C'}(c)_i = Δ^{2t}_C(c)_{i-t}

  Key idea: Since C is left-independent, δ(a,b,c) = δ(q,b,c) for any q.
  Define δ'(a,b,c) := δ(q, δ(q,a,b), δ(q,b,c))
  This computes TWO steps of C in ONE step of C', shifting right by 1.
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

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
private lemma left_indep_subst (a a' b c : e.C_orig.Q) :
    e.C_orig.δ a b c = e.C_orig.δ a' b c :=
  e.h_left_indep a b c a'

/-- The transition function for C': δ'(a,b,c) = δ(q, δ(q,a,b), δ(q,b,c)) -/
private def δ' (a b c : e.C_orig.Q) : e.C_orig.Q :=
  e.C_orig.δ a (e.C_orig.δ a a b) (e.C_orig.δ a b c)

/-- The compressed CA C'. -/
def C : CellAutomaton e.α e.β := {
  Q := e.C_orig.Q
  δ := e.δ'
  embed := e.C_orig.embed
  project := e.C_orig.project
}

/-- One step of C' equals two steps of C_orig, shifted by 1 position. -/
private lemma one_step_shift (c : Config e.C_orig.Q) (i : ℤ) :
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

private theorem spec_nextt (c : Config e.C_orig.Q) (t : ℕ) (i : ℤ) :
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

theorem spec (c : Config e.α) (t : ℕ) (i : ℤ) :
    e.C.comp c t i = e.C_orig.comp c (2 * t) (i - t) := by
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold]
  congr 1
  exact spec_nextt e ⦋c⦌ t i

attribute [irreducible] C

end LeftIndepToRegular

end CellularAutomatas
