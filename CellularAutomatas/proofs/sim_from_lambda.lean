import CellularAutomatas.defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import CellularAutomatas.proofs.basic


namespace CellularAutomatas

open CellAutomaton

structure SimFromΛ where
  {α: Type}
  {β: Type}
  {γ: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [_inst_γ: Alphabet γ]
  C_ctl: CellAutomaton α β？
  C_inr: CellAutomaton β γ

attribute [instance] SimFromΛ._inst_α
attribute [instance] SimFromΛ._inst_β
attribute [instance] SimFromΛ._inst_γ

namespace SimFromΛ
  variable (e: SimFromΛ)

  structure Q where
    state: e.C_ctl.Q
    counter: Fin 3
    sim: Option (e.C_inr.Q × e.C_inr.Q)
  deriving Inhabited, DecidableEq

  -- TODO@hediet - why cannot I derive Fintype automatically here?
  instance : Fintype (Q e) :=
    Fintype.ofEquiv (e.C_ctl.Q × Fin 3 × Option (e.C_inr.Q × e.C_inr.Q))
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun x => (x.state, x.counter, x.sim)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

  def get_neighbor_val (q: Q e) : e.C_inr.Q :=
    match q.sim with
    | some (new, old) => if q.counter == 1 then old else new
    | none => default

  def C: CellAutomaton e.α e.γ？ := {
    Q := Q e
    δ := fun qa qb qc =>
        let next_q_ctl := e.C_ctl.δ qa.state qb.state qc.state
        let trigger := e.C_ctl.project next_q_ctl
        match trigger with
        | some s =>
          { state := next_q_ctl, counter := 0, sim := some (e.C_inr.embed s, e.C_inr.embed s) }
        | none =>
          match qb.sim with
          | some (new_b, old_b) =>
             if qb.counter == 2 then
               let val_a := e.get_neighbor_val qa
               let val_c := e.get_neighbor_val qc
               let next_val := e.C_inr.δ val_a new_b val_c
               { state := next_q_ctl, counter := 0, sim := some (next_val, new_b) }
             else
               { state := next_q_ctl, counter := qb.counter + 1, sim := some (new_b, old_b) }
          | none =>
             { state := next_q_ctl, counter := 0, sim := none }
    embed := fun a =>
      { state := e.C_ctl.embed a, counter := 0, sim := none }
    project := fun q =>
      match q.sim with
      | some (new, _) => some (e.C_inr.project new)
      | none => none
  }

  variable (c_ctl: Config e.α)
  variable (c_inr: Config e.β)

  def c_ctl_computes_c_inr: Prop :=
    ∀ (t: ℕ) (p: ℤ),
    e.C_ctl.comp c_ctl t p =
      if t = 3 + 2 * p.natAbs
      then some (c_inr p)
      else none


  lemma state_track (t: ℕ) (p: ℤ):
    (e.C.nextt ⦋c_ctl⦌ t p).state = e.C_ctl.nextt ⦋c_ctl⦌ t p := by
    induction t generalizing p with
    | zero =>
      simp [CellAutomaton.embed_config, C]
    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      unfold CellAutomaton.next
      simp only [C]
      -- By induction hypothesis, states at previous step match
      have h1 := ih (p - 1)
      have h2 := ih p
      have h3 := ih (p + 1)
      simp only [C] at h1 h2 h3
      -- All branches of δ set state := e.C_ctl.δ qa.state qb.state qc.state
      -- After substituting via h1, h2, h3, both sides are definitionally equal
      grind

  def T (t: ℕ) (p: ℤ) (k: ℕ) := 3 * t + 3 + 2 * p.natAbs + k

  lemma T_reset_iff (t: ℕ) (p: ℤ) (k: Fin 3):
    T t p k = 3 + 2 * p.natAbs ↔ t = 0 ∧ k = 0 := by
    unfold T
    omega

  theorem spec (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (t: ℕ):
    e.C.trace c_ctl (3 * t + 3) = some (e.C_inr.trace c_inr t) := by
    sorry

  -- Complete characterization: output exists iff time has form 3*t + 3
  theorem spec_iff (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (t: ℕ):
    (e.C.trace c_ctl t).isSome ↔ ∃ t', t = 3 * t' + 3 := by
    constructor
    · -- If output exists, time has form 3*t' + 3
      intro h_some
      -- This requires understanding the counter mechanism in SimFromΛ
      -- Output only happens when counter cycles and sim is some
      sorry
    · -- If time = 3*t' + 3, output exists (follows from spec)
      intro ⟨t', ht'⟩
      rw [ht']
      rw [@spec e c_ctl c_inr h_CM t']
      simp

  -- Specialized version matching DecompressTriple.h_cond form
  theorem h_cond_form (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (k: ℕ) (hk: k = 3):
    ∀ t, (e.C.trace c_ctl (t + k)).isSome == (t % 3 == 0) := by
    intro t
    subst hk
    have spec := @spec_iff e c_ctl c_inr h_CM (t + 3)
    -- Both sides are Bools, show they have the same value
    have h_iff : (e.C.trace c_ctl (t + 3)).isSome = true ↔ (t % 3 == 0) = true := by
      simp only [beq_iff_eq]
      constructor
      · intro h_isSome
        have ⟨t', ht'⟩ := spec.mp h_isSome
        omega
      · intro h_mod
        have h := spec.mpr ⟨t / 3, by omega⟩
        exact h
    cases h1 : (e.C.trace c_ctl (t + 3)).isSome <;>
    cases h2 : (t % 3 == 0) <;>
    simp_all

end SimFromΛ

end CellularAutomatas
