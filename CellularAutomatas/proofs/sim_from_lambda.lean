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
    -- Only produce output at counter=0 (every 3rd step after trigger)
    project := fun q =>
      if q.counter == 0 then
        match q.sim with
        | some (new, _) => some (e.C_inr.project new)
        | none => none
      else none
  }

  variable (c_ctl: Config e.α)
  variable (c_inr: Config e.β)

  def c_ctl_computes_c_inr: Prop :=
    ∀ (t: ℕ) (p: ℤ),
    e.C_ctl.comp c_ctl t p =
      if t = 3 + 2 * p.natAbs
      then some (c_inr p)
      else none

  -- Invariant 1: The .state field tracks C_ctl
  lemma state_track (t: ℕ) (p: ℤ):
    (e.C.nextt ⦋c_ctl⦌ t p).state = e.C_ctl.nextt ⦋c_ctl⦌ t p := by
    induction t generalizing p with
    | zero => simp [CellAutomaton.embed_config, C]
    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      unfold CellAutomaton.next; simp only [C]
      have h1 := ih (p - 1); have h2 := ih p; have h3 := ih (p + 1)
      simp only [C] at h1 h2 h3; grind

  -- One-step lemma: characterizes counter and sim at time T+1
  -- Uses native_decide and grind to handle the match/split cases
  lemma step_counter_sim (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (T: ℕ) (p: ℤ):
      if T + 1 = 3 + 2 * p.natAbs then
        (e.C.nextt ⦋c_ctl⦌ (T + 1) p).counter = 0 ∧
        (e.C.nextt ⦋c_ctl⦌ (T + 1) p).sim = some (e.C_inr.embed (c_inr p), e.C_inr.embed (c_inr p))
      else
        match (e.C.nextt ⦋c_ctl⦌ T p).sim with
        | some (new_b, old_b) =>
           if (e.C.nextt ⦋c_ctl⦌ T p).counter == 2 then
             (e.C.nextt ⦋c_ctl⦌ (T + 1) p).counter = 0 ∧
             (e.C.nextt ⦋c_ctl⦌ (T + 1) p).sim =
               some (e.C_inr.δ (e.get_neighbor_val (e.C.nextt ⦋c_ctl⦌ T (p - 1)))
                                new_b
                                (e.get_neighbor_val (e.C.nextt ⦋c_ctl⦌ T (p + 1))), new_b)
           else
             (e.C.nextt ⦋c_ctl⦌ (T + 1) p).counter = (e.C.nextt ⦋c_ctl⦌ T p).counter + 1 ∧
             (e.C.nextt ⦋c_ctl⦌ (T + 1) p).sim = some (new_b, old_b)
        | none =>
           (e.C.nextt ⦋c_ctl⦌ (T + 1) p).counter = 0 ∧
           (e.C.nextt ⦋c_ctl⦌ (T + 1) p).sim = none := by
    -- Use nextt_succ, unfold C.δ, rewrite states, rewrite trigger
    have h_eq : ∀ q, (e.C.nextt ⦋c_ctl⦌ (T + 1) q) =
      e.C.δ (e.C.nextt ⦋c_ctl⦌ T (q - 1)) (e.C.nextt ⦋c_ctl⦌ T q) (e.C.nextt ⦋c_ctl⦌ T (q + 1)) := by
      intro q; rw [CellAutomaton.nextt_succ]; rfl
    rw [h_eq]; simp only [C]
    -- Rewrite state fields — use conv to target just the .state accessors
    have hs_a := e.state_track c_ctl T (p - 1)
    have hs_b := e.state_track c_ctl T p
    have hs_c := e.state_track c_ctl T (p + 1)
    simp only [C] at hs_a hs_b hs_c
    simp only [hs_a, hs_b, hs_c]
    -- Rewrite trigger
    rw [show e.C_ctl.δ (e.C_ctl.nextt ⦋c_ctl⦌ T (p - 1))
                        (e.C_ctl.nextt ⦋c_ctl⦌ T p)
                        (e.C_ctl.nextt ⦋c_ctl⦌ T (p + 1))
         = e.C_ctl.nextt ⦋c_ctl⦌ (T + 1) p from by rw [CellAutomaton.nextt_succ]; rfl]
    have h_trig := h_CM (T + 1) p
    simp only [CellAutomaton.comp, CellAutomaton.project_config, Function.comp_apply] at h_trig
    rw [h_trig]
    split
    · simp
    · split
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩

  -- Invariant 2: Before the trigger
  lemma before_trigger (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr)
      (T: ℕ) (p: ℤ) (hT: T < 3 + 2 * p.natAbs):
      (e.C.nextt ⦋c_ctl⦌ T p).counter = 0 ∧ (e.C.nextt ⦋c_ctl⦌ T p).sim = none := by
    induction T with
    | zero => simp [CellAutomaton.embed_config, C]
    | succ T ih =>
      have h := e.step_counter_sim c_ctl c_inr h_CM T p
      rw [if_neg (by omega : ¬(T + 1 = 3 + 2 * p.natAbs))] at h
      have ⟨_, h_sim⟩ := ih (by omega)
      rw [h_sim] at h; exact h

  -- Helper lemmas for get_neighbor_val
  private lemma get_neighbor_val_of_counter_ne_1 (q_val: Q e)
      {new_val old_val : e.C_inr.Q}
      (h_counter: q_val.counter ≠ 1) (h_sim: q_val.sim = some (new_val, old_val)):
      e.get_neighbor_val q_val = new_val := by
    simp only [get_neighbor_val, h_sim, beq_iff_eq]
    split
    · exact absurd ‹_› h_counter
    · rfl

  private lemma get_neighbor_val_of_counter_1 (q_val: Q e)
      {new_val old_val : e.C_inr.Q}
      (h_counter: q_val.counter = 1) (h_sim: q_val.sim = some (new_val, old_val)):
      e.get_neighbor_val q_val = old_val := by
    simp only [get_neighbor_val, h_sim, beq_iff_eq, h_counter, ↓reduceIte]

  -- Invariant 3: After the trigger
  -- Uses k : ℕ with hk : k < 3 to avoid Fin coercion issues
  theorem after_trigger (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr)
      (t: ℕ) (p: ℤ) (k: ℕ) (hk: k < 3):
      (e.C.nextt ⦋c_ctl⦌ (3 * t + (3 + 2 * p.natAbs) + k) p).counter = ⟨k, hk⟩ ∧
      (e.C.nextt ⦋c_ctl⦌ (3 * t + (3 + 2 * p.natAbs) + k) p).sim =
        some (e.C_inr.nextt ⦋c_inr⦌ t p, e.C_inr.nextt ⦋c_inr⦌ (t - 1) p) := by
    -- Strategy: normalize the goal's time, then apply step_counter_sim + IH
    -- Normalize: rw [h_time] where h_time : 3*t + (3+2|p|) + k = SOME_VALUE
    -- This gives us nextt SOME_VALUE p in the goal, matching our hypotheses
    match t, k, hk with
    | 0, 0, hk =>
      -- Time = 3+2|p|; trigger fires
      have h_time : 3 * 0 + (3 + 2 * p.natAbs) + 0 = 3 + 2 * p.natAbs := by omega
      rw [h_time]
      have h := e.step_counter_sim c_ctl c_inr h_CM (2 + 2 * p.natAbs) p
      rw [show 2 + 2 * p.natAbs + 1 = 3 + 2 * p.natAbs from by omega, if_pos rfl] at h
      refine ⟨h.1, ?_⟩
      rw [h.2]; simp [CellAutomaton.nextt, CellAutomaton.embed_config]
    | 0, 1, hk =>
      have h_time : 3 * 0 + (3 + 2 * p.natAbs) + 1 = (3 + 2 * p.natAbs) + 1 := by omega
      rw [h_time]
      have h_prev := after_trigger h_CM 0 p 0 (by omega)
      rw [show 3 * 0 + (3 + 2 * p.natAbs) + 0 = 3 + 2 * p.natAbs from by omega] at h_prev
      have h := e.step_counter_sim c_ctl c_inr h_CM (3 + 2 * p.natAbs) p
      rw [if_neg (by omega)] at h; rw [h_prev.2] at h; simp only [h_prev.1] at h
      simp only [beq_iff_eq] at h
      refine ⟨?_, h.2⟩; rw [h.1]; rfl
    | 0, 2, hk =>
      have h_time : 3 * 0 + (3 + 2 * p.natAbs) + 2 = (3 + 2 * p.natAbs + 1) + 1 := by omega
      rw [h_time]
      have h_prev := after_trigger h_CM 0 p 1 (by omega)
      rw [show 3 * 0 + (3 + 2 * p.natAbs) + 1 = 3 + 2 * p.natAbs + 1 from by omega] at h_prev
      have h := e.step_counter_sim c_ctl c_inr h_CM (3 + 2 * p.natAbs + 1) p
      rw [if_neg (by omega)] at h; rw [h_prev.2] at h; simp only [h_prev.1] at h
      simp only [beq_iff_eq] at h
      have h12 : ¬((⟨1, by omega⟩ : Fin 3) = 2) := by simp [Fin.ext_iff]
      rw [if_neg h12] at h
      refine ⟨?_, h.2⟩; rw [h.1]; rfl
    | t + 1, 0, hk =>
      -- Compute step
      have h_time : 3 * (t + 1) + (3 + 2 * p.natAbs) + 0 = (3 * t + (3 + 2 * p.natAbs) + 2) + 1 := by omega
      rw [h_time]
      have h_b := after_trigger h_CM t p 2 (by omega)
      have h_step := e.step_counter_sim c_ctl c_inr h_CM (3 * t + (3 + 2 * p.natAbs) + 2) p
      rw [if_neg (by omega)] at h_step
      rw [h_b.2] at h_step
      -- h_b.1 says counter = ⟨2, _⟩, so counter == 2 evaluates to true
      have h_beq2 : ((e.C.nextt ⦋c_ctl⦌ (3 * t + (3 + 2 * p.natAbs) + 2) p).counter == 2) = true := by
        rw [beq_iff_eq]; exact h_b.1
      rw [h_beq2] at h_step; simp only [↓reduceIte] at h_step
      -- Neighbor values: both return nextt_inr t at their position
      have h_left : e.get_neighbor_val (e.C.nextt ⦋c_ctl⦌ (3 * t + (3 + 2 * p.natAbs) + 2) (p - 1))
                    = e.C_inr.nextt ⦋c_inr⦌ t (p - 1) := by
        rcases le_or_gt p 0 with hp | hp
        · -- p ≤ 0: p-1 is outer, |p-1| = |p|+1, phase (t, p-1, 0)
          have h_a := after_trigger h_CM t (p - 1) 0 (by omega)
          rw [show (p - 1).natAbs = p.natAbs + 1 from by omega,
              show 3 * t + (3 + 2 * (p.natAbs + 1)) + 0 = 3 * t + (3 + 2 * p.natAbs) + 2 from by omega] at h_a
          exact get_neighbor_val_of_counter_ne_1 e _ (by rw [h_a.1]; simp [Fin.ext_iff]) h_a.2
        · -- p > 0: p-1 is inner, |p-1| = |p|-1, phase (t+1, p-1, 1)
          have h_a := after_trigger h_CM (t + 1) (p - 1) 1 (by omega)
          rw [show (p - 1).natAbs = p.natAbs - 1 from by omega,
              show 3 * (t + 1) + (3 + 2 * (p.natAbs - 1)) + 1 = 3 * t + (3 + 2 * p.natAbs) + 2 from by omega] at h_a
          exact get_neighbor_val_of_counter_1 e _ h_a.1
            (by rw [h_a.2]; congr 1)
      have h_right : e.get_neighbor_val (e.C.nextt ⦋c_ctl⦌ (3 * t + (3 + 2 * p.natAbs) + 2) (p + 1))
                    = e.C_inr.nextt ⦋c_inr⦌ t (p + 1) := by
        rcases le_or_gt 0 p with hp | hp
        · -- p ≥ 0: p+1 is outer, |p+1| = |p|+1, phase (t, p+1, 0)
          have h_c := after_trigger h_CM t (p + 1) 0 (by omega)
          rw [show (p + 1).natAbs = p.natAbs + 1 from by omega,
              show 3 * t + (3 + 2 * (p.natAbs + 1)) + 0 = 3 * t + (3 + 2 * p.natAbs) + 2 from by omega] at h_c
          exact get_neighbor_val_of_counter_ne_1 e _ (by rw [h_c.1]; simp [Fin.ext_iff]) h_c.2
        · -- p < 0: p+1 is inner, |p+1| = |p|-1, phase (t+1, p+1, 1)
          have h_c := after_trigger h_CM (t + 1) (p + 1) 1 (by omega)
          rw [show (p + 1).natAbs = p.natAbs - 1 from by omega,
              show 3 * (t + 1) + (3 + 2 * (p.natAbs - 1)) + 1 = 3 * t + (3 + 2 * p.natAbs) + 2 from by omega] at h_c
          apply get_neighbor_val_of_counter_1 e _
          · exact_mod_cast h_c.1
          · convert h_c.2 using 2
      rw [h_left, h_right] at h_step
      refine ⟨h_step.1, ?_⟩
      rw [h_step.2]; congr 2
      rw [CellAutomaton.nextt_succ]; rfl
    | t + 1, 1, hk =>
      have h_time : 3 * (t + 1) + (3 + 2 * p.natAbs) + 1 = (3 * (t + 1) + (3 + 2 * p.natAbs)) + 1 := by omega
      rw [h_time]
      have h_prev := after_trigger h_CM (t + 1) p 0 (by omega)
      rw [show 3 * (t + 1) + (3 + 2 * p.natAbs) + 0 = 3 * (t + 1) + (3 + 2 * p.natAbs) from by omega] at h_prev
      have h := e.step_counter_sim c_ctl c_inr h_CM (3 * (t + 1) + (3 + 2 * p.natAbs)) p
      rw [if_neg (by omega)] at h; rw [h_prev.2] at h; simp only [h_prev.1] at h
      simp only [beq_iff_eq] at h
      refine ⟨?_, h.2⟩; rw [h.1]; rfl
    | t + 1, 2, hk =>
      have h_time : 3 * (t + 1) + (3 + 2 * p.natAbs) + 2 = (3 * (t + 1) + (3 + 2 * p.natAbs) + 1) + 1 := by omega
      rw [h_time]
      have h_prev := after_trigger h_CM (t + 1) p 1 (by omega)
      have h := e.step_counter_sim c_ctl c_inr h_CM (3 * (t + 1) + (3 + 2 * p.natAbs) + 1) p
      rw [if_neg (by omega)] at h; rw [h_prev.2] at h; simp only [h_prev.1] at h
      simp only [beq_iff_eq] at h
      have h12 : ¬((⟨1, by omega⟩ : Fin 3) = 2) := by simp [Fin.ext_iff]
      rw [if_neg h12] at h
      refine ⟨?_, h.2⟩; rw [h.1]; rfl
    | _, k + 3, hk => omega
  termination_by (t, p.natAbs, k)

  -- ═══════════════════════════════════════════════
  -- Main theorems
  -- ═══════════════════════════════════════════════

  theorem spec (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (t: ℕ):
    e.C.trace c_ctl (3 * t + 3) = some (e.C_inr.trace c_inr t) := by
    simp only [CellAutomaton.trace, CellAutomaton.comp, CellAutomaton.project_config,
               Function.comp_apply]
    have h := e.after_trigger c_ctl c_inr h_CM t 0 0 (by omega)
    simp only [Int.natAbs_zero, Nat.mul_zero, Nat.add_zero] at h
    rw [show 3 * t + 3 + 0 = 3 * t + 3 from by omega] at h
    change (if (e.C.nextt ⦋c_ctl⦌ (3 * t + 3) 0).counter == 0 then
              match (e.C.nextt ⦋c_ctl⦌ (3 * t + 3) 0).sim with
              | some (new, _) => some (e.C_inr.project new)
              | none => none
            else none) = _
    rw [h.1, h.2]; rfl

  private theorem spec_iff (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (T: ℕ):
    (e.C.trace c_ctl T).isSome ↔ ∃ t, T = 3 * t + 3 := by
    constructor
    · intro h_some
      simp only [CellAutomaton.trace, CellAutomaton.comp, CellAutomaton.project_config,
                  Function.comp_apply] at h_some
      change (if (e.C.nextt ⦋c_ctl⦌ T 0).counter == 0 then
                match (e.C.nextt ⦋c_ctl⦌ T 0).sim with
                | some (new, _) => some (e.C_inr.project new)
                | none => none
              else none).isSome = true at h_some
      by_cases hT : T < 3
      · have ⟨_, h_sim⟩ := e.before_trigger c_ctl c_inr h_CM T 0 (by simp; omega)
        rw [h_sim] at h_some; simp at h_some
      · push_neg at hT
        set t := (T - 3) / 3; set k := (T - 3) % 3
        have hk_lt : k < 3 := Nat.mod_lt _ (by omega)
        have h_at := e.after_trigger c_ctl c_inr h_CM t 0 k hk_lt
        simp only [Int.natAbs_zero, Nat.mul_zero, Nat.add_zero] at h_at
        rw [show 3 * t + 3 + k = T from by omega] at h_at
        rw [h_at.1, h_at.2] at h_some
        simp only [beq_iff_eq, Fin.mk_eq_zero] at h_some
        split at h_some
        · exact ⟨t, by omega⟩
        · simp at h_some
    · intro ⟨t, hT⟩; rw [hT, e.spec c_ctl c_inr h_CM t]; simp

  theorem h_cond_form (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (k: ℕ) (hk: k = 3):
    ∀ t, (e.C.trace c_ctl (t + k)).isSome == (t % 3 == 0) := by
    intro t; subst hk
    suffices h : (e.C.trace c_ctl (t + 3)).isSome = (t % 3 == 0) by simp [h]
    cases h_is : (e.C.trace c_ctl (t + 3)).isSome
    · symm; rw [beq_eq_false_iff_ne]; intro h_mod
      exact absurd ((e.spec_iff c_ctl c_inr h_CM (t + 3)).mpr ⟨t / 3, by omega⟩) (by simp [h_is])
    · symm; rw [beq_iff_eq]
      have ⟨t', ht'⟩ := (e.spec_iff c_ctl c_inr h_CM (t + 3)).mp (by simp [h_is])
      omega

end SimFromΛ

end CellularAutomatas
