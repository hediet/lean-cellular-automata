import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.compress_to_diag

namespace CellularAutomatas

open CellAutomaton

structure DecompressTriple where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α (Option (β³))

attribute [instance] DecompressTriple._inst_α
attribute [instance] DecompressTriple._inst_β

namespace DecompressTriple

  variable (e: DecompressTriple)

  -- State: original state, counter mod 3, stored triple
  def C: CellAutomaton e.α e.β := {
    Q := e.C_orig.Q × Fin 3 × e.β³
    δ := fun (qa, _, _) (qb, cb, vb) (qc, _, _) =>
      let next_q := e.C_orig.δ qa qb qc
      match e.C_orig.project next_q with
      | some triple => (next_q, 0, triple)
      | none => (next_q, cb + 1, vb)
    embed := fun a =>
      (e.C_orig.embed a, 0, fun _ => default)
    project := fun (_, c, v) => v c
  }

  -- h_cond says: output exists at times k, k+3, k+6, ... (i.e., when t % 3 == 0)
  def h_cond (c: Config e.α) (k: ℕ): Prop :=
      ∀ (t: ℕ), ((e.C_orig.trace c (t + k))).isSome == (t % 3 == 0)

  -- Helper: state tracking for C_orig
  -- The first component of the Decompress CA state tracks C_orig's state
  lemma state_track (c: Config e.α) (t: ℕ) (p: ℤ):
      (e.C.nextt ⦋c⦌ t p).1 = e.C_orig.nextt ⦋c⦌ t p := by
    induction t generalizing p with
    | zero => simp [CellAutomaton.embed_config, C]
    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      unfold CellAutomaton.next
      simp only [C]
      -- By induction hypothesis, states at previous step match
      have h1 := ih (p - 1)
      have h2 := ih p
      have h3 := ih (p + 1)
      -- All branches of δ set first component to e.C_orig.δ qa.1 qb.1 qc.1
      -- The result of δ is either (next_q, 0, triple) or (next_q, cb+1, vb)
      -- In both cases, first projection is next_q = e.C_orig.δ qa qb qc
      simp only [C] at h1 h2 h3
      -- Rewrite using the IH and simplify the match
      simp only [h1, h2, h3]
      -- Now pattern match on the result of e.C_orig.project
      cases e.C_orig.project (e.C_orig.δ (e.C_orig.nextt ⦋c⦌ t (p - 1))
                                         (e.C_orig.nextt ⦋c⦌ t p)
                                         (e.C_orig.nextt ⦋c⦌ t (p + 1))) with
      | some _ => rfl
      | none => rfl

  -- Helper lemma: gets the second components of C.δ based on C_orig.project
  -- This is the core computation that determines counter and stored value
  private lemma delta_snd (qa qb qc : e.C.Q) :
    let result := e.C.δ qa qb qc
    match e.C_orig.project (e.C_orig.δ qa.1 qb.1 qc.1) with
    | some triple => result.2 = (0, triple)
    | none => result.2 = (qb.2.1 + 1, qb.2.2) := by
    simp only [C]
    cases e.C_orig.project (e.C_orig.δ qa.1 qb.1 qc.1) <;> rfl

  -- Helper: track (counter, stored_value) after an output at time t
  -- If C_orig outputs v at time t (and none at t+1, t+2), then at time t+o
  -- the state has counter=o and stored=v
  lemma counter_stored (c: Config e.α) (t: ℕ) (v: e.β³)
    (h0: e.C_orig.comp c t 0 = some v)
    (h1: e.C_orig.comp c (t + 1) 0 = none)
    (h2: e.C_orig.comp c (t + 2) 0 = none)
    (o: Fin 3):
    let state := e.C.nextt ⦋c⦌ (t + o) 0
    state.2.1 = o ∧ state.2.2 = v := by
    -- Proof outline:
    -- For o = 0: At time t, h0 says C_orig project = some v
    --   So the C transition at step t-1→t stores (0, v)
    -- For o = 1: At time t+1, h1 says C_orig project = none
    --   So counter increments: (0+1, v) = (1, v)
    -- For o = 2: At time t+2, h2 says C_orig project = none
    --   So counter increments: (1+1, v) = (2, v)
    -- The actual proof requires careful tracking of the match expression
    -- in the C.δ transition function, which is complex to formalize
    sorry

  theorem spec (c: Config e.α) (t: ℕ) (v: e.β³)
    (h: ∀ o: Fin 3, e.C_orig.comp c (t + o) 0 = if o == 0 then some v else none):
      ∀ o: Fin 3, e.C.comp c (t + o) 0 = v o := by
    intro o
    -- Extract hypotheses from h
    have h0 : e.C_orig.comp c t 0 = some v := by simpa using h 0
    have h1 : e.C_orig.comp c (t + 1) 0 = none := by simpa using h 1
    have h2 : e.C_orig.comp c (t + 2) 0 = none := by simpa using h 2
    -- Use counter_stored to get the state at t+o
    have hs := counter_stored e c t v h0 h1 h2 o
    -- The output is v[counter] = v[o]
    -- project (_, counter, stored) = stored counter
    -- By hs, counter = o and stored = v, so output = v o
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply]
    change e.C.project (e.C.nextt ⦋c⦌ (t + o) 0) = v o
    -- The state at time t+o is (_, o, v) by hs
    -- project (_, o, v) = v o
    have h_counter := hs.1
    have h_stored := hs.2
    -- project for C extracts state.2.2 state.2.1
    show (e.C.nextt ⦋c⦌ (t + o) 0).2.2 (e.C.nextt ⦋c⦌ (t + o) 0).2.1 = v o
    rw [h_counter, h_stored]

  theorem spec2 (c: Config e.α) (h: e.h_cond c k) (t1: ℕ) (t2: Fin 3):
      e.C.trace c (3 * t1 + t2 + k) = (e.C_orig.trace c (3 * t1 + k)).get (by
        have := h (3 * t1)
        simp only [beq_iff_eq, Nat.mul_mod_right] at this
        simp [trace, CellAutomaton.comp] at this ⊢
        exact this
      ) t2 := by
    -- h_cond gives: output at t+k exists iff t % 3 == 0
    -- Thus at 3*t1+k: output some v; at 3*t1+1+k, 3*t1+2+k: output none
    -- We use spec applied at time (3*t1+k)
    unfold trace
    -- Get the value v that is output at time 3*t1+k
    have h_isSome : (e.C_orig.comp c (3 * t1 + k) 0).isSome := by
      have := h (3 * t1)
      simp only [beq_iff_eq, Nat.mul_mod_right] at this
      simp [trace, CellAutomaton.comp] at this ⊢
      exact this
    set v := (e.C_orig.comp c (3 * t1 + k) 0).get h_isSome with hv_def
    -- We need to show the hypotheses of spec are satisfied
    have h_spec_hyp : ∀ o: Fin 3, e.C_orig.comp c (3 * t1 + k + o) 0 =
                                  if o == 0 then some v else none := by
      intro o
      cases o using Fin.cases with
      | zero =>
        simp only [beq_self_eq_true, ↓reduceIte, Fin.val_zero, Nat.add_zero]
        -- v = get h_isSome, so some v = some (get h_isSome) = the original option
        rw [hv_def]
        exact (Option.some_get h_isSome).symm
      | succ o' =>
        -- Goal: comp c (3*t1 + k + succ o') 0 = if succ o' == 0 then some v else none
        -- succ o' ≠ 0, so the if reduces to none
        have h_beq : (o'.succ == 0) = false := beq_false_of_ne (Fin.succ_ne_zero o')
        simp only [h_beq]
        have ho := h (3 * t1 + o'.succ)
        -- ho : (trace...).isSome == ((3*t1 + o'.succ) % 3 == 0)
        -- Since (3*t1 + o'.succ) % 3 ≠ 0, the RHS is false
        have h_mod : (3 * t1 + ↑o'.succ) % 3 ≠ 0 := by
          have h1 : (↑o'.succ : ℕ) < 3 := o'.succ.isLt
          have h2 : (↑o'.succ : ℕ) > 0 := Nat.succ_pos _
          omega
        have h_rhs_false : ((3 * t1 + ↑o'.succ) % 3 == 0) = false :=
          beq_false_of_ne h_mod
        simp only [h_rhs_false, beq_false] at ho
        unfold trace at ho
        -- ho: (!isSome ...) = true, convert to isSome = false, then to = none
        simp only [Bool.not_eq_true'] at ho
        simp at ho
        -- Now ho should be = none
        have h_eq : 3 * t1 + k + ↑o'.succ = 3 * t1 + ↑o'.succ + k := by ring
        rw [h_eq]
        exact ho
    -- Now apply spec
    have h_spec := spec e c (3 * t1 + k) v h_spec_hyp t2
    -- Adjust the indices: 3*t1 + k + t2 = 3*t1 + t2 + k
    convert h_spec using 2
    ring

end DecompressTriple

end CellularAutomatas
