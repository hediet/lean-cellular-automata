import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

/-
  ComposeKSteps: Run C1 for k steps, then run C2.

  Given two CAs where C2 operates on the output alphabet of C1,
  this structure creates a CA that first runs C1 for k steps,
  then switches to running C2 on the projected configuration.
-/
structure ComposeKSteps where
  {α: Type}
  {β: Type}
  {γ: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [_inst_γ: Alphabet γ]
  C1: CellAutomaton α β
  C2: CellAutomaton β γ
  k: ℕ

attribute [instance] ComposeKSteps._inst_α
attribute [instance] ComposeKSteps._inst_β
attribute [instance] ComposeKSteps._inst_γ

namespace ComposeKSteps
  variable (e: ComposeKSteps)

  /-- The combined state: either in phase 1 (running C1) or phase 2 (running C2) -/
  inductive State
  | phase1 : Fin e.k → e.C1.Q → State
  | phase2 : e.C2.Q → State
  deriving DecidableEq

  instance : Inhabited e.State := ⟨.phase2 default⟩

  instance : Fintype e.State :=
    Fintype.ofEquiv ((Fin e.k × e.C1.Q) ⊕ e.C2.Q) {
      toFun := fun
        | .inl (i, q) => .phase1 i q
        | .inr q => .phase2 q
      invFun := fun
        | .phase1 i q => .inl (i, q)
        | .phase2 q => .inr q
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun x => by cases x <;> rfl
    }

  def extractC1 : e.State → e.C1.Q
    | .phase1 _ q => q
    | .phase2 _ => default

  def extractC2 : e.State → e.C2.Q
    | .phase1 _ _ => default
    | .phase2 q => q

  /-- The combined CA that runs C1 for k steps, then C2 -/
  def C : CellAutomaton e.α e.γ := {
    Q := e.State
    δ := fun l c r =>
      match c with
      | .phase1 i q =>
        let q' := e.C1.δ (e.extractC1 l) q (e.extractC1 r)
        match i with
        | ⟨0, _⟩ => .phase2 (e.C2.embed (e.C1.project q'))
        | ⟨n+1, h⟩ => .phase1 ⟨n, Nat.lt_of_succ_lt h⟩ q'
      | .phase2 q =>
        .phase2 (e.C2.δ (e.extractC2 l) q (e.extractC2 r))
    embed := fun a =>
      if h : e.k > 0
      then .phase1 ⟨e.k - 1, Nat.sub_lt h (by omega)⟩ (e.C1.embed a)
      else .phase2 (e.C2.embed (e.C1.project (e.C1.embed a)))
    project := fun
      | .phase1 _ _ => default
      | .phase2 q => e.C2.project q
  }

  /-- After t < k steps, all cells are in phase1 with countdown k-1-t and C1's state -/
  private lemma phase1_state (c: Config e.α) (t: ℕ) (ht: t < e.k) (p: ℤ):
      e.C.nextt ⦋c⦌ t p = .phase1 ⟨e.k - 1 - t, by omega⟩ (e.C1.nextt ⦋c⦌ t p) := by
    have hk : e.k > 0 := by omega
    induction t generalizing p with
    | zero =>
      simp only [CellAutomaton.nextt_zero, Nat.sub_zero]
      unfold CellAutomaton.embed_config C
      simp only [hk, ↓reduceDIte]
    | succ t ih =>
      have ht' : t < e.k := by omega
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      unfold CellAutomaton.next
      rw [ih ht' (p-1), ih ht' p, ih ht' (p+1)]
      unfold C extractC1
      simp only
      -- The countdown at step t is k-1-t, which is > 0 since t+1 < k means t < k-1
      have h_pos : e.k - 1 - t > 0 := by omega
      -- So k-1-t = (k-1-t-1) + 1, i.e., it matches the succ case
      obtain ⟨m, hm⟩ : ∃ m, e.k - 1 - t = m + 1 := ⟨e.k - 1 - t - 1, by omega⟩
      simp only [hm]
      congr 2
      omega

  /-- At step k, all cells transition to phase2 with C2.embed of C1's projected state -/
  private lemma phase2_at_k (c: Config e.α) (p: ℤ):
      e.C.nextt ⦋c⦌ e.k p = .phase2 (e.C2.embed (e.C1.comp ⦋c⦌ e.k p)) := by
    rcases Nat.eq_zero_or_pos e.k with hk | hk
    · -- k = 0: immediate transition
      simp only [hk, CellAutomaton.nextt_zero]
      unfold CellAutomaton.embed_config C CellAutomaton.comp CellAutomaton.project_config
      simp only [hk, Nat.lt_irrefl, ↓reduceDIte, Function.comp_apply, CellAutomaton.nextt_zero]
    · -- k > 0: use phase1_state for k-1 steps, then one more step
      have hk' : e.k - 1 < e.k := by omega
      rw [show e.k = (e.k - 1) + 1 by omega]
      rw [CellAutomaton.nextt_succ]
      unfold CellAutomaton.next
      rw [phase1_state e c (e.k - 1) hk' (p-1)]
      rw [phase1_state e c (e.k - 1) hk' p]
      rw [phase1_state e c (e.k - 1) hk' (p+1)]
      unfold C extractC1
      simp only
      -- At step k-1, countdown is k-1-(k-1) = 0
      have h_zero : e.k - 1 - (e.k - 1) = 0 := by omega
      simp only [h_zero]
      -- Now we're in the .phase1 ⟨0, _⟩ case
      unfold CellAutomaton.comp CellAutomaton.project_config
      simp only [Function.comp_apply]
      congr 1
      -- Need: C1.δ (nextt..(p-1)) (nextt..p) (nextt..(p+1)) = nextt..k p
      conv_rhs => rw [show e.k = e.k - 1 + 1 by omega, CellAutomaton.nextt_succ]
      unfold CellAutomaton.next
      rfl

  /-- After k steps, the combined CA simulates C2 on C1's output -/
  private lemma phase2_state (c: Config e.α) (t: ℕ) (p: ℤ):
      e.C.nextt ⦋c⦌ (e.k + t) p = .phase2 (e.C2.nextt (e.C2.embed_config (e.C1.comp ⦋c⦌ e.k)) t p) := by
    induction t generalizing p with
    | zero =>
      simp only [Nat.add_zero, CellAutomaton.nextt_zero]
      rw [phase2_at_k]
      unfold CellAutomaton.embed_config CellAutomaton.comp CellAutomaton.project_config
      rfl
    | succ t ih =>
      rw [show e.k + (t + 1) = e.k + t + 1 by omega]
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ]
      unfold CellAutomaton.next
      rw [ih (p-1), ih p, ih (p+1)]
      unfold C extractC2
      rfl

  /-- After k steps of C1 and t steps of C2, the result matches running C2 on C1's output -/
  @[simp]
  theorem spec (c: Config e.α) (t: ℕ) (p: ℤ):
      e.C.comp c t p = if t ≥ e.k then e.C2.comp (e.C1.comp c e.k) (t - e.k) p else default := by
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply]
    by_cases h : t ≥ e.k
    · -- t ≥ k: use phase2_state
      simp only [h, ↓reduceIte]
      conv_lhs => rw [show t = e.k + (t - e.k) by omega]
      rw [phase2_state]
      unfold C
      rfl
    · -- t < k: use phase1_state, which projects to default
      simp only [h, ↓reduceIte]
      have ht : t < e.k := by omega
      rw [phase1_state e c t ht p]
      unfold C
      rfl

  /-- Trace version: trace at time k+t equals C2's trace on C1's projection -/
  @[simp]
  theorem trace_spec (c: Config e.α) (t: ℕ):
      e.C.trace c t = if t ≥ e.k then e.C2.trace (e.C1.comp c e.k) (t - e.k) else default := by
    unfold CellAutomaton.trace
    rw [spec]

end ComposeKSteps

/-- Convenience: compose two CAs with a k-step delay -/
def CellAutomaton.composeKSteps {α β γ: Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C1: CellAutomaton α β) (C2: CellAutomaton β γ) (k: ℕ): CellAutomaton α γ :=
  ({ C1 := C1, C2 := C2, k := k } : ComposeKSteps).C

@[simp]
theorem CellAutomaton.composeKSteps_comp {α β γ: Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C1: CellAutomaton α β) (C2: CellAutomaton β γ) (k: ℕ) (c: Config α) (t: ℕ) (p: ℤ):
    (C1.composeKSteps C2 k).comp c t p = if t ≥ k then C2.comp (C1.comp c k) (t - k) p else default := by
  exact ComposeKSteps.spec { C1 := C1, C2 := C2, k := k } c t p

@[simp]
theorem CellAutomaton.composeKSteps_trace {α β γ: Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C1: CellAutomaton α β) (C2: CellAutomaton β γ) (k: ℕ) (c: Config α) (t: ℕ):
    (C1.composeKSteps C2 k).trace c t = if t ≥ k then C2.trace (C1.comp c k) (t - k) else default := by
  exact ComposeKSteps.trace_spec { C1 := C1, C2 := C2, k := k } c t


/-- Identity CA: computes identity after 1 step. State = input alphabet, δ returns center. -/
def CellAutomaton.idCA (α: Type) [Alphabet α]: CellAutomaton α α := {
  Q := α
  δ := fun _ c _ => c
  embed := id
  project := id
}

namespace CellAutomaton.idCA
  variable {α: Type} [Alphabet α]

  private lemma nextt_eq (c: Config α) (t: ℕ) (p: ℤ):
      (idCA α).nextt c t p = c p := by
    induction t generalizing p with
    | zero => rfl
    | succ t ih =>
      rw [CellAutomaton.nextt_succ]
      unfold CellAutomaton.next idCA
      exact ih p

  @[simp]
  theorem comp_spec (c: Config α) (t: ℕ):
      (idCA α).comp c t = c := by
    funext p
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply]
    rw [nextt_eq]
    rfl

  @[simp]
  theorem trace_spec (c: Config α) (t: ℕ):
      (idCA α).trace c t = c 0 := by
    unfold CellAutomaton.trace
    simp [embed_config]
    rfl

end CellAutomaton.idCA

/-- Left edge detector CA: outputs [some ()] at position 0 after 1 step on non-empty words -/
def CellAutomaton.leftEdgeCA (α: Type) [Alphabet α]: CellAutomaton α？ Unit？ := {
  Q := Bool
  δ := fun l c _ => !l && c
  embed := fun
    | some _ => true
    | none => false
  project := fun
    | true => some ()
    | false => none
}

namespace CellAutomaton.leftEdgeCA
  variable {α: Type} [Alphabet α]

  @[simp]
  theorem comp_spec (w: Word α) (hw: w ≠ []):
      (leftEdgeCA α).comp ⟬w⟭ 1 = ⟬[()]⟭ := by
    have hw' : w.length > 0 := by cases w <;> simp_all
    funext p
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply, CellAutomaton.nextt_succ, CellAutomaton.nextt_zero]
    unfold CellAutomaton.next CellAutomaton.embed_config leftEdgeCA word_to_config
    simp only [ge_iff_le, List.length_singleton]
    split_ifs <;> first | rfl | omega

  @[simp]
  theorem trace_spec (w: Word α) (hw: w ≠ []):
      (leftEdgeCA α).trace ⟬w⟭ 1 = some () := by
    unfold CellAutomaton.trace
    rw [comp_spec w hw]
    unfold word_to_config
    simp

  /-- For empty input, leftEdgeCA outputs empty at all times -/
  @[simp]
  theorem comp_empty (t: ℕ):
      (leftEdgeCA α).comp ⟬([] : Word α)⟭ t = ⟬[]⟭ := by
    funext p
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply]
    -- The empty word embeds to all-false state
    have embed_eq : ∀ q : ℤ, (leftEdgeCA α).embed_config ⟬([] : Word α)⟭ q = false := by
      intro q
      unfold CellAutomaton.embed_config leftEdgeCA word_to_config
      have : ¬(0 ≤ q ∧ q < 0) := by omega
      simp [this]
    -- All states remain false for empty input
    have h : ∀ s : ℕ, ∀ q : ℤ, (leftEdgeCA α).nextt ((leftEdgeCA α).embed_config ⟬([] : Word α)⟭) s q = false := by
      intro s
      induction s with
      | zero =>
        intro q
        simp only [CellAutomaton.nextt_zero]
        exact embed_eq q
      | succ s ih =>
        intro q
        rw [CellAutomaton.nextt_succ]
        unfold CellAutomaton.next
        simp only [ih (q-1), ih q, ih (q+1)]
        unfold leftEdgeCA
        rfl
    rw [h]
    unfold leftEdgeCA word_to_config
    have : ¬(0 ≤ p ∧ p < 0) := by omega
    simp [this]

end CellAutomaton.leftEdgeCA

end CellularAutomatas
