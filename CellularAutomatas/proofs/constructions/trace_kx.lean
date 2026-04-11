import CellularAutomatas.defs
import CellularAutomatas.proofs.constructions.speedup_compressed
namespace CellularAutomatas

open CellAutomaton

-- TraceKx: Outputs k+1 values (including current time step)
-- At time t1 + k, index t2 : Fin (k+1) gives output from time t1 + t2
-- So at time t, we get outputs from times t-k, t-k+1, ..., t-1, t
structure TraceKx where
  k: ℕ
  α: Type
  β: Type
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [inst: NeZero k]
  C_orig: CellAutomaton α β

attribute [instance] TraceKx.inst
attribute [instance] TraceKx._inst_α
attribute [instance] TraceKx._inst_β

namespace TraceKx

  variable (e: TraceKx)

  def C: CellAutomaton e.α (Fin (e.k + 1) → e.β？) := {
    Q := Fin (e.k + 1) → e.C_orig.Q
    δ := fun a b c =>
      let next_s := e.C_orig.δ (a (Fin.last e.k)) (b (Fin.last e.k)) (c (Fin.last e.k))
      Fin.snoc (Fin.tail b) next_s
    embed := fun a =>
      let s := e.C_orig.embed a
      fun _ => s
    project := fun q =>
      fun i => some (e.C_orig.project (q i))
  }

  lemma state_eq (c: Config e.α) (t: ℕ) (p: ℤ) (i: Fin (e.k + 1)):
      (e.C.nextt ⦋c⦌ t p) i = (e.C_orig.nextt ⦋c⦌ (t + i - e.k) p) := by
    revert p i
    induction t with
    | zero =>
      intros p i
      simp [C, CellAutomaton.embed_config]
      have : (i : ℕ) - e.k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt_succ i.isLt)
      rw [this]
      rw [nextt_zero]
      rfl
    | succ t ih =>
      intros p i
      rw [CellAutomaton.nextt_succ]
      unfold CellAutomaton.next C
      simp
      by_cases h: i = Fin.last e.k
      · rw [h]
        simp [Fin.snoc]
        change e.C_orig.δ (e.C.nextt ⦋c⦌ t (p - 1) (Fin.last e.k)) (e.C.nextt ⦋c⦌ t p (Fin.last e.k)) (e.C.nextt ⦋c⦌ t (p + 1) (Fin.last e.k)) = _
        rw [ih (p-1) (Fin.last e.k), ih p (Fin.last e.k), ih (p+1) (Fin.last e.k)]
        simp [CellAutomaton.next]
      · have h_lt : (i : ℕ) < e.k := by
          apply Nat.lt_of_le_of_ne
          · apply Nat.le_of_lt_succ
            exact i.isLt
          · intro heq
            apply h
            ext
            simp [heq]
        have h_cast : i = Fin.castSucc ⟨i, h_lt⟩ := by
          ext
          simp
        rw [h_cast]
        simp [Fin.snoc, h_lt]
        change e.C.nextt ⦋c⦌ t p (Fin.succ ⟨i, h_lt⟩) = _
        rw [ih p (Fin.succ ⟨i, h_lt⟩)]
        congr 1
        simp
        rw [Nat.add_comm (↑i) 1]
        rw [←Nat.add_assoc]

  lemma spec_at (c: Config e.α) (t1: ℕ) (p: ℤ):
      e.C.comp c (t1 + e.k) p =
        fun (t2: Fin (e.k + 1)) => some (e.C_orig.comp c (t1 + t2) p)
      := by
    funext t2
    simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold]
    simp only [C]
    show some (e.C_orig.project (e.C.nextt ⦋c⦌ (t1 + e.k) p t2)) = _
    rw [state_eq]
    congr 1
    rw [Nat.add_right_comm]
    rw [Nat.add_sub_cancel]

  @[simp]
  theorem spec (c: Config e.α) (t1: ℕ) (p: ℤ) (t2: Fin (e.k + 1)) (h: t1 > e.k):
      e.C.comp c t1 p t2 = some (e.C_orig.comp c (t1 - e.k + t2) p) := by
    have key := congrFun (e.spec_at c (t1 - e.k) p) t2
    simp [Nat.sub_add_cancel (Nat.le_of_lt h)] at key
    exact key

  attribute [irreducible] C

end TraceKx

structure SpeedupAndTraceKx where
  k: ℕ
  α: Type
  β: Type
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [inst: NeZero k]
  C_orig: CellAutomaton α β

attribute [instance] SpeedupAndTraceKx.inst
attribute [instance] SpeedupAndTraceKx._inst_α
attribute [instance] SpeedupAndTraceKx._inst_β

namespace SpeedupAndTraceKx

  variable (e: SpeedupAndTraceKx)

  private def T: TraceKx := {
    k := e.k
    α := e.α
    β := e.β
    C_orig := e.C_orig
  }
  example : (CellAutomaton e.α (Fin (e.k + 1) → e.β？)) := e.T.C

  private def SP: SpeedupKx := {
    k := e.k
    α := e.α
    β := Fin (e.k + 1) → e.β？
    C_orig := e.T.C
  }
  example : (CellAutomaton (Fin e.k → e.α) (Fin e.k → (Fin (e.k + 1) → e.β？))) := e.SP.C

  def C: CellAutomaton (Fin e.k → e.α) (Fin e.k → e.β) :=
    e.SP.C.map_project (fun f => fun i => (f 0 i.castSucc).getD default)

  theorem spec1 {c: Config e.α} {t1: ℕ} {t2: Fin e.k}:
      e.C.trace (SpeedupKx.compress e.k c) (t1 + 1) t2 = e.C_orig.trace c (e.k * t1 + t2) := by
    unfold trace
    have h_comp : ∀ t p, e.C.comp ⦋SpeedupKx.compress e.k c⦌ t p = (fun g i => (g 0 i.castSucc).getD default) (e.SP.C.comp ⦋SpeedupKx.compress e.k c⦌ t p) := by
      intros t p
      simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold]
      simp [C]
      rfl
    rw [h_comp]
    have h_spec : e.SP.C.comp ⦋SpeedupKx.compress e.k c⦌ (t1 + 1) = SpeedupKx.compress e.k (e.T.C.comp c (e.k * (t1 + 1))) := by
      convert e.SP.spec (t1 + 1)
    rw [h_spec]
    unfold SpeedupKx.compress
    simp only
    rw [mul_add, mul_one]
    have h_spec_T : e.T.C.comp c (e.k * t1 + e.k) 0 = fun (t2 : Fin (e.k + 1)) => some (e.C_orig.comp c (e.k * t1 + t2) 0) := by
      convert e.T.spec_at c (e.k * t1) 0
    simp only [zero_mul, zero_add]
    erw [h_spec_T]
    simp

  attribute [irreducible] C

end SpeedupAndTraceKx

end CellularAutomatas
