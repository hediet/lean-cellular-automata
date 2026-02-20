import CellularAutomatas.defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Linarith
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.border
import CellularAutomatas.proofs.constructions.border_dead
import CellularAutomatas.proofs.causal
namespace CellularAutomatas


section

  def φ {C: CellAutomaton α？ β} (b: C.Q) (c: C.Q) := (b, fun a => C.δ a b c)

  def Sp (C: CellAutomaton α？ β): CellAutomaton α？ (C.Q -> β) := by
    exact {
      Q := C.Q × (C.Q → C.Q)
      δ := fun a b c => φ (C.δ a.fst b.fst c.fst) (c.snd b.fst),
      embed a := φ (C.embed a) C.border,
      project qc := fun l => C.project (qc.snd l),
    }

  variable {C: CellAutomaton α？ β}

  private lemma fst_prop {w: Word α} (t: ℕ) (i: ℤ):
      ((Sp C).nextt w t i).fst = C.nextt w t i := by
    induction t generalizing i with
    | zero =>
      simp [Sp, φ, embed_word_at_eq]
    | succ t ih =>
      simp [CellAutomaton.next]
      set c := (Sp C).nextt w t
      simp [Sp, φ, ih]


  private lemma snd_prop (w: Word α) (t: ℕ) (i: ℤ) (h: t + i + 1 ≥ w.length):
    ((Sp C).nextt w t i).snd (C.nextt w t (i - 1)) = C.nextt w (t + 1) i := by

    induction t generalizing i with
    | zero =>
      rw [CellAutomaton.nextt_succ, nextt0, nextt0]

      have cp1_border : (CellAutomaton.embed_config (⟬w⟭)) (i+1) = C.border := by
        have: i + 1 ∉ w.range := by simp [Word.range]; omega
        simp_all [CellAutomaton.border, embed_word_at_eq2]

      simp [Sp, φ, cp1_border, CellAutomaton.next, embed_word_at_eq]


    | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next]

      set c' := (Sp C).nextt w t
      set c := C.nextt w t

      conv in (Sp C).δ => dsimp [Sp]

      have this i : (c' i).1 = c i := by simp [c', c, fst_prop]
      rw [this]
      rw [this]
      rw [this]

      rw [←CellAutomaton.next]

      have ih := ih (i + 1) (by omega)
      rw [add_sub_cancel_right] at ih
      rw [ih]
      unfold φ
      simp
      rfl

  lemma spec (w: Word α) (t: ℕ) (h: t + 1 ≥ w.length):
    ((Sp C).trace w t) (C.nextt w t (-1)) = C.trace w (t + 1) := by
    unfold CellAutomaton.trace CellAutomaton.comp
    simp only [Function.comp_apply]
    unfold CellAutomaton.project_config Sp
    simp only
    have := snd_prop (C := C) w t 0 (by simp; omega : (t : ℤ) + 0 + 1 ≥ w.length)
    simp only at this
    convert congrArg C.project this using 2

end

def SpB (C: CellAutomaton α？ β) := (Sp C).map_project (fun q => q C.border)

def SpBk (k: ℕ) (C: CellAutomaton α？ β) := (SpB)^[k] C

-- SpB speeds up by 1 step when the condition t + 1 ≥ w.length holds
lemma SpB_trace_eq {C: CellAutomaton α？ β} (h: C.left_dead C.border) (w: Word α) (t: ℕ) (ht: t + 1 ≥ w.length):
    (SpB C).trace w t = C.trace w (t + 1) := by
  simp only [SpB, trace_of_map_project, Function.comp_apply]
  have h_neg1 : C.nextt w t (-1) = C.border := left_dead_border_left h w t (-1) (by omega)
  conv_lhs => rw [←h_neg1]
  exact spec w t ht

-- DeadBorder wrapper function: takes an automaton and wraps it with DeadBorder
def withDeadBorder (c_val: ℕ) (C: CellAutomaton α？ β) [Alphabet α]: CellAutomaton α？ β :=
  let db : DeadBorder := { c := c_val, C_orig := C }
  db.C

-- DeadBorder.C has dead border by construction
lemma withDeadBorder_dead_border [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β):
    (withDeadBorder c_val C).dead (withDeadBorder c_val C).border :=
  DeadBorder.spec_left_border_dead

-- DeadBorder.C has left_dead border
lemma withDeadBorder_left_dead [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β):
    (withDeadBorder c_val C).left_dead (withDeadBorder c_val C).border :=
  dead_implies_left_dead (withDeadBorder_dead_border c_val C)

-- DeadBorder preserves trace within bounds
lemma withDeadBorder_trace_eq [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β) (w: Word α) (t: ℕ)
    (h_bound: t < c_val * w.length):
    (withDeadBorder c_val C).trace w t = C.trace w t := by
  unfold withDeadBorder
  let db : DeadBorder := { c := c_val, C_orig := C }
  exact @DeadBorder.spec_comp_trace db w t h_bound

-- SpB applied to DeadBorder.C then wrapped again - one step of speedup
def SpBD [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β): CellAutomaton α？ β :=
  withDeadBorder c_val (SpB (withDeadBorder c_val C))

-- k iterations of SpBD
def SpBDk [Alphabet α] (c_val k: ℕ) (C: CellAutomaton α？ β): CellAutomaton α？ β :=
  (SpBD c_val)^[k] C

-- Main speedup lemma using DeadBorder at each step
lemma SpBD_trace_eq [Alphabet α] (c_val: ℕ) (C: CellAutomaton α？ β) (w: Word α) (t: ℕ)
    (ht: t + 1 ≥ w.length) (h_bound: t + 1 < c_val * w.length):
    (SpBD c_val C).trace w t = C.trace w (t + 1) := by
  unfold SpBD
  -- withDeadBorder c_val (SpB (withDeadBorder c_val C)).trace w t
  -- = C.trace w (t + 1)

  -- Step 1: inner DeadBorder has left_dead border
  set C1 := withDeadBorder c_val C
  have h_C1_left_dead : C1.left_dead C1.border := withDeadBorder_left_dead c_val C

  -- Step 2: SpB of C1 speeds up by 1
  have h_spb : (SpB C1).trace w t = C1.trace w (t + 1) := SpB_trace_eq h_C1_left_dead w t ht

  -- Step 3: relate C1.trace to C.trace using DeadBorder preservation
  have h_db_trace : C1.trace w (t + 1) = C.trace w (t + 1) :=
    withDeadBorder_trace_eq c_val C w (t + 1) h_bound

  -- Step 4: outer DeadBorder doesn't change trace within bounds
  have h_outer : (withDeadBorder c_val (SpB C1)).trace w t = (SpB C1).trace w t :=
    withDeadBorder_trace_eq c_val (SpB C1) w t (by omega)

  rw [h_outer, h_spb, h_db_trace]

-- k-step speedup using DeadBorder at each iteration
lemma SpBDk_trace_eq [Alphabet α] (c_val k: ℕ) (C: CellAutomaton α？ β) (w: Word α) (t: ℕ)
    (ht: t + 1 ≥ w.length) (h_bound: t + k < c_val * w.length):
    (SpBDk c_val k C).trace w t = C.trace w (t + k) := by
  unfold SpBDk
  induction k generalizing t with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.add_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    -- (SpBD c_val ((SpBD c_val)^[k] C)).trace w t = C.trace w (t + k + 1)
    set Ck := (SpBD c_val)^[k] C
    have h_step : (SpBD c_val Ck).trace w t = Ck.trace w (t + 1) := by
      apply SpBD_trace_eq
      · exact ht
      · omega
    rw [h_step]
    rw [ih (t + 1) (by omega) (by omega)]
    ring_nf

structure SpeedupKSteps where
  {α: Type}
  {β: Type}
  [inst1: Alphabet α]
  [inst2: Alphabet β]
  C_orig: CellAutomaton α？ β
  k: ℕ
  c: ℕ  -- speedup factor bound (from DeadBorder)

attribute [instance] SpeedupKSteps.inst1
attribute [instance] SpeedupKSteps.inst2


namespace SpeedupKSteps

  variable (e: SpeedupKSteps)

  -- The speedup automaton: k iterations of SpBD
  def C : CellAutomaton e.α？ e.β := SpBDk e.c e.k e.C_orig

  theorem spec (w: Word e.α) (i: ℕ) (h_len: i ≥ w.length - 1) (h_bound: i + e.k < e.c * w.length):
      e.C.trace w i = e.C_orig.trace w (i + e.k) := by
    exact SpBDk_trace_eq e.c e.k e.C_orig w i (by omega) h_bound

end SpeedupKSteps

lemma intCastEq {k: ℕ} [NeZero k] (p: ℤ): ((Fin.intCast p: Fin k) : ℤ) = p % k := by
  unfold Fin.intCast
  split_ifs with h
  · lift p to ℕ using h
    simp
  · push_neg at h
    rw [Fin.val_neg]
    simp only [Fin.val_ofNat]
    have hp : p = -↑(p.natAbs) := by
      rw [←neg_neg p, ←Int.ofNat_natAbs_of_nonpos (le_of_lt h)]
      simp
    rw [hp]
    rw [Int.neg_emod]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    by_cases hk : k ∣ p.natAbs
    · simp only [Fin.ofNat_eq_cast, Fin.natCast_eq_zero, hk, ↓reduceIte, Nat.cast_zero,
      Int.ofNat_dvd.mpr hk]
    · have h_not_dvd : ¬ (↑k : ℤ) ∣ ↑p.natAbs := mt Int.ofNat_dvd.mp hk
      simp only [Fin.ofNat_eq_cast, Fin.natCast_eq_zero, hk, ↓reduceIte, h_not_dvd]
      rw [Int.ofNat_sub]
      · simp only [Int.natCast_emod]
      · apply le_of_lt
        apply Nat.mod_lt
        exact NeZero.pos k

open CellAutomaton

structure SpeedupKx where
  k: ℕ
  α: Type
  β: Type
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [inst: NeZero k]
  C_orig: CellAutomaton α β

attribute [instance] SpeedupKx.inst
attribute [instance] SpeedupKx._inst_α
attribute [instance] SpeedupKx._inst_β

namespace SpeedupKx
  section
    variable {Q: Type}
    variable (k: ℕ) [NeZero k]

    def compress (c: Config Q): Config (Fin k → Q) :=
      fun p => fun j => c (p * k + j)

    def decompress (c: Config (Fin k → Q)): Config Q :=
      fun p => c (p / k) (Fin.intCast p)

    lemma compress_decompress (c: Config Q):
      decompress k (compress k c) = c := by
        funext p
        unfold decompress compress
        congr
        rw [intCastEq]
        rw [Int.emod_def]
        grind only

  end

  variable (e: SpeedupKx)

  def Q' := Fin e.k → e.C_orig.Q

  def local_config (a b c: e.Q'): Config e.C_orig.Q :=
      fun p => if p <= -e.k then a (Fin.intCast 0) else
        if p < 0 then a (Fin.intCast (p + e.k))
        else if p < e.k then b (Fin.intCast p)
        else c (Fin.intCast (p - e.k))

  def to_local_config (c: Config (e.C_orig.Q)): e.Q' := fun j => c j

  def C: CellAutomaton (Fin e.k → e.α) (Fin e.k → e.β) := {
    Q := Fin e.k → e.C_orig.Q
    δ := fun a b c =>
      e.to_local_config (e.C_orig.nextt (e.local_config a b c) e.k)
    embed q := e.C_orig.embed ∘ q
    project q := e.C_orig.project ∘ q
  }


  lemma compression_k_step (c: Config e.C_orig.Q):
      e.C.next (compress e.k c) = compress e.k (e.C_orig.nextt c e.k) := by
    funext p j
    simp [CellAutomaton.next, C, compress, to_local_config]
    rw [add_comm (p * e.k) j]
    rw [nextt_shift]
    apply nextt_locality
    intro y hy
    have hk : (e.k : ℤ) ≥ 1 := by
      have : e.k ≠ 0 := NeZero.ne e.k
      omega
    have hj : 0 ≤ (j : ℤ) ∧ (j : ℤ) < e.k := by
      constructor
      · simp
      · simp
    unfold local_config
    split_ifs with h1 h2 h3
    · -- y <= -k
      have : y = -e.k := by omega
      subst y
      unfold compress
      rw [intCastEq]
      simp
      apply congrArg
      ring
    · -- -k < y < 0
      unfold compress
      rw [intCastEq]
      have h_pos : 0 ≤ y + ↑e.k := by omega
      have h_lt : y + ↑e.k < ↑e.k := by omega
      rw [Int.emod_eq_of_lt h_pos h_lt]
      apply congrArg
      ring
    · -- 0 <= y < k
      unfold compress
      rw [intCastEq]
      have h_pos : 0 ≤ y := by omega
      have h_lt : y < ↑e.k := by omega
      rw [Int.emod_eq_of_lt h_pos h_lt]
      apply congrArg
      ring
    · -- k <= y
      unfold compress
      rw [intCastEq]
      have h_pos : 0 ≤ y - ↑e.k := by omega
      have h_lt : y - ↑e.k < ↑e.k := by omega
      rw [Int.emod_eq_of_lt h_pos h_lt]
      apply congrArg
      ring

  theorem spec {c: Config e.α}:
      ∀ t, e.C.comp ⦋(compress e.k c)⦌ t = compress e.k (e.C_orig.comp c (e.k * t)) := by
    intro t
    unfold CellAutomaton.comp CellAutomaton.project_config
    funext p
    let c_orig : Config e.C_orig.Q := c
    have h_comm : (⦋compress e.k c⦌: Config e.C.Q) = compress e.k c_orig := by
      funext p j
      simp [compress, CellAutomaton.embed_config, C]
      rfl
    dsimp [CellAutomaton.embed_config] at h_comm ⊢
    change e.C.project ((e.C.nextt (e.C.embed_config (compress e.k c)) t) p) = _
    have h_eq : e.C.nextt ⦋compress e.k c⦌ t = e.C.nextt (compress e.k c_orig) t := by
      congr 1
    rw [h_eq]
    have h_state : e.C.nextt (compress e.k c_orig) t = compress e.k (e.C_orig.nextt c_orig (e.k * t)) := by
      induction t with
      | zero => simp
      | succ t ih =>
        rw [CellAutomaton.nextt_succ]
        rw [ih]
        rw [compression_k_step]
        rw [mul_add, mul_one]
        rw [nextt_add]
        grind
    rw [h_state]
    unfold compress
    simp [C]
    rfl

  theorem spec1 {c: Config e.α} {t1: ℕ}:
      e.C.trace (compress e.k c) t1 0 = e.C_orig.trace c (e.k * t1) := by
    unfold trace
    rw [e.spec]
    unfold compress
    simp

end SpeedupKx

structure TraceKx where
  k: ℕ
  α: Type
  β: Type
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [inst: NeZero k]
  C_orig: CellAutomaton α β

namespace TraceKx

  variable (e: TraceKx)

  def C: CellAutomaton e.α (Fin e.k → e.β？) := {
    Q := Fin (e.k + 1) → e.C_orig.Q
    δ := fun a b c =>
      let next_s := e.C_orig.δ (a (Fin.last e.k)) (b (Fin.last e.k)) (c (Fin.last e.k))
      Fin.snoc (Fin.tail b) next_s
    embed := fun a =>
      let s := e.C_orig.embed a
      fun _ => s
    project := fun q =>
      fun i => some (e.C_orig.project (q (i.castSucc)))
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

  theorem spec (c: Config e.α) (t1: ℕ) (p: ℤ):
      e.C.comp c (t1 + e.k) p =
        fun (t2: Fin e.k) => some (e.C_orig.comp c (t1 + t2) p)
      := by
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [C]
    simp
    change (fun (t2 : Fin e.k) => some (e.C_orig.project ((e.C.nextt ⦋c⦌ (t1 + e.k) p) t2.castSucc))) = _
    funext t2
    rw [state_eq]
    congr
    simp
    rw [Nat.add_right_comm]
    rw [Nat.add_sub_cancel]

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

  def T: TraceKx := {
    k := e.k
    α := e.α
    β := e.β
    C_orig := e.C_orig
  }
  example : (CellAutomaton e.α (Fin e.k → e.β？)) := e.T.C

  def SP: SpeedupKx := {
    k := e.k
    α := e.α
    β := Fin e.k → e.β？
    C_orig := e.T.C
  }
  example : (CellAutomaton (Fin e.k → e.α) (Fin e.k → (Fin e.k → e.β？))) := e.SP.C

  def C: CellAutomaton (Fin e.k → e.α) (Fin e.k → e.β) :=
    e.SP.C.map_project (fun f => fun i => (f 0 i).getD default)

  theorem spec1 {c: Config e.α} {t1: ℕ} {t2: Fin e.k}:
      e.C.trace (SpeedupKx.compress e.k c) (t1 + 1) t2 = e.C_orig.trace c (e.k * t1 + t2) := by
    unfold trace
    have h_comp : ∀ t p, e.C.comp ⦋SpeedupKx.compress e.k c⦌ t p = (fun g i => (g 0 i).getD default) (e.SP.C.comp ⦋SpeedupKx.compress e.k c⦌ t p) := by
      intros t p
      unfold CellAutomaton.comp CellAutomaton.project_config
      simp [C]
      rfl
    rw [h_comp]
    have h_spec : e.SP.C.comp ⦋SpeedupKx.compress e.k c⦌ (t1 + 1) = SpeedupKx.compress e.k (e.T.C.comp c (e.k * (t1 + 1))) := by
      convert e.SP.spec (t1 + 1)
    rw [h_spec]
    unfold SpeedupKx.compress
    simp only
    rw [mul_add, mul_one]
    have h_spec_T : e.T.C.comp c (e.k * t1 + e.k) 0 = fun (t2 : Fin e.k) => some (e.C_orig.comp c (e.k * t1 + t2) 0) := by
      convert e.T.spec c (e.k * t1) 0
    simp only [zero_mul, zero_add]
    erw [h_spec_T]
    simp


end SpeedupAndTraceKx

end CellularAutomatas
