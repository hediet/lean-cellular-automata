import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
namespace CellularAutomatas

open CellAutomaton

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
    simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold]
    funext p
    let c_orig : Config e.C_orig.Q := c
    have h_comm : (⦋compress e.k c⦌: Config e.C.Q) = compress e.k c_orig := by
      funext p j
      simp [compress, CellAutomaton.embed_config, C]
      rfl
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

end CellularAutomatas
