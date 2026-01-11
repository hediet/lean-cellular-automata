--import CellularAutomatas.defs
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


namespace CellularAutomatas

notation:max t "？" => Option t

notation:max x "³"  => Fin 3 → x

class Alphabet (α: Type) where
    [dec: DecidableEq α]
    [fin: Fintype α]
    [inh: Inhabited α]

attribute [instance] Alphabet.dec Alphabet.fin Alphabet.inh

instance (α: Type) [DecidableEq α] [Fintype α] [Inhabited α]: Alphabet α := {}


def Config (Q: Type) := ℤ → Q
def Trace (Q: Type) := ℕ → Q

abbrev Word (α: Type) := List α

def word_to_config {α : Type} (w : Word α) : Config (Option α) :=
  fun p => if h : p ≥ 0 ∧ p < w.length then some w[p.toNat] else none

notation "⟬" w "⟭" => word_to_config w

instance : Coe (Word α) (Config α？) := ⟨word_to_config⟩



structure CellAutomaton (α β: Type) where
  Q: Type
  [alphabetQ: Alphabet Q]
  δ: Q → Q → Q → Q
  embed: α → Q
  project: Q → β

attribute [instance] CellAutomaton.alphabetQ

namespace CellAutomaton

  def embed_config {α β: Type} {C: CellAutomaton α β} (c: Config α) : Config C.Q :=
    fun p => C.embed (c p)

  notation "⦋" w "⦌"  => embed_config w

  instance {C: CellAutomaton α β} : Coe (Config α) (Config C.Q) := ⟨embed_config⟩


  def embed_word {α β: Type} {C: CellAutomaton α？ β} (w: Word α): Config C.Q := word_to_config w

  notation "⦋" w "⦌" => embed_word w

  instance {C: CellAutomaton α？ β} : Coe (Word α) (Config C.Q) := ⟨embed_word⟩

  @[simp]
  lemma embed_word_word_to_config_eq {α β: Type} {C: CellAutomaton α？ β} (w: Word α):
      C.embed_config (word_to_config w) = ⦋w⦌ := rfl

  def project_config {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): Config β :=
    fun p => C.project (c p)

  def next {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): Config C.Q :=
    fun p => C.δ (c (p - 1)) (c p) (c (p + 1))

  def nextt {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t: ℕ): Config C.Q :=
    Nat.iterate (C.next) t c

  @[simp]
  lemma nextt_zero {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): C.nextt c 0 = c := rfl

  @[simp]
  lemma nextt_succ {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t: ℕ): C.nextt c (t + 1) = C.next (C.nextt c t) := by
    simp [nextt, Function.iterate_succ_apply']

  def comp {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): Trace (Config β) :=
    C.project_config ∘ C.nextt c

  def trace {α β: Type} (C: CellAutomaton α β) (c: Config α): Trace β := (C.comp c · 0)

  def trace_rt {α β: Type} (C: CellAutomaton α？ β) (w: Word α): Word β :=
    (List.range w.length).map (C.trace w)

  def map_project {α β γ: Type} (C: CellAutomaton α β) (f: β → γ): CellAutomaton α γ :=
    {
      Q := C.Q
      δ := C.δ
      embed := C.embed
      project := f ∘ C.project
    }

  @[simp]
  lemma map_project_nextt {α β γ: Type} (C: CellAutomaton α β) (f: β → γ) (c: Config C.Q) (t: ℕ):
    (C.map_project f).nextt c t = C.nextt c t := by
    induction t generalizing c with
    | zero => simp
    | succ t ih =>
      rw [nextt_succ, nextt_succ]
      rw [ih]
      rfl

end CellAutomaton






abbrev LCellAutomaton (α: Type) := CellAutomaton α？ Bool

structure tCellAutomaton (α: Type) extends LCellAutomaton α where
  t: ℕ → ℕ
  p: ℕ → ℤ

def tCellAutomaton.accepts {C: tCellAutomaton α} (w: Word α) := C.comp w (C.t w.length) (C.p w.length)


open CellAutomaton

@[grind =]
lemma word_to_config_natcast_eq {w: Word α} {t: ℕ} (h: t < w.length): ⟬w⟭ ↑t = some w[t] := by simp [word_to_config, h]


lemma trace_rt_of_map_project {α β γ: Type} {C: CellAutomaton α？ β} (f: β → γ) (w: Word α):
      (C.map_project f).trace_rt w = (C.trace_rt w).map f := by
  unfold trace_rt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  unfold trace comp project_config
  simp
  unfold map_project
  rfl

@[simp]
lemma trace_rt_length {α β: Type} {C: CellAutomaton α？ β} {w: Word α}:
  (C.trace_rt w).length = w.length := by simp [trace_rt]






section id

  def ca_id (α : Type) [Alphabet α] : CellAutomaton α α := {
    Q := α
    δ := fun _ _ r => r
    embed := id
    project := id
  }

  def config_to_trace {α: Type} (c: Config α): Trace α := fun t => c t

  @[simp]
  lemma ca_id_trace_eq {α : Type} [Alphabet α]:
    (ca_id α).trace = config_to_trace := by
    unfold trace
    funext t
    conv in comp _ => change nextt _

    have shift_next c : (ca_id α).next c = fun i => c (i + 1) := by
      funext i
      simp [CellAutomaton.next, ca_id]

    have shift_nextt k c i: ((ca_id α).nextt c k) i = c (i + k) := by
      induction k generalizing c i with
      | zero =>
        simp
      | succ k ih =>
        rw [CellAutomaton.nextt_succ]
        rw [shift_next]
        simp
        rw [ih]
        grind
    funext t
    rw [shift_nextt]
    conv in embed_config => change id
    simp [config_to_trace]



  def ca_id_word (α: Type) [Alphabet α] : CellAutomaton α？ α := (ca_id α？).map_project (·.getD default)

  @[simp]
  lemma ca_id_scan_temporal [Alphabet α]: (ca_id_word α).trace_rt = id := by
    funext w
    rw [id_eq, ca_id_word, trace_rt_of_map_project]
    apply List.ext_getElem (by simp)
    intro i h_i h_len
    unfold trace_rt
    simp [ca_id_trace_eq]
    grind [ca_id_trace_eq, config_to_trace]

end id










def triple_at {Q} (c: ℕ → Q) (i: ℕ): Q³ := fun o => c (i + o)




structure CompressToDiag where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α？ β

attribute [instance] CompressToDiag._inst_α
attribute [instance] CompressToDiag._inst_β

namespace CompressToDiag

  variable (e: CompressToDiag)

  def C: CellAutomaton e.α？ (Option (e.β³)) := sorry

  theorem spec (w: Word e.α) (t: ℕ) (p: ℤ):
      e.C.comp w t p =
        if p >= 0 ∧ t = 2 * p + 3
        then some (triple_at (e.C_orig.comp w · 0) (3 * p).natAbs)
        else none
        := by
    sorry

end CompressToDiag







structure CompressToΛ where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α？ β？

attribute [instance] CompressToΛ._inst_α
attribute [instance] CompressToΛ._inst_β

namespace CompressToΛ
  variable (e: CompressToΛ)

  def C: CellAutomaton e.α？ ((e.β？)³)？ := sorry

  def decode_cfg (w: Word e.α): Config ((e.β？)³) :=
    fun p =>
      if p ≥ 0
      then triple_at (e.C_orig.trace w) (3 * p).natAbs
      else (fun _ => none)

  theorem spec (w: Word e.α) (t: ℕ) (p: ℤ):
      e.C.comp w t p =
        if t = 3 + 2 * p.natAbs
        then some (e.decode_cfg w p)
        else none
        := by
    sorry

end CompressToΛ

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

lemma nextt_shift {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t: ℕ) (x d: ℤ):
    C.nextt c t (x + d) = C.nextt (fun i => c (i + d)) t x := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [nextt_succ, nextt_succ]
    unfold CellAutomaton.next
    have h1 : x + d - 1 = x - 1 + d := by ring
    have h2 : x + d + 1 = x + 1 + d := by ring
    rw [h1, h2]
    rw [ih (x-1), ih x, ih (x+1)]

lemma nextt_locality {α β: Type} (C: CellAutomaton α β) (c1 c2: Config C.Q) (t: ℕ) (x: ℤ):
    (∀ y, x - t ≤ y ∧ y ≤ x + t → c1 y = c2 y) → C.nextt c1 t x = C.nextt c2 t x := by
  induction t generalizing x with
  | zero =>
    intro h
    apply h
    simp
  | succ t ih =>
    intro h
    rw [nextt_succ, nextt_succ]
    unfold CellAutomaton.next
    grind



lemma nextt_add {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t1 t2: ℕ):
    C.nextt c (t1 + t2) = C.nextt (C.nextt c t1) t2 := by
  rw [Nat.add_comm]
  rw [nextt, Function.iterate_add_apply]
  rfl

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
    let c_orig : Config e.C_orig.Q := ⦋c⦌
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
      simp [CellAutomaton.next, C]
      rw [ih (p-1), ih p, ih (p+1)]
      rfl

  def T (t: ℕ) (p: ℤ) (k: ℕ) := 3 * t + 3 + 2 * p.natAbs + k

  lemma T_reset_iff (t: ℕ) (p: ℤ) (k: Fin 3):
    T t p k = 3 + 2 * p.natAbs ↔ t = 0 ∧ k = 0 := by
    unfold T
    constructor
    · intro h
      have : 3 * t + k = 0 := by linarith
      have : 3 * t = 0 := by linarith
      have : k.val = 0 := by linarith
      simp_all
      apply Fin.eq_of_val_eq
      assumption
    · intro h
      rcases h with ⟨rfl, rfl⟩
      simp

  theorem spec (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (t: ℕ):
    e.C.trace c_ctl (3 * t + 3) = some (e.C_inr.trace c_inr t) := by
    unfold trace
    have h_inv (τ: ℕ) (t: ℕ) (p: ℤ) (k: Fin 3) (h_time: T t p k = τ):
      let q := e.C.nextt ⦋c_ctl⦌ τ p
      q.sim = some (e.C_inr.nextt ⦋c_inr⦌ t p, e.C_inr.nextt ⦋c_inr⦌ (t - 1) p) ∧
      q.counter = k := by
      induction τ using Nat.strong_induction_on generalizing t p k with
      | h τ ih =>
        subst τ
        let q := e.C.nextt ⦋c_ctl⦌ (T t p k) p
        by_cases h_reset : t = 0 ∧ k = 0
        · -- Reset case
          rcases h_reset with ⟨rfl, rfl⟩
          simp [T]
          have h_ctl := h_CM 0 p
          simp at h_ctl

          have h_state_eq := e.state_track c_ctl (T 0 p 0) p
          have h_proj : e.C_ctl.project (e.C.nextt ⦋c_ctl⦌ (T 0 p 0) p).state = some (c_inr p) := by
            rw [h_state_eq]
            exact h_ctl

          have h_struct : ∀ q, q = e.C.nextt ⦋c_ctl⦌ (T 0 p 0) p →
            match e.C_ctl.project q.state with
            | some s => q.sim = some (e.C_inr.embed s, e.C_inr.embed s) ∧ q.counter = 0
            | none => True := by
              intro q hq
              rw [hq]
              have h_pos : T 0 p 0 > 0 := by unfold T; linarith
              let t_prev := T 0 p 0 - 1
              have h_t : T 0 p 0 = t_prev + 1 := by omega
              rw [h_t, CellAutomaton.nextt_succ]
              simp [CellAutomaton.next, C]
              split
              · simp
              · simp

          specialize h_struct _ rfl
          rw [h_proj] at h_struct
          rcases h_struct with ⟨h_sim_eq, h_cnt_eq⟩
          constructor
          · rw [h_sim_eq]
            simp
            rfl
          · exact h_cnt_eq

        · -- Non-reset case
          have h_not_reset : T t p k ≠ 3 + 2 * p.natAbs := by
             intro h_eq
             rw [T_reset_iff] at h_eq
             contradiction

          have h_struct : ∀ q, q = e.C.nextt ⦋c_ctl⦌ (T t p k) p →
            match e.C_ctl.project q.state with
            | some _ => True
            | none =>
               let q_prev := e.C.nextt ⦋c_ctl⦌ (T t p k - 1) p
               match q_prev.sim with
               | some (new_b, old_b) =>
                 if q_prev.counter == 2 then
                   let val_a := e.get_neighbor_val (e.C.nextt ⦋c_ctl⦌ (T t p k - 1) (p - 1))
                   let val_c := e.get_neighbor_val (e.C.nextt ⦋c_ctl⦌ (T t p k - 1) (p + 1))
                   let next_val := e.C_inr.δ val_a new_b val_c
                   q.sim = some (next_val, new_b) ∧ q.counter = 0
                 else
                   q.sim = some (new_b, old_b) ∧ q.counter = q_prev.counter + 1
               | none => q.sim = none ∧ q.counter = 0
               := by
              intro q hq
              rw [hq]
              have h_pos : T t p k > 0 := by unfold T; linarith
              let t_prev := T t p k - 1
              have h_t : T t p k = t_prev + 1 := by omega
              rw [h_t, CellAutomaton.nextt_succ]
              simp [CellAutomaton.next, C]
              split
              · simp
              · simp
                split
                · split
                  · simp
                  · simp
                · simp

          have h_proj_none : e.C_ctl.project (e.C.nextt ⦋c_ctl⦌ (T t p k) p).state = none := by
            rw [e.state_track]
            have := h_CM (T t p k) p
            simp at this
            rw [if_neg h_not_reset] at this
            exact this

          specialize h_struct _ rfl
          rw [h_proj_none] at h_struct

          -- Predecessor time
          let τ_prev := T t p k - 1

          by_cases hk_zero : k.val = 0
          · -- k = 0. Predecessor is k=2 at t-1.
            have ht_pos : t > 0 := by
              by_contra h
              have : t = 0 := Nat.eq_zero_of_nonpos t h
              subst t
              have : k = 0 := Fin.eq_of_val_eq hk_zero
              subst k
              contradiction -- h_reset

            let t_prev := t - 1
            have ht : t = t_prev + 1 := by omega
            let k_prev : Fin 3 := 2

            have h_time_prev : T t_prev p k_prev = τ_prev := by
              unfold T
              rw [ht]
              simp
              omega

            have h_prev := ih τ_prev (by unfold T; linarith) t_prev p k_prev h_time_prev
            rcases h_prev with ⟨h_sim_prev, h_cnt_prev⟩

            rw [h_sim_prev] at h_struct
            rw [h_cnt_prev] at h_struct

            -- counter == 2 is true
            simp at h_struct

            -- Need neighbors
            let τ_prev_L := T t_prev p k_prev

            -- Left neighbor
            let t_L := if p > 0 then t else t_prev
            let k_L : Fin 3 := if p > 0 then 1 else 0
            have h_L_time : T t_L (p - 1) k_L = τ_prev := by
              unfold T
              split_ifs
              · -- p > 0
                have : (p - 1).natAbs = p.natAbs - 1 := by
                   rw [Int.natAbs_sub_pos]
                   omega
                   omega
                rw [this]
                rw [ht]
                omega
              · -- p <= 0
                have : (p - 1).natAbs = p.natAbs + 1 := by
                   rw [Int.natAbs_sub_neg]
                   omega
                   omega
                rw [this]
                omega

            have h_L := ih τ_prev (by unfold T; linarith) t_L (p - 1) k_L h_L_time
            rcases h_L with ⟨h_sim_L, h_cnt_L⟩

            -- Right neighbor
            let t_R := if p < 0 then t else t_prev
            let k_R : Fin 3 := if p < 0 then 1 else 0
            have h_R_time : T t_R (p + 1) k_R = τ_prev := by
              unfold T
              split_ifs
              · -- p < 0
                have : (p + 1).natAbs = p.natAbs - 1 := by
                   rw [Int.natAbs_add_neg]
                   omega
                   omega
                rw [this]
                rw [ht]
                omega
              · -- p >= 0
                have : (p + 1).natAbs = p.natAbs + 1 := by
                   rw [Int.natAbs_add_pos]
                   omega
                   omega
                rw [this]
                omega

            have h_R := ih τ_prev (by unfold T; linarith) t_R (p + 1) k_R h_R_time
            rcases h_R with ⟨h_sim_R, h_cnt_R⟩

            -- Evaluate get_neighbor_val
            have h_val_a : e.get_neighbor_val (e.C.nextt ⦋c_ctl⦌ τ_prev (p - 1)) = e.C_inr.nextt ⦋c_inr⦌ (t - 1) (p - 1) := by
               rw [←h_L_time]
               unfold get_neighbor_val
               rw [h_sim_L, h_cnt_L]
               simp
               split_ifs with h_cnt
               · -- k_L == 1. Means p > 0.
                 -- t_L = t.
                 -- old value is nextt ... (t-1). Correct.
                 have : p > 0 := by
                    by_contra h_neg
                    simp [k_L] at h_cnt
                    simp [h_neg] at h_cnt
                    contradiction
                 simp [t_L, this] at h_sim_L
                 rfl
               · -- k_L != 1. Means p <= 0. k_L = 0.
                 -- t_L = t_prev = t - 1.
                 -- new value is nextt ... t_prev = nextt ... (t-1). Correct.
                 have : p <= 0 := by
                    by_contra h_pos
                    simp [k_L] at h_cnt
                    simp [h_pos] at h_cnt
                 simp [t_L, this] at h_sim_L
                 rw [ht]
                 rfl

            have h_val_c : e.get_neighbor_val (e.C.nextt ⦋c_ctl⦌ τ_prev (p + 1)) = e.C_inr.nextt ⦋c_inr⦌ (t - 1) (p + 1) := by
               rw [←h_R_time]
               unfold get_neighbor_val
               rw [h_sim_R, h_cnt_R]
               simp
               split_ifs with h_cnt
               · -- k_R == 1. Means p < 0.
                 -- t_R = t.
                 -- old value is nextt ... (t-1). Correct.
                 have : p < 0 := by
                    by_contra h_pos
                    simp [k_R] at h_cnt
                    simp [h_pos] at h_cnt
                    contradiction
                 simp [t_R, this] at h_sim_R
                 rfl
               · -- k_R != 1. Means p >= 0. k_R = 0.
                 -- t_R = t_prev = t - 1.
                 -- new value is nextt ... t_prev = nextt ... (t-1). Correct.
                 have : p >= 0 := by
                    by_contra h_neg
                    simp [k_R] at h_cnt
                    simp [h_neg] at h_cnt
                 simp [t_R, this] at h_sim_R
                 rw [ht]
                 rfl

            rw [h_val_a, h_val_c] at h_struct

            -- next_val = δ (nextt (t-1) (p-1)) (nextt (t-1) p) (nextt (t-1) (p+1))
            -- = nextt t p.
            have h_next : e.C_inr.δ (e.C_inr.nextt ⦋c_inr⦌ (t - 1) (p - 1)) (e.C_inr.nextt ⦋c_inr⦌ (t - 1) p) (e.C_inr.nextt ⦋c_inr⦌ (t - 1) (p + 1)) = e.C_inr.nextt ⦋c_inr⦌ t p := by
               rw [ht, CellAutomaton.nextt_succ]
               rfl

            rw [h_next] at h_struct
            rcases h_struct with ⟨h_sim_res, h_cnt_res⟩
            constructor
            · rw [h_sim_res]
              simp
              rw [ht]
              rfl
            · rw [h_cnt_res]
              apply Fin.eq_of_val_eq
              simp [hk_zero]

          · -- k != 0. Predecessor is k-1 at t.
            let k_prev : Fin 3 := ⟨k.val - 1, by
               have : k.val > 0 := by
                  apply Nat.pos_of_ne_zero
                  intro h
                  apply hk_zero
                  exact h
               have : k.val < 3 := k.isLt
               omega
            ⟩
            have h_time_prev : T t p k_prev = τ_prev := by
               unfold T
               simp
               omega

            have h_prev := ih τ_prev (by unfold T; linarith) t p k_prev h_time_prev
            rcases h_prev with ⟨h_sim_prev, h_cnt_prev⟩

            rw [h_sim_prev] at h_struct
            rw [h_cnt_prev] at h_struct

            -- counter == 2 is false (since k_prev < 2)
            -- k_prev = k-1. k <= 2.
            -- If k=1, k_prev=0. 0 != 2.
            -- If k=2, k_prev=1. 1 != 2.
            have h_not_two : k_prev ≠ 2 := by
               intro h
               have : k.val - 1 = 2 := by
                  rw [←h]
                  rfl
               have : k.val = 3 := by omega
               have : k.val < 3 := k.isLt
               linarith

            simp [h_not_two] at h_struct
            rcases h_struct with ⟨h_sim_res, h_cnt_res⟩
            constructor
            · exact h_sim_res
            · rw [h_cnt_res]
              apply Fin.eq_of_val_eq
              simp
              omega

    have h := h_inv (T t 0 0) t 0 0 rfl
    rcases h with ⟨h_sim, h_cnt⟩
    unfold trace
    simp [CellAutomaton.comp, CellAutomaton.project_config]
    rw [h_sim]
    simp [C]
    rfl
end SimFromΛ


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

  def C (e: DecompressTriple): CellAutomaton e.α (e.β) := sorry


  theorem spec (c: Config e.α) (t: ℕ) (v: (e.β³))
    (h: ∀ o: Fin 3, e.C_orig.comp c (t + o) 0 = if o == 0 then some v else none):
      ∀ o: Fin 3, (e.C.comp c (t + o) 0) = some (v o) := by
    sorry


  def h_cond (c: Config e.α) (k: ℕ): Prop :=
      ∀ (t: ℕ), ((e.C_orig.trace c (t + k))).isSome == ((t - k) % 3 == 0)


  theorem spec2 (c: Config e.α) (h: e.h_cond c k) (t1: ℕ) (t2: Fin 3):
        e.C.trace c (3 * t1 + t2 + k) = (e.C_orig.trace c (3 * t1 + k)).get (sorry) t2
      := by
    -- should be simple to prove from spec
    sorry

end DecompressTriple




structure SpeedupKSteps where
  {α: Type}
  {β: Type}
  [inst1: Alphabet α]
  [inst2: Alphabet β]
  C_orig: CellAutomaton α？ β
  k: ℕ

attribute [instance] SpeedupKSteps.inst1
attribute [instance] SpeedupKSteps.inst2

namespace SpeedupKSteps

  variable (e: SpeedupKSteps)

  def C: CellAutomaton e.α？ e.β := sorry

  lemma inv (w: Word e.α): e.C.trace w w.length = e.C_orig.trace w (w.length + e.k) := sorry

  theorem spec (w: Word e.α): e.C.trace w i = e.C_orig.trace w (i + e.k) := sorry
    -- Use inv with "e.C.trace w i = e.C.trace w[0..i] w[0..i].length"

end SpeedupKSteps




structure AddBorder where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α？ β

namespace AddBorder
  variable (e: AddBorder)

  def b := e.C_orig.embed none

  def C: CellAutomaton e.α？ e.β？ := {
    Q := e.C_orig.Q？
    δ := fun a b c =>
      match b, c with
      | some vb, some vc => some (e.C_orig.δ (a.getD e.b) vb vc)
      | _, _ => none
    embed := fun
      | some a => some (e.C_orig.embed (some a))
      | none => none
    project := Option.map e.C_orig.project
  }

  theorem spec (w: Word e.α): e.C.trace w = config_to_trace (e.C_orig.trace_rt w) := by
    sorry

end AddBorder



structure Composition where
  α: Type
  β: Type
  γ: Type
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [_inst_γ: Alphabet γ]
  C2: CellAutomaton β？ γ
  C1: CellAutomaton α？ β

attribute [instance] Composition._inst_α
attribute [instance] Composition._inst_β
attribute [instance] Composition._inst_γ


namespace Composition
  variable (e: Composition)

  def C1': AddBorder := { C_orig := e.C1 }
  example : (CellAutomaton e.α？ e.β？) := e.C1'.C

  abbrev C1_Λ: CompressToΛ := {
    α := e.α
    β := e.β
    C_orig := e.C1'.C
  }
  example : (CellAutomaton e.α？ e.β？³？) := e.C1_Λ.C

  abbrev C2_3x: SpeedupAndTraceKx := {
    k := 3
    α := e.β？
    β := e.γ
    C_orig := e.C2
  }
  example : (CellAutomaton e.β？³ e.γ³) := e.C2_3x.C

  abbrev C_sim: SimFromΛ := {
    α := e.α？
    β := e.β？³
    γ := e.γ³
    C_ctl := e.C1_Λ.C
    C_inr := e.C2_3x.C
  }
  example : (CellAutomaton e.α？ e.γ³？) := e.C_sim.C

  abbrev C_decomp: DecompressTriple := {
    C_orig := e.C_sim.C
  }
  example : (CellAutomaton e.α？ e.γ) := e.C_decomp.C

  abbrev C_exact: SpeedupKSteps := {
    C_orig := e.C_decomp.C
    k := 6
  }

  def C : (CellAutomaton e.α？ e.γ) := e.C_exact.C



  theorem spec: e.C.trace_rt = e.C2.trace_rt ∘ e.C1.trace_rt := by
    funext w
    apply List.ext_getElem (by simp)
    intro t h1 h2

    obtain ⟨t₁, t₂, ht⟩: ∃ t1: ℕ, ∃ t2: Fin 3, t = 3 * t1 + t2 := by
      use t / 3
      use ⟨t % 3, Nat.mod_lt _ (by decide)⟩
      simp [Nat.div_add_mod]

    let c_inr: Config e.β？³ := SpeedupKx.compress 3 (word_to_config (e.C1.trace_rt w))
    have x: e.C_sim.c_ctl_computes_c_inr ⟬w⟭ c_inr := by
      unfold SimFromΛ.c_ctl_computes_c_inr
      intro t p
      simp
      rw [CompressToΛ.spec]
      congr
      unfold CompressToΛ.decode_cfg

      sorry

    calc (e.C.trace_rt w)[t]
      = (e.C.trace w) t := by simp [trace_rt]
      _ = e.C_exact.C.trace ⟬w⟭ t := by rfl
      _ = e.C_decomp.C.trace ⟬w⟭ (t + 6) := by rw [SpeedupKSteps.spec]
      _ = e.C_decomp.C.trace ⟬w⟭ (t + 3 + 3) := by simp
      _ = e.C_decomp.C.trace ⟬w⟭ (3 * t₁ + t₂ + 3 + 3) := by rw [ht]
      _ = e.C_decomp.C.trace ⟬w⟭ (3 * (t₁ + 1) + t₂ + 3) := by ring_nf
      _ = (e.C_sim.C.trace ⟬w⟭ (3 * (t₁ + 1) + 3)).get (sorry) t₂ := by
        rw [DecompressTriple.spec2]
        change ∀ (t : ℕ), ((e.C_sim.C.trace ⟬w⟭ (t + 3))).isSome == ((t - 3) % 3 == 0)

        sorry

      _ = (some (e.C2_3x.C.trace c_inr (t₁ + 1))).get (sorry) t₂ := by rw [e.C_sim.spec _ _ x]
      _ = e.C2_3x.C.trace c_inr (t₁ + 1) t₂ := by rfl
      _ = e.C2.trace ⟬e.C1.trace_rt w⟭ (3 * t₁ + t₂) := by

        rw [SpeedupAndTraceKx.spec1]

      _ = e.C2.trace ⟬e.C1.trace_rt w⟭ t := by rw [ht]
      _ = (e.C2.trace_rt (e.C1.trace_rt w))[t] := by simp [trace_rt]


end Composition
