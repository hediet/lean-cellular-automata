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
  unfold trace comp project_config map_project
  simp
  congr 1

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
      induction k generalizing c with
      | zero =>
        simp [CellAutomaton.nextt, Nat.iterate]
      | succ k ih =>
        rw [CellAutomaton.nextt, Nat.iterate]
        rw [shift_next]
        rw [← CellAutomaton.nextt]
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

lemma intCastEq {k: ℕ} [NeZero k] (p: ℤ): (Fin.intCast p: Fin k) = (p % k) := by
  sorry



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
      e.C.next (compress e.k c) = compress e.k (e.C_orig.nextt c e.k) :=
        sorry

  theorem spec {c: Config e.α}:
      ∀ t, e.C.comp ⦋(compress e.k c)⦌ t = compress e.k (e.C_orig.comp c (e.k * t)) :=
        sorry

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

  -- cell at (t + k,p) has state of orig at (t + {0,1,...,k-1}, p)
  def C: CellAutomaton e.α (Fin e.k → e.β？) := sorry

  theorem spec (c: Config e.α) (t1: ℕ) (p: ℤ):
      e.C.comp c (t1 + e.k) p =
        fun (t2: Fin e.k) => some (e.C_orig.comp c (t1 + t2) p)
      := by
    sorry
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
        sorry


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

  structure Q1 where
    state: e.C_ctl.Q
    counter: Fin 3
  deriving Inhabited, DecidableEq

  -- TODO@hediet - why cannot I derive Fintype automatically here?
  instance : Fintype (Q1 e) :=
    Fintype.ofEquiv (e.C_ctl.Q × Fin 3)
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => (x.1, x.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }


  def C: CellAutomaton e.α e.γ？ := {
    Q := Option (Q1 e × e.C_inr.Q)
    δ := fun a b c =>
      match (a, b, c) with
      | (some qa, some (qb, _), some qc) =>
        if qb.counter = 2
        then sorry
        else none
      | _ => none
    embed := sorry
    project := sorry
  }

  variable (c_ctl: Config e.α)
  variable (c_inr: Config e.β)

  def c_ctl_computes_c_inr: Prop :=
    ∀ (t: ℕ) (p: ℤ),
    e.C_ctl.comp c_ctl t p =
      if t = 3 + 2 * p.natAbs
      then some (c_inr p)
      else none


  theorem spec (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (t: ℕ):
    e.C.trace c_ctl (3 * t + 3) = some (e.C_inr.trace c_inr t) := by
      sorry
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
        e.C.trace c (3 * t1 + t2 + k) =
          (e.C_orig.trace c (3 * t1 + k)).get (sorry) t2
      := by
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

  lemma spec1 (w: Word e.α): e.C.trace w w.length = e.C_orig.trace w (w.length + e.k) := sorry

  theorem spec (w: Word e.α): e.C.trace w i = e.C_orig.trace w (i + e.k) := sorry
    -- e.C.trace w i = e.C.trace w[0..i] w[0..i].length

end SpeedupKSteps




structure AddBorder where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α？ β

namespace AddBorder
  variable (e: AddBorder)

  def C: CellAutomaton e.α？ e.β？ := {
    Q := e.C_orig.Q
    δ := e.C_orig.δ
    embed := e.C_orig.embed
    project := sorry
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
