import CellularAutomatas.defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring

namespace CellularAutomatas

private lemma list_map_congr {α β} {f g : α → β} {l : List α} (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
  simp only [List.map_cons, List.cons.injEq]
  constructor
  · apply h; simp
  · apply ih; intro x hx; apply h; simp [hx]


lemma nextt_congr (C: CellAutomaton) (c1 c2: Config C.Q) (t: ℕ) (i: ℤ):
    (∀ j, i - t ≤ j ∧ j ≤ i + t → c1 j = c2 j) →
    (C.nextt c1 t) i = (C.nextt c2 t) i := by
  induction t generalizing i c1 c2 with
  | zero =>
    intro h
    simp [CellAutomaton.nextt, apply_iterated]
    apply h
    constructor <;> omega
  | succ t ih =>
    intro h
    simp [CellAutomaton.nextt, apply_iterated]
    -- The goal is now nextt (next c1) t i = nextt (next c2) t i
    apply ih
    intro j hj
    unfold CellAutomaton.next
    congr 1
    · apply h
      constructor <;> omega
    · apply h
      constructor <;> omega
    · apply h
      constructor <;> omega

theorem LCellAutomaton.scan_temporal_independence [Alphabet α] (C: LCellAutomaton α) (p s: Word α):
  (C.scan_temporal_rt (p ++ s)).take p.length = C.scan_temporal_rt p := by
  unfold LCellAutomaton.scan_temporal_rt LCellAutomaton.scan_temporal
  rw [← List.map_take, List.take_range, min_eq_left (by simp)]
  apply list_map_congr
  intro t ht
  rw [List.mem_range] at ht
  apply nextt_congr
  intro j hj
  unfold LCellAutomaton.embed_word
  split_ifs with h1 h2
  · congr 1
    unfold Word.get'
    simp only [List.get_eq_getElem]
    apply List.getElem_append_left
  · exfalso; unfold Word.range at *; simp at *; omega
  · exfalso; unfold Word.range at *; simp at *; omega
  · rfl

theorem CArtTransducer.scan_temporal_independence [Alphabet α] [Alphabet Γ] (C: CArtTransducer α Γ) (p s: Word α):
  (C.advice.f (p ++ s)).take p.length = C.advice.f p := by
  unfold CArtTransducer.advice
  simp
  rw [←List.map_take]
  rw [LCellAutomaton.scan_temporal_independence]






section id

  def ca_id (α : Type) [Alphabet α] : CArtTransducer α α := {
    Q := α
    δ := fun _ _ r => r
    embed := id
    border := default
    f := id
  }

  lemma ca_id_comp_p0 {α : Type} [Alphabet α] {w : Word α} (h: t < w.length):
    (ca_id α).comp w t 0 = w[t] := by
    unfold LCellAutomaton.comp

    have shift_next c : (ca_id α).next c = fun i => c (i + 1) := by
      funext i
      simp [CellAutomaton.next, ca_id]

    have shift_nextt k c i: ((ca_id α).nextt c k) i = c (i + k) := by
      induction k generalizing c with
      | zero =>
        simp [CellAutomaton.nextt, apply_iterated]
      | succ k ih =>
        rw [CellAutomaton.nextt, apply_iterated]
        simp only [Nat.iterate]
        rw [shift_next]
        rw [← apply_iterated]
        rw [← CellAutomaton.nextt]
        rw [ih]
        simp
        ring_nf

    rw [shift_nextt]
    unfold LCellAutomaton.embed_word
    dsimp [ca_id]
    unfold Word.get'
    unfold Word.range
    grind

  @[simp]
  lemma ca_id_scan_temporal [Alphabet α]: (ca_id α).advice.f = id := by
    funext w
    rw [id_eq]
    apply List.ext_getElem
    · simp
    · intro i h_i h_len
      unfold CArtTransducer.advice LCellAutomaton.scan_temporal_rt LCellAutomaton.scan_temporal
      conv in (ca_id α).f => change id
      simp [ca_id_comp_p0 h_len]

end id








def word_dvd_k_ext (k: ℕ) (w_len: ℕ) := (w_len - (w_len % w_len)) % w_len

def word_dvd_k (k: ℕ) (w: Word α): Word (Option α) :=
  w.map (fun a => some a) ++ List.replicate (word_dvd_k_ext k w.length) none

def L_dvd_k (k: ℕ) (L: Language α): Language (Option α) := { word_dvd_k k w | w ∈ L }

theorem L_in_RT_iff_L_dvd_k_in_RT (k: ℕ) (L: Language α):
    L ∈ ℒ (CA_rt α) ↔ (L_dvd_k k L) ∈ ℒ (CA_rt (Option α)) := by
  sorry


notation x "³"  => Fin 3 → x





def triple_at {Q} (c: ℕ → Q) (i: ℕ): Q³ := fun o => c (i + o)


def CArtTransducer.compo [Alphabet α] [Alphabet β] {C: CArtTransducer α β} (w: Word α) (t: ℕ): Config β := C.f ∘ (C.toLCellAutomaton.comp w t)

def CArtTransducer.comport [Alphabet α] [Alphabet β] {C: CArtTransducer α β} (w: Word α): Word β :=
  (List.range w.length).map (fun t => C.compo w t 0)

def CArtTransducer.compio [Alphabet α] [Alphabet β] {C: CArtTransducer α β} (c: Config α) (t: ℕ): Config β := C.f ∘ (C.toLCellAutomaton.nextt (C.embed ∘ c) t)



structure CompressToDiag where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CArtTransducer α β

attribute [instance] CompressToDiag._inst_α
attribute [instance] CompressToDiag._inst_β

namespace CompressToDiag

  variable (e: CompressToDiag)

  def C: CArtTransducer e.α (Option (e.β³)) := sorry

  theorem spec (w: Word e.α) (t: ℕ) (p: ℤ):
      e.C.compo w t p =
        if p >= 0 ∧ t = 2 * p + 3
        then some (triple_at (e.C_orig.compo w · 0) (3 * p).natAbs)
        else none
        := by
    sorry

end CompressToDiag







structure CompressToΛ where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CArtTransducer α β
  border: β

attribute [instance] CompressToΛ._inst_α
attribute [instance] CompressToΛ._inst_β

namespace CompressToΛ
  variable (e: CompressToΛ)

  def C: CArtTransducer e.α (Option (e.β³)) := sorry

  def decode_cfg (w: Word e.α): Config (e.β³) :=
    fun p =>
      if p ≥ 0
      then triple_at (e.C_orig.compo w . 0) (3 * p).natAbs
      else (fun _ => e.border)

  theorem spec (w: Word e.α) (t: ℕ) (p: ℤ):
      e.C.compo w t p =
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
  [inst: NeZero k]
  C_orig: CellAutomaton

attribute [instance] SpeedupKx.inst

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

  def C: CellAutomaton := {
    Q := Fin e.k → e.C_orig.Q
    δ := fun a b c =>
      e.to_local_config (e.C_orig.nextt (e.local_config a b c) e.k)
  }


  lemma compression_k_step (c: Config e.C_orig.Q):
      e.C.next (compress e.k c) = compress e.k (e.C_orig.nextt c e.k) :=
        sorry

  theorem spec (c: Config e.C_orig.Q):
      ∀ t, e.C.nextt (compress e.k c) t = compress e.k (e.C_orig.nextt c (e.k * t)) :=
        sorry

end SpeedupKx



structure SimFromΛ where
  {α: Type}
  {β: Type}
  {γ: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [_inst_γ: Alphabet γ]
  C_ctl: CArtTransducer α (Option β)
  C_inr: CArtTransducer β γ

attribute [instance] SimFromΛ._inst_α
attribute [instance] SimFromΛ._inst_β
attribute [instance] SimFromΛ._inst_γ

namespace SimFromΛ
  variable (e: SimFromΛ)

  structure Q1 where
    state: e.C_ctl.Q
    counter: Fin 3
  deriving Inhabited, DecidableEq, Fintype


  def C: CArtTransducer e.α (Option e.γ) := {
    Q := Option (Q1 e × e.C_inr.Q)
    δ := fun a b c =>
      match (a, b, c) with
      | (some qa, some (qb, _), some qc) =>
        if qb.counter = 2
        then sorry
        else none
      | _ => none
    border := default
    embed := sorry
    f := sorry
  }

  variable (c_ctl: Config e.α)
  variable (c_inr: Config e.β)

  def c_ctl_computes_c_inr: Prop :=
    ∀ (t: ℕ) (p: ℤ),
    e.C_ctl.compio c_ctl t p =
      if t = 3 + 2 * p.natAbs
      then some (c_inr p)
      else none


  theorem spec (h_CM: e.c_ctl_computes_c_inr c_ctl c_inr) (t: ℕ) (p: ℤ):
    e.C.compio c_ctl (3 + 3 * t) 0 = some (e.C_inr.compio c_inr t 0) := by
      sorry
end SimFromΛ


structure DecompressTriple where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CArtTransducer α (Option (β³))

attribute [instance] DecompressTriple._inst_α
attribute [instance] DecompressTriple._inst_β

namespace DecompressTriple

  variable (e: DecompressTriple)

  def C (e: DecompressTriple): CArtTransducer e.α (Option e.β) := sorry


  theorem spec (c: Config e.α) (t: ℕ) (v: (e.β³))
    (h: ∀ o: Fin 3, e.C_orig.compio c (t + o) 0 = if o == 0 then some v else none):
      ∀ o: Fin 3, (e.C.compio c (t + o) 0) = some (v o) := by
    sorry


  def h_cond (c: Config e.α) (k: ℕ): Prop :=
      ∀ (t: ℕ), ((e.C_orig.compio c (t + k) 0)).isSome == ((t - k) % 3 == 0)

  theorem spec2 (c: Config e.α) (h: e.h_cond c k) (t: ℕ):
        e.C.compio c t 0 =
          if t < k then none
          else (e.C_orig.compio c ((t - k) / 3 * 3) 0).map (. (Fin.ofNat 3 (t - k)))
      := by
    sorry

end DecompressTriple




structure SpeedupKSteps where
  {α: Type}
  {β: Type}
  [inst1: Alphabet α]
  [inst2: Alphabet β]
  C_orig: CArtTransducer α β
  k: ℕ

attribute [instance] SpeedupKSteps.inst1
attribute [instance] SpeedupKSteps.inst2

namespace SpeedupKSteps

  variable (e: SpeedupKSteps)

  def C: CArtTransducer e.α e.β := sorry

  theorem spec: e.C.compo w w.length = e.C_orig.compo w (w.length + e.k) := sorry

end SpeedupKSteps





def triple_to_fun (v: α × α × α): α³ :=
    fun
      | 0 => v.1
      | 1 => v.2.1
      | 2 => v.2.2


/-
  def C_ctl {e: Composition} : LCellAutomaton e.α := sorry
  def f : e.C_ctl.Q → Option (e.C2.Q³) := sorry


  variable (w: Word e.α)
  def c_orig: Config (e.C2.Q³) := SpeedupKx.compress 3 (e.C2.embed_word (e.C1.advice.f w))

  lemma C_ctl_spec: e.f (e.C_ctl.comp w t p) =
      if t = 3 + 2 * p.natAbs then some (e.c_orig w p)
      else none := by
    sorry
-/


def CArtTransducer.map_out [Alphabet α] [Alphabet β] [Alphabet γ] (C: CArtTransducer α β) (f: β → γ):
    CArtTransducer α γ := {
  Q := C.Q
  δ := C.δ
  embed := C.embed
  border := sorry
  f := f ∘ C.f
}

structure Composition where
  α: Type
  β: Type
  γ: Type
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  [_inst_γ: Alphabet γ]
  C2: CArtTransducer β γ
  C1: CArtTransducer α β

attribute [instance] Composition._inst_α
attribute [instance] Composition._inst_β
attribute [instance] Composition._inst_γ

def LCellAutomaton.embed_c [Alphabet α] [Alphabet β] {C: LCellAutomaton α} (c: Option α): C.Q :=
  match c with
  | none => C.border
  | some x => C.embed x


structure CellAutomatonT (α β: Type) where
  Q: Type
  [alphabetQ: Alphabet Q]
  δ: Q → Q → Q → Q
  embed: α → Q
  project: Q → β

def CellAutomatonT.embed_config {α β: Type} (C: CellAutomatonT α β) (c: Config α): Config C.Q :=
  fun p => C.embed (c p)

def CellAutomatonT.project_config {α β: Type} (C: CellAutomatonT α β) (c: Config C.Q): Config β :=
  fun p => C.project (c p)

def CellAutomatonT.comp {α β: Type} (C: CellAutomatonT α β) (c: Config α) (t: ℕ): Config β :=
  C.project_config (C.nextt (C.embed_config c) t)


--@[coe]
def Word.toConfig {α : Type} (w : Word α) : Config (Option α) := w.get'?
--instance : CoeOut (Word α) (Config (Option α)) := ⟨Word.toConfig⟩

def Word.toConfig2 {α : Type} (w : Word α) : Config (Option α) := w.get'?
instance {C: CellAutomatonT (Option α) β} : Coe (Word α) (Config C.Q) := ⟨C.embed_config ∘ Word.toConfig2⟩


abbrev CellAutomaton2 (α: Type) := CellAutomatonT (Option α) Bool

def foo (e: CellAutomaton2 α) (w: Word α) := e.nextt w
#print foo

namespace Composition
  variable (e: Composition)

  -- α -> (Option C2.Q³)
  def C1_Λ: CompressToΛ := {
    α := e.α
    β := e.C2.Q
    -- α -> C2.Q
    C_orig := e.C1.map_out (fun v => e.C2.embed v)
    border := e.C2.border
  }
/-

We want to show:
C.trace_rt = C2.trace_rt ∘ C1.trace_rt
<=>
C.trace_rt w = C2.trace_rt (C1.trace_rt w)







-/


  -- LCellAutomaton α := CellAutomaton (Option α) Bool


  -- C.trace [w] = C2.trace [C1.trace [w]]

  -- restrict_border: * * # = #, # # # = #
  -- VC1.comp_extract [w] = compress3 [C1.trace [w]]
  -- then (Sim VC1 (C2_3x)).nextt [w] (3t + 3) 0 = C2_3x.nextt (compress3 [C1.trace [w]]) t 0
  --   = (C2.nextt [C1.trace [w]]) 3t 0


  -- c_ctl := compress [w]: (Config C1.Q)
  -- c_inr := compress [C1_Λ.comport w]: (Option ³)
  -- lemma l1: C1_Λ.c_ctl_computes_c_inr c_ctl c_inr
  -- lemma l2:
  -- C2.Q³ -> C2.Q³
  def C2_3x: SpeedupKx := {
    k := 3
    C_orig := e.C2.toCellAutomaton
  }

  def C_sim: SimFromΛ := {
    α := e.α
    β := e.C2.Q³
    γ := e.γ³
    C_ctl := e.C1_Λ.C -- α -> (Option C2.Q³)
    C_inr := {
      toCellAutomaton := e.C2_3x.C
      border := default
      embed := id
      f := fun q => fun o => e.C2.f (q o)
    }
  }

  --
  def C_decomp: DecompressTriple := {
    α := e.α
    β := e.γ
    C_orig := e.C_sim.C
  }

  def C_exact: SpeedupKSteps := {
    α := e.α
    β := e.γ
    C_orig := e.C_decomp.C.map_out (fun o => o.getD default)
    k := 3
  }

  def C: CArtTransducer e.α e.γ := e.C_exact.C

  theorem spec: e.C.comport = e.C2.comport ∘ e.C1.comport := by
    sorry


end Composition

/-

* Lc(adv2) is rt+adv1
* Lc(adv2 o adv1) is rt
* adv2 o adv1 is rt-closed



* put input + advice on the diagonal (3-tupel)
* then run the simulation on the 3x speedup automaton
* we have now the results for (3t, 3t+1, 3t+2) at 3t+3 (from step 3) (or something like this)
  * we need to smear it out , so that 3t+k is available at 3t + k + 3, for k = 0,1,2
  * then we speed it up by 3 steps
  * if temporal_trace[i] is w[i], then temporal_trace[i - 1] must be w[i - 1],
  * because it cannot see the end

-/




def CArtTransducer.rt_closed [Alphabet α] [Alphabet β] [Alphabet γ] (t: CArtTransducer β γ): t.advice.rt_closed :=
  sorry




def CArtTransducer.compose [Alphabet α] [Alphabet β] [Alphabet γ] (t1: CArtTransducer β γ) (t2: CArtTransducer α β):
    CArtTransducer α γ :=
  sorry

def CArtTransducer.compose_spec [Alphabet α] [Alphabet β] [Alphabet γ]
    {t1: CArtTransducer β γ} {t2: CArtTransducer α β}:
    (CArtTransducer.compose t1 t2).advice.f =
      t1.advice.f ∘ t2.advice.f := by
        sorry
