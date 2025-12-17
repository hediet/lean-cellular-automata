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


def triple_at {Q} (c: ℕ → Q) (i: ℕ): Q × Q × Q :=
    (c i, c (i + 1), c (i + 2))

namespace compress_to_diag
  structure Params where
    α: Type
    [_inst_α: Alphabet α]
    C: LCellAutomaton α

  def Params.C' (e: Params): LCellAutomaton e.α := sorry

  def Params.decode (e: Params): e.C'.Q → Option (e.C.Q × e.C.Q × e.C.Q) := sorry

  theorem Params.spec (e: Params) (w: Word e.α) (t: ℕ) (p: ℤ):
      e.decode (e.C'.comp w t p) =
        if p >= 0 ∧ t = 2 * p + 3
        then some (triple_at (e.C.comp w . 0) (3 * p).natAbs)
        else none
        := by
    sorry

end compress_to_diag

namespace compress_to_Λ
  structure Params where
    {α: Type}
    {β: Type}
    [_inst_α: Alphabet α]
    in_C: LCellAutomaton α
    β_embed_q: in_C.Q → β
    β_embed_border: β

  def Params.C (e: Params): LCellAutomaton e.α := sorry


  def Params.decode (e: Params): e.C.Q → Option (e.β × e.β × e.β) := sorry

  def Params.decode_cfg (e: Params) (w: Word e.α): Config (e.β × e.β × e.β) :=
    fun p =>
      if p ≥ 0
      then triple_at (e.β_embed_q ∘ (e.in_C.comp w . 0)) (3 * p).natAbs
      else (e.β_embed_border, e.β_embed_border, e.β_embed_border)

  theorem Params.spec (e: Params) (w: Word e.α) (t: ℕ) (p: ℤ):
      e.decode (e.C.comp w t p) =
        if t = 3 + 2 * p.natAbs
        then some (e.decode_cfg w p)
        else none
        := by
    sorry

end compress_to_Λ

lemma intCastEq {k: ℕ} [NeZero k] (p: ℤ): (Fin.intCast p: Fin k) = (p % k) := by
  sorry


namespace speedup_kx
  variable [Alphabet α]

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



  variable (C: CellAutomaton)

  def Q' := Fin k → C.Q

  def local_config (a b c: Q' k C): Config C.Q :=
      fun p => if p <= -k then a (Fin.intCast 0) else
        if p < 0 then a (Fin.intCast (p + k))
        else if p < k then b (Fin.intCast p)
        else c (Fin.intCast (p - k))

  def to_local_config (c: Config (C.Q)): Q' k C := fun j => c j

  def C': CellAutomaton := {
    Q := Fin k → C.Q
    δ := fun a b c =>
      to_local_config k C (C.nextt (local_config k C (a) (b) (c)) k)
  }



  lemma compression_k_step (c: Config C.Q):
      (C' k C).next (compress k c) = compress k (C.nextt c k) :=
        sorry

  theorem spec (c: Config C.Q):
      ∀ t, (C' k C).nextt (compress k c) t = compress k (C.nextt c (k * t)) :=
        sorry

end speedup_kx



namespace sim_from_Λ
  structure Params where
    C_ctl: CellAutomaton
    C_inr: CellAutomaton
    ctl_Q_get_inr_Q?: C_ctl.Q → Option C_inr.Q

  variable (e: Params)


  structure Q1 where
    state: e.C_ctl.Q
    counter: Fin 3
  deriving Inhabited, DecidableEq, Fintype


  def Params.C': CellAutomaton := {
    Q := Option (Q1 e × e.C_inr.Q)
    δ := fun a b c =>
      match (a, b, c) with
      | (some qa, some (qb, _), some qc) =>
        if qb.counter = 2
        then sorry
        else none
      | _ => none
  }


  def Params.to_C'Q: e.C_ctl.Q → (C' e).Q := sorry
  def Params.to_CinrQ: (C' e).Q → Option e.C_inr.Q := sorry

  variable (c_ctl: Config e.C_ctl.Q)
  variable (c_inr: Config e.C_inr.Q)

  def c_ctl_computes_c_inr: Prop :=
    ∀ (t: ℕ) (p: ℤ),
    e.ctl_Q_get_inr_Q? (e.C_ctl.nextt c_ctl t p) =
      if t = 3 + 2 * p.natAbs
      then some (c_inr p)
      else none


  theorem Params.spec (h_CM: c_ctl_computes_c_inr e c_ctl c_inr) (t: ℕ) (p: ℤ):
    to_CinrQ e (e.C'.nextt (e.to_C'Q ∘ c_ctl) (3 + 3 * t) 0) =
      some (e.C_inr.nextt c_inr t 0) := by
      sorry
end sim_from_Λ

notation x "³"  => Fin 3 → x

namespace decompress_triple
  structure Params where
    in_C: CellAutomaton
    {β: Type}
    in_Q_get_triple?: in_C.Q → Option (β³)


  def Params.C (e: Params): CellAutomaton := sorry
  def Params.encode_in_C (e: Params): e.in_C.Q → e.C.Q := sorry
  def Params.decode_C (e: Params): e.C.Q → Option e.β := sorry


  theorem Params.spec (e: Params) (c: Config e.in_C.Q) (t: ℕ) (v: (e.β³)) (o: Fin 3)
    (h: e.in_Q_get_triple? (e.in_C.nextt c (t + o) 0) = if o == 0 then some v else none):
      e.decode_C (e.C.nextt (e.encode_in_C ∘ c) (t + o) 0) = some (v o) := by
    sorry


  def Params.h_cond (e: Params) (c: Config e.in_C.Q) (k: ℕ): Prop :=
      ∀ (t: ℕ), (e.in_Q_get_triple? (e.in_C.nextt c (t + k) 0)).isSome == ((t - k) % 3 == 0)

  theorem Params.spec2 (e: Params) (c: Config e.in_C.Q) (t: ℕ):
        e.decode_C (e.C.nextt (e.encode_in_C ∘ c) t 0) =
          if t < k then none
          else ((e.in_Q_get_triple? (e.in_C.nextt c ((t - k) / 3 * 3) 0)).map (. (Fin.ofNat 3 (t - k))))
      := by
    sorry

end decompress_triple



namespace composition

  structure Params where
    α: Type
    β: Type
    γ: Type
    [_inst_α: Alphabet α]
    [_inst_β: Alphabet β]
    [_inst_γ: Alphabet γ]
    C2: CArtTransducer β γ
    C1: CArtTransducer α β

  attribute [instance] Params._inst_α
  attribute [instance] Params._inst_β
  attribute [instance] Params._inst_γ

  variable {e: Params}

  def Params.C_ctl {e: Params} : LCellAutomaton e.α := sorry
  def Params.f : e.C_ctl.Q → Option (e.C2.Q³) := sorry


  variable (w: Word e.α)
  def Params.c_orig: Config (e.C2.Q³) := speedup_kx.compress 3 (e.C2.embed_word (e.C1.advice.f w))

  lemma C_ctl_spec: e.f (e.C_ctl.comp w t p) =
      if t = 3 + 2 * p.natAbs then some (e.c_orig w p)
      else none := by
    sorry



  def triple_to_fun (v: α × α × α): Fin 3 → α :=
    fun
      | 0 => v.1
      | 1 => v.2.1
      | 2 => v.2.2

  def C_Λ: compress_to_Λ.Params := {
    in_C := e.C1.toLCellAutomaton
    β := e.C2.Q
    β_embed_q := e.C2.embed ∘ e.C1.f
    β_embed_border := e.C2.border
  }

  def Params.C2_3x := speedup_kx.C' 3 (e.C2.toCellAutomaton)

  def C_sim: sim_from_Λ.Params := {
    C_ctl := C_Λ.C.toCellAutomaton
    C_inr := e.C2_3x
    ctl_Q_get_inr_Q? q := (C_Λ.decode q).map triple_to_fun
  }

  def C_decomp: decompress_triple.Params := {
    in_C := C_sim.C'
    β := e.C2.Q
    in_Q_get_triple? := C_sim.to_CinrQ
  }
  -- Want to show: C_sim.temp_scan+3 w = C2.temp_scan_rt (C1.temp_scan_rt w)



  -- if c.temp_scan_rt[w.len + v.len - 1] = f(wv)
  -- then c.temp_scan_rt[w.len - 1] = f(w)

  -- c_ctl_computes_c_inr
  --lemma C_sim_spec:

end composition

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
