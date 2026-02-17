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
import CellularAutomatas.proofs.k_step_speedup
import CellularAutomatas.proofs.sim_from_lambda
import CellularAutomatas.proofs.decompress_triple
import CellularAutomatas.proofs.compress_to_diag
import CellularAutomatas.proofs.diag_left3


namespace CellularAutomatas


open CellAutomaton

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

  def data_source : CompressToDiag := {
    α := e.α
    β := e.β？
    C_orig := e.C_orig
  }

  -- diag_right fires (true) at p >= 0 at correct diagonal time
  -- diag_left fires (true) at p < 0 at correct diagonal time
  -- data_source.C provides the actual triple values (but always outputs some)
  def C: CellAutomaton e.α？ ((e.β？)³)？ :=
    (e.data_source.C ⨂ (DiagLeftRight.diag_right : CellAutomaton e.α？ Bool) ⨂ (DiagLeftRight.diag_left : CellAutomaton e.α？ Bool)).map_project
      (fun (triple, (signal_right, signal_left)) =>
        if signal_right then triple              -- p >= 0 on diagonal: use computed triple
        else if signal_left then some (fun _ => none)  -- p < 0 on diagonal: placeholder
        else none)                                -- not on diagonal


  def decode_cfg (w: Word e.α): Config ((e.β？)³) :=
    fun p =>
      if p ≥ 0
      then triple_at (e.C_orig.trace w) (3 * p).natAbs
      else (fun _ => none)

  @[simp]
  lemma map_project_comp2 {α β γ: Type} (C: CellAutomaton α？ β) (f: β → γ) (w: Word α) (t: ℕ):
    (C.map_project f).comp w t p = f (C.comp w t p) := by rfl

  @[simp]
  lemma ca_zip_comp2 {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
      {C1: CellAutomaton α？ β1} {C2: CellAutomaton α？ β2} {w: Word α} {t: ℕ} {i: ℤ}:
      (C1 ⨂ C2).comp w t i = ((C1.comp w t i), (C2.comp w t i)) := by
    unfold embed_word
    simp only [ca_zip_comp]

  theorem spec (w: Word e.α) (hw: w ≠ []) (t: ℕ) (p: ℤ):
      e.C.comp w t p =
        if t = 3 + 2 * p.natAbs
        then some (e.decode_cfg w p)
        else none
        := by
    -- Step 1: Unfold C and use composition lemmas
    unfold C
    simp only [map_project_comp2, ca_zip_comp2]

    -- Step 2: Get the specs for diag signals
    rw [DiagLeftRight.diag_right_spec w hw, DiagLeftRight.diag_left_spec2 w hw]
    simp only [hw, ne_eq, not_false_eq_true, true_and]

    -- Step 3: Case split on diagonal timing
    by_cases ht : t = 3 + 2 * p.natAbs
    case pos =>
      -- On diagonal
      simp only [ht, and_true, decide_eq_true_eq]
      by_cases hp : p ≥ 0
      case pos =>
        -- p ≥ 0: diag_right fires, use data_source.C output
        simp only [hp, ↓reduceIte]
        -- Need: data_source.C.comp w t p = some (decode_cfg w p)
        unfold decode_cfg
        simp only [hp, ↓reduceIte]
        -- data_source.C.comp gives triple_at via CompressToDiag.spec
        have hw' : w.length > 0 := List.length_pos_of_ne_nil hw
        -- Convert p to ℕ since p ≥ 0
        lift p to ℕ using hp
        simp only [Int.natAbs_natCast] at ht ⊢
        have h := e.data_source.spec w hw' p
        simp only [mul_comm 2 p] at h ⊢
        convert h using 1
        ring_nf
      case neg =>
        -- p < 0: diag_left fires, diag_right doesn't
        push_neg at hp
        have hp' : p ≤ 0 := le_of_lt hp
        simp only [hp', ↓reduceIte]
        -- Output is some (fun _ => none) which matches decode_cfg for p < 0
        unfold decode_cfg
        simp only [show ¬(p ≥ 0) by linarith, ↓reduceIte]
    case neg =>
      -- Off diagonal: both diag signals are false
      simp only [ht, and_false, decide_false]
      rfl

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


structure AddBorder where
  {α: Type}
  {β: Type}
  [_inst_α: Alphabet α]
  [_inst_β: Alphabet β]
  C_orig: CellAutomaton α？ β

attribute [instance] AddBorder._inst_α
attribute [instance] AddBorder._inst_β

namespace AddBorder
  variable (e: AddBorder)

  def b := e.C_orig.embed none

  def C_mark_border: CellAutomaton e.α？ Bool := {
    Q := Bool
    δ := fun _a _b c => c
    embed := fun
      | some _a => false
      | none => true
    project := id
  }

  theorem spec_mark_border (w: Word e.α) (t: ℕ) (p: ℤ):
      e.C_mark_border.comp w t p = (p + t < 0 || p + t ≥ w.length) := by
    unfold CellAutomaton.comp CellAutomaton.project_config
    simp only [Function.comp_apply]
    have next_val : ∀ (c: Config e.C_mark_border.Q) (p: ℤ), e.C_mark_border.next c p = c (p+1) := by
      intro c p
      unfold CellAutomaton.next
      simp [C_mark_border]
    have h_nextt: ∀ t p, e.C_mark_border.nextt (embed_word w) t p = (embed_word w) (p + t) := by
      intro t
      induction t with
      | zero =>
        intro p
        simp
      | succ t ih =>
        intro p
        rw [CellAutomaton.nextt_succ]
        rw [next_val]
        rw [ih]
        apply congrArg
        grind
    rw [h_nextt]
    dsimp [embed_word, word_to_config, CellAutomaton.embed_config]
    dsimp [C_mark_border]
    split_ifs with h
    · simp_all
    · simp
      rcases lt_or_ge (p+t) 0 with h_neg | h_pos
      · left; exact h_neg
      · right; simp_all

  @[simp]
  theorem spec_mark_border2 (w: Word e.α) (t: ℕ):
      e.C_mark_border.trace w t = (t < 0 || t ≥ w.length) := by
    unfold trace
    rw [←embed_word]
    rw [spec_mark_border]
    simp

  def C := (e.C_orig ⨂ e.C_mark_border).map_project (fun (v1, v2) =>
    if v2 then none else (some v1)
  )

  theorem spec (w: Word e.α): e.C.trace w = config_to_trace (e.C_orig.trace_rt w) := by
    funext t
    unfold C
    unfold config_to_trace
    unfold trace_rt
    simp [word_to_config]
    grind

end AddBorder



structure Composition where
  {α: Type}
  {β: Type}
  {γ: Type}
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
    c := 7
  }

  def C : (CellAutomaton e.α？ e.γ) := e.C_exact.C


  theorem spec: e.C.trace_rt = e.C2.trace_rt ∘ e.C1.trace_rt := by
    rw [IsCausal.eq_iff _ _ (by simp) (by simp)]

    intro w

    by_cases hw: w = []
    case pos => simp [hw]

    let c_inr: Config e.β？³ := SpeedupKx.compress 3 (word_to_config (e.C1.trace_rt w))
    have x: e.C_sim.c_ctl_computes_c_inr ⟬w⟭ c_inr := by
      unfold SimFromΛ.c_ctl_computes_c_inr
      intro t p
      simp
      rw [CompressToΛ.spec _ _ hw]
      congr
      unfold CompressToΛ.decode_cfg
      dsimp [C1_Λ]
      rw [AddBorder.spec]
      dsimp [C1']
      dsimp [c_inr]

      have {α} (w: Word α) : (if p ≥ 0 then triple_at (config_to_trace ⟬w⟭) (3 * p).natAbs else fun x => none) =
          SpeedupKx.compress 3 ⟬w⟭ p := by

        unfold SpeedupKx.compress
        funext j
        by_cases hp: p >= 0
        case neg =>
          simp [hp]
          unfold word_to_config
          simp_all
          omega
        case pos =>
          simp [hp]
          unfold word_to_config triple_at config_to_trace
          grind

      simp [this]

    suffices (e.C.trace_rt w)[w.length - 1]'(by simp [List.length_pos_of_ne_nil hw])
      = (e.C2.trace_rt (e.C1.trace_rt w))[w.length - 1]'(by simp [List.length_pos_of_ne_nil hw]) by
      simp [List.getLast?_eq_getElem?]
      grind

    set t := w.length - 1 with t_h
    have t_len : t < w.length := by simp [t_h, List.length_pos_of_ne_nil hw]

    obtain ⟨t₁, t₂, ht⟩: ∃ t1: ℕ, ∃ t2: Fin 3, t = 3 * t1 + t2 := by
      use t / 3
      use ⟨t % 3, Nat.mod_lt _ (by decide)⟩
      simp [Nat.div_add_mod]

    calc (e.C.trace_rt w)[t]'(by simp_all)
      = (e.C.trace w) t := by simp [trace_rt]
      _ = e.C_exact.C.trace ⟬w⟭ t := by rfl
      _ = e.C_decomp.C.trace ⟬w⟭ (t + 6) := by
        rw [SpeedupKSteps.spec (h_len := by simp_all) (h_bound := by simp; omega)]

      _ = e.C_decomp.C.trace ⟬w⟭ (t + 3 + 3) := by simp
      _ = e.C_decomp.C.trace ⟬w⟭ (3 * t₁ + t₂ + 3 + 3) := by rw [ht]
      _ = e.C_decomp.C.trace ⟬w⟭ (3 * (t₁ + 1) + t₂ + 3) := by ring_nf
      _ = (e.C_sim.C.trace ⟬w⟭ (3 * (t₁ + 1) + 3)).get (by
          rw [e.C_sim.spec ⟬w⟭ c_inr x]
          simp) t₂ := by
        rw [DecompressTriple.spec2]
        exact e.C_sim.h_cond_form ⟬w⟭ c_inr x 3 rfl
        simp

      _ = (some (e.C2_3x.C.trace c_inr (t₁ + 1))).get (by trivial) t₂ := by
        have h := e.C_sim.spec ⟬w⟭ c_inr x (t₁ + 1)
        -- The issue is dependent types. Let's work with the values directly.
        -- Both `.get _ t₂` and the RHS are function applications to t₂
        -- Show they evaluate to the same thing by showing the options are equal
        -- and thus their `.get`s are the same
        have h2 : (e.C_sim.C.trace ⟬w⟭ (3 * (t₁ + 1) + 3)) =
                  some (e.C2_3x.C.trace c_inr (t₁ + 1)) := h
        -- Now the goal is: opt.get _ t₂ = (some v).get _ t₂
        -- where opt = some v by h2
        -- This is true because get extracts the value
        rw [show (e.C_sim.C.trace ⟬w⟭ (3 * (t₁ + 1) + 3)).get _ =
               (some (e.C2_3x.C.trace c_inr (t₁ + 1))).get (by trivial)
            from by simp only [h2, Option.get_some]]
      _ = e.C2_3x.C.trace c_inr (t₁ + 1) t₂ := by rfl
      _ = e.C2.trace ⟬e.C1.trace_rt w⟭ (3 * t₁ + t₂) := by
          rw [SpeedupAndTraceKx.spec1]

      _ = e.C2.trace ⟬e.C1.trace_rt w⟭ t := by rw [ht]
      _ = (e.C2.trace_rt (e.C1.trace_rt w))[t]'(by simp_all) := by simp [trace_rt]


end Composition


def CellAutomaton.compose_trace_rt {α β γ} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C2: CArtTransducer β γ) (C1: CArtTransducer α β): CArtTransducer α γ :=
  (Composition.mk C2 C1).C

infixr:90 "⊚"  => CellAutomaton.compose_trace_rt

@[simp]
theorem CellAutomaton.compose_trace_rt_spec {α β γ} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C2: CArtTransducer β γ) (C1: CArtTransducer α β):
    (C2.compose_trace_rt C1).trace_rt = C2.trace_rt ∘ C1.trace_rt := by
  rw [compose_trace_rt, Composition.spec]

@[simp]
theorem CArtTransducer.compose_trace_rt_advice_spec {α β γ} [Alphabet α] [Alphabet β] [Alphabet γ]
    (C2: CArtTransducer β γ) (C1: CArtTransducer α β):
    (C2.compose_trace_rt C1).advice.f = C2.advice.f ∘ C1.advice.f := by
  simp [CArtTransducer.advice]
