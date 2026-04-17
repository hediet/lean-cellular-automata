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
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Computability.Language

namespace CellularAutomatas

notation:max t "？" => Option t
infix:50 " ⨉ " => Prod

section Alphabet

  class Alphabet (α: Type) where
      [dec: DecidableEq α]
      [fin: Fintype α]
      [inh: Inhabited α]

  attribute [instance] Alphabet.dec Alphabet.fin Alphabet.inh

  instance (α: Type) [DecidableEq α] [Fintype α] [Inhabited α]: Alphabet α := {}
  instance AlphabetUnit : Alphabet Unit := {}
  instance AlphabetBool : Alphabet Bool := {}
  instance ProductAlphabet {α β: Type} [Alphabet α] [Alphabet β] : Alphabet (α × β) := {}
  instance FunctionAlphabet {α β: Type} [Alphabet α] [Alphabet β] : Alphabet (α → β) := {}

end Alphabet

section Word

  abbrev Word (α: Type*) := List α

  notation:max w "⟦" a ".." b "⟧" => List.extract w a b
  notation:max w "⟦" a "..*⟧" => List.drop a w
  notation:max w "⟦*.." a "⟧" => List.take a w

  namespace Word
    variable {α: Type} (w: Word α)

    def range: Set ℤ := { i: ℤ | i ≥ 0 ∧ i < w.length }

    instance (i: ℤ): Decidable (i ∈ w.range) := by
      unfold range
      infer_instance

    def get' (i: ℤ) (h: i ∈ w.range) := w.get ⟨
      i.toNat,
      by simp only [range, ge_iff_le, Set.mem_setOf_eq] at h; omega
    ⟩

    def get'? (i: ℤ): Option α :=
      if h: i ∈ w.range
      then some (w.get' i h)
      else none
  end Word

end Word

section CellAutomaton

  structure CellAutomaton (α β: Type) where
    Q: Type
    [alphabetQ: Alphabet Q]
    δ: Q → Q → Q → Q
    embed: α → Q
    project: Q → β

  attribute [instance] CellAutomaton.alphabetQ

  def Config (α: Type) := ℤ → α
  def Trace (α: Type) := ℕ → α

  namespace CellAutomaton

    def embed_config {α β: Type} {C: CellAutomaton α β} (c: Config α) : Config C.Q :=
      fun p => C.embed (c p)

    lemma embed_config_apply {α β: Type} {C: CellAutomaton α β} (c: Config α) (p: ℤ) :
        @embed_config α β C c p = C.embed (c p) := rfl

    notation "⦋" w "⦌"  => embed_config w

    instance {C: CellAutomaton α β} : Coe (Config α) (Config C.Q) := ⟨embed_config⟩


    def project_config {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): Config β :=
      fun p => C.project (c p)

    lemma project_config_apply {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (p: ℤ) :
        C.project_config c p = C.project (c p) := rfl

    /-- Function-level unfolding: `project_config c = fun p => project (c p)`. Use with `simp` or `rw`. -/
    lemma project_config_unfold {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) :
        C.project_config c = fun p => C.project (c p) := rfl

    def next {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): Config C.Q :=
      fun p => C.δ (c (p - 1)) (c p) (c (p + 1))

    lemma next_apply {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (p: ℤ) :
        C.next c p = C.δ (c (p - 1)) (c p) (c (p + 1)) := rfl

    def nextt {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): Trace (Config C.Q) :=
      fun t => Nat.iterate (C.next) t c


    @[simp]
    lemma nextt_zero {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): C.nextt c 0 = c := rfl

    @[simp]
    lemma nextt_succ {α β: Type} (C: CellAutomaton α β) (c: Config C.Q) (t: ℕ): C.nextt c (t + 1) = C.next (C.nextt c t) := by
      simp [nextt, Function.iterate_succ_apply']


    section
      variable {α β: Type} (C: CellAutomaton α β)

      def comp (c: Config C.Q): Trace (Config β) :=
        C.project_config ∘ C.nextt c

      /-- Function-level unfolding: `comp c t = project_config (nextt c t)`. Use with `simp` or `rw`. -/
      lemma comp_unfold (c: Config C.Q) (t: ℕ) :
          C.comp c t = C.project_config (C.nextt c t) := rfl

      lemma comp_apply (c: Config C.Q) (t: ℕ) (p: ℤ) :
          C.comp c t p = C.project (C.nextt c t p) := rfl

      def trace (c: Config α): Trace β :=
        (C.comp c · 0)

      lemma trace_eq_comp (c: Config α) (t: ℕ) :
          C.trace c t = C.comp (⦋c⦌) t 0 := rfl

    end

    def map_project {α β γ: Type} (C: CellAutomaton α β) (f: β → γ): CellAutomaton α γ :=
      {
        Q := C.Q
        δ := C.δ
        embed := C.embed
        project := f ∘ C.project
      }

    @[simp]
    lemma map_project_nextt {α β γ: Type} (C: CellAutomaton α β) (f: β → γ) (c: Config C.Q) (t: ℕ):
      (C.map_project f).nextt c t = C.nextt c t := by rfl

    def map_embed {α β γ: Type} (C: CellAutomaton β γ) (f: α → β): CellAutomaton α γ :=
      {
        Q := C.Q
        δ := C.δ
        embed := C.embed ∘ f
        project := C.project
      }

    @[simp]
    lemma map_embed_nextt {α β γ: Type} (C: CellAutomaton β γ) (f: α → β) (c: Config C.Q) (t: ℕ):
      (C.map_embed f).nextt c t = C.nextt c t := by rfl

    section states

      variable (C: CellAutomaton α β)

      /-- A set is quiescent if every element stays the same when it is just surrounded by other elements from the set. -/
      def quiescent_set (Q: Set C.Q) := ∀ (a b c: Q), C.δ a b c = b

      /-- A state is quiescent if it stays the same when it is just surrounded by itself. -/
      def quiescent (q: C.Q) := C.quiescent_set { q }

      lemma quiescent_iff {q: C.Q} : C.quiescent q ↔ C.δ q q q = q := by
        unfold quiescent quiescent_set
        constructor
        · intro h; exact h ⟨q, rfl⟩ ⟨q, rfl⟩ ⟨q, rfl⟩
        · intro h ⟨_, ha⟩ ⟨_, hb⟩ ⟨_, hc⟩
          simp only [Set.mem_singleton_iff] at ha hb hc
          subst ha; subst hb; subst hc; exact h

      /-- A state is dead if no matter what, it doesn't change. -/
      def dead (q: C.Q) := ∀ (a b c: C.Q), b = q → C.δ a b c = q

      def left_independent := ∀ (q1 q2 q3 q1'), C.δ q1 q2 q3 = C.δ q1' q2 q3
      def right_independent := ∀ (q1 q2 q3 q3'), C.δ q1 q2 q3 = C.δ q1 q2 q3'

      /-- A state is initial if no other state can transition to it -/
      def initial (q: C.Q) := ∀ a b c, C.δ a b c = q → b = q

      def right_initial (q: C.Q) := ∀ a b c, (C.δ a b c = q) → (b = q ∨ c = q)

      def left_spreading (q: C.Q) := ∀ a b c, c = q → (C.δ a b c = q)
      def inj_embed (q: α) := ∀ (q': α), C.embed q = C.embed q' → q = q'
      def left_dead (q: C.Q) := ∀ a b c, a = q ∧ b = q → C.δ a b c = q


    end states

    -- API lemmas above (comp_unfold, comp_apply, project_config_unfold, project_config_apply,\n    -- next_apply, trace_eq_comp, embed_config_apply, quiescent_iff, etc.) provide the preferred\n    -- interface. Prefer `simp only [comp_unfold]` over `unfold CellAutomaton.comp`.

  end CellAutomaton

end CellAutomaton


section DefinesLanguage

  class DefinesLanguage (CA) (α: outParam (Type)) where
    L: CA -> Language α

  variable {T: Type*} [Alphabet α]

  /-- The set of languages recognized by automata of type T. -/
  def ℒ (T : Type*) [Alphabet α] [DefinesLanguage T α] : Set (Language α) :=
      fun L => ∃ ca : T, L = DefinesLanguage.L ca

  /-- The set of languages recognized by automata in a set S. -/
  def ℒs [d: DefinesLanguage T α] (s: (Set T)): Set (Language α) :=
      fun L => ∃ ca: T, ca ∈ s ∧ L = DefinesLanguage.L ca

end DefinesLanguage

section LCellAutomaton

  abbrev LCellAutomaton (α: Type) := CellAutomaton α？ Bool

  def CellAutomaton.border (C: CellAutomaton α？ β): C.Q := C.embed none
  def CellAutomaton.inner (C: CellAutomaton α？ β) (a: α): C.Q := C.embed (some a)

  def word_to_config {α : Type} (w : Word α) : Config α？ :=
    fun p => if h : p ≥ 0 ∧ p < w.length then some w[p.toNat] else none

  lemma word_to_config_apply {α : Type} (w : Word α) (p: ℤ) :
      word_to_config w p = if h : p ≥ 0 ∧ p < w.length then some w[p.toNat] else none := rfl

  notation "⟬" w "⟭" => word_to_config w

  instance : Coe (Word α) (Config α？) := ⟨word_to_config⟩

  @[app_unexpander CellAutomaton.embed_config]
  def unexpand_embed_word : Lean.PrettyPrinter.Unexpander
    | `($_ ⟬$w⟭) => `(⦋$w⦌)
    | _ => throw ()

  instance {C: CellAutomaton α？ β} : Coe (Word α) (Config C.Q) := ⟨fun w => CellAutomaton.embed_config (word_to_config w)⟩


  def CellAutomaton.trace_rt {α β: Type} (C: CellAutomaton α？ β) (w: Word α): Word β :=
    (List.range w.length).map (C.trace ⟬w⟭)

  @[simp]
  lemma trace_rt_len {α β: Type} (C: CellAutomaton α？ β) (w: Word α):
      (C.trace_rt w).length = w.length := by
    simp [CellAutomaton.trace_rt]

end LCellAutomaton

section BorderedConfig

/--
Bordered configuration `[#₁, v | w, #₂]`:
- Position `i ∈ [0, |w|)`: holds `wᵢ`
- Position `i ∈ [-|v|, 0)`: holds `v_{-i-1}` (so position -1 has v₀, position -2 has v₁, etc.)
- Position `i ≥ |w|`: holds `#₂`
- Position `i < -|v|`: holds `#₁`

Requires `|v| = |w|` for the mirror construction.
-/
def BorderedConfig {α : Type} (borderLeft : α) (v w : Word α) (borderRight : α) : Config α :=
  fun p =>
    if h : 0 ≤ p ∧ p < w.length then
      w[p.toNat]
    else if h2 : -v.length ≤ p ∧ p < 0 then
      v[(-p - 1).toNat]  -- position -1 → v[0], position -2 → v[1], etc.
    else if p ≥ w.length then
      borderRight
    else
      borderLeft

lemma BorderedConfig_apply {α : Type} (borderLeft : α) (v w : Word α) (borderRight : α) (p: ℤ) :
    BorderedConfig borderLeft v w borderRight p =
    if h : 0 ≤ p ∧ p < w.length then w[p.toNat]
    else if h2 : -(v.length : ℤ) ≤ p ∧ p < 0 then v[(-p - 1).toNat]
    else if p ≥ w.length then borderRight
    else borderLeft := rfl

@[simp] lemma BorderedConfig_word {α : Type} {borderLeft borderRight : α} {v w : Word α} {p: ℤ}
    (h : 0 ≤ p ∧ p < w.length) :
    BorderedConfig borderLeft v w borderRight p = w[p.toNat] := by
  unfold BorderedConfig; simp [h]

@[simp] lemma BorderedConfig_mirror {α : Type} {borderLeft borderRight : α} {v w : Word α} {p: ℤ}
    (hw : ¬(0 ≤ p ∧ p < w.length)) (hv : -(v.length : ℤ) ≤ p ∧ p < 0) :
    BorderedConfig borderLeft v w borderRight p = v[(-p - 1).toNat] := by
  unfold BorderedConfig; simp [hw, hv]

@[simp] lemma BorderedConfig_right {α : Type} {borderLeft borderRight : α} {v w : Word α} {p: ℤ}
    (hw : ¬(0 ≤ p ∧ p < w.length)) (hv : ¬(-(v.length : ℤ) ≤ p ∧ p < 0)) (hr : p ≥ w.length) :
    BorderedConfig borderLeft v w borderRight p = borderRight := by
  unfold BorderedConfig; simp [hw, hv, hr]

@[simp] lemma BorderedConfig_left {α : Type} {borderLeft borderRight : α} {v w : Word α} {p: ℤ}
    (hw : ¬(0 ≤ p ∧ p < w.length)) (hv : ¬(-(v.length : ℤ) ≤ p ∧ p < 0)) (hr : ¬(p ≥ (w.length : ℤ))) :
    BorderedConfig borderLeft v w borderRight p = borderLeft := by
  unfold BorderedConfig; simp [hw, hv, hr]

/-- Notation for bordered configurations: `[#₁ | v ‖ w | #₂]` -/
-- Using ‖ to separate v and w since | is reserved
notation:max "[" b₁ " | " v " ‖ " w " | " b₂ "]" => BorderedConfig b₁ v w b₂

/-- Simplified notation when borders are the same -/
def BorderedConfigSame {α : Type} (border : α) (v w : Word α) : Config α :=
  BorderedConfig border v w border

@[simp] lemma BorderedConfigSame_eq {α : Type} (border : α) (v w : Word α) (p: ℤ) :
    BorderedConfigSame border v w p = BorderedConfig border v w border p := rfl

notation:max "[" b " | " v " ‖ " w "]" => BorderedConfigSame b v w

end BorderedConfig

section AcceptanceSchema

  /-- How to read the result of a CA computation:
      `t` maps input length to number of steps, `p` maps input length to cell position. -/
  structure AcceptanceSchema where
    t : ℕ → ℕ
    p : ℕ → ℤ

  namespace AcceptanceSchema
    /-- Real-time, center-reading: t(n) = n - 1, p = 0 -/
    def rt_center    : AcceptanceSchema := ⟨(· - 1), fun _ => 0⟩
    /-- Real-time, right-reading: t(n) = n - 1, p = n -/
    def rt_right     : AcceptanceSchema := ⟨(· - 1), fun n => ((n : ℤ) - 1)⟩
    /-- 2(n-1) time, center-reading -/
    def time_2n_center : AcceptanceSchema := ⟨fun n => 2 * (n - 1), fun _ => 0⟩
    /-- 2(n-1) time, left-reading at -(n-1) -/
    def time_2n_left : AcceptanceSchema := ⟨fun n => 2 * (n - 1), fun n => -((n : ℤ) - 1)⟩
    /-- Linear time c*(n-1), center-reading -/
    def lt_center (c : ℕ) : AcceptanceSchema := ⟨fun n => c * (n - 1), fun _ => 0⟩
  end AcceptanceSchema

end AcceptanceSchema

section tCellAutomaton

  structure tCellAutomaton (schema : AcceptanceSchema) (α : Type) extends LCellAutomaton α

  def tCellAutomaton.accepts {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word α) : Bool :=
    C.comp w (schema.t w.length) (schema.p w.length)

  def tCellAutomaton.L {schema : AcceptanceSchema} {α : Type} (C : tCellAutomaton schema α) : Language α :=
    { w | C.accepts w }

  instance [Alphabet α] (schema : AcceptanceSchema) : DefinesLanguage (tCellAutomaton schema α) α where
    L C := C.L

  instance {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word α) : Decidable (w ∈ C.L) := by
    change Decidable (C.comp w (schema.t w.length) (schema.p w.length) = true)
    infer_instance

  instance {schema : AcceptanceSchema} (C : tCellAutomaton schema α) : DecidablePred C.L := by
    intro w
    change Decidable (w ∈ C.L)
    infer_instance

end tCellAutomaton

section CAClasses

    variable (α : Type)

    /-- CA reading at cell 0, real-time: t(n) = n - 1 -/
    abbrev CA_rt := tCellAutomaton .rt_center
    /-- CA reading at cell 0, time 2(n-1) -/
    abbrev CA_2n := tCellAutomaton .time_2n_center
    /-- CA reading at cell n (right border), real-time -/
    abbrev CAr_rt := tCellAutomaton .rt_right
    /-- CA reading at cell -(n-1), time 2(n-1) -/
    abbrev CA_2n_neg_n := tCellAutomaton .time_2n_left
    /-- Linear-time center-reading: ∃ c, t(n) = c*(n-1) -/
    def CA_lt := Σ c : ℕ, tCellAutomaton (.lt_center c) α

    instance [Alphabet α] : DefinesLanguage (CA_lt α) α where
      L C := C.2.L

    /-- One-way CA (left-independent), real-time, center-reading -/
    def OCA_rt  := { C : CA_rt α // C.left_independent }
    /-- One-way CA (left-independent), time 2(n-1), center-reading -/
    def OCA_2n  := { C : CA_2n α // C.left_independent }
    /-- One-way CA (left-independent), linear-time -/
    def OCA_lt  := Σ c : ℕ, { C : tCellAutomaton (.lt_center c) α // C.left_independent }

    instance [Alphabet α] : DefinesLanguage (OCA_rt α) α where
      L C := C.1.L
    instance [Alphabet α] : DefinesLanguage (OCA_2n α) α where
      L C := C.1.L
    instance [Alphabet α] : DefinesLanguage (OCA_lt α) α where
      L C := C.2.1.L

    /-- Right-reading one-way CA (right-independent), real-time -/
    def OCAr_rt := { C : CAr_rt α // C.right_independent }
    /-- Right-reading one-way CA (right-independent), time 2(n-1) -/
    def OCAr_2n := { C : CA_2n α // C.right_independent }
    /-- Right-reading one-way CA (right-independent), linear-time -/
    def OCAr_lt := Σ c : ℕ, { C : tCellAutomaton (.lt_center c) α // C.right_independent }

    instance [Alphabet α] : DefinesLanguage (OCAr_rt α) α where
      L C := C.1.L
    instance [Alphabet α] : DefinesLanguage (OCAr_2n α) α where
      L C := C.1.L
    instance [Alphabet α] : DefinesLanguage (OCAr_lt α) α where
      L C := C.2.1.L

    /-- OCA at time 2*(n-1), reading at position -(n-1). -/
    def OCA_2n_neg2n := { C : CA_2n_neg_n α // C.left_independent }

    instance [Alphabet α] : DefinesLanguage (OCA_2n_neg2n α) α where
      L C := C.1.L

end CAClasses

section Causal
  variable {α β: Type} (f: Word α → Word β)

  def IsCausal: Prop := ∀ w, (f w).length = w.length ∧ ∀ i, f (w.take i) = (f w).take i

  lemma IsCausal.len (h: IsCausal f) (w: Word α): (f w).length = w.length := (h w).1

  lemma IsCausal.prefix (h: IsCausal f) (w: Word α) (i: ℕ): f (w.take i) = (f w).take i := (h w).2 i

end Causal

section Advice

  structure Advice (α: Type) (Γ: Type) where
    f: Word α → Word Γ
    len: ∀ w: Word α, (f w).length = w.length := by simp

  instance : CoeFun (Advice α Γ) (fun _ => Word α → Word Γ) where
    coe adv := adv.f

  @[simp]
  lemma advice_len {α Γ} (adv: Advice α Γ) (w: Word α): (adv w).length = w.length := by
    simp [adv.len]

  infixl:65 " ⨂ " => List.zip

  @[app_unexpander List.zip]
  def unexpand_zip_words : Lean.PrettyPrinter.Unexpander
  | `($_ $w $a) => `($w ⨂ $a)
  | _ => throw ()


  namespace Advice
    section
      variable {Γ: Type} (adv: Advice α Γ)

      def annotate (w: Word α): Word (α × Γ) := w ⨂ (adv w)

      def causal: Prop := IsCausal adv.f
    end

    def compose {Γ₁: Type} {Γ₂: Type} (adv1: Advice α Γ₁) (adv2: Advice Γ₁ Γ₂): Advice α Γ₂ :=
      ⟨ adv2 ∘ adv1, by simp [adv1.len, adv2.len] ⟩

    def lift {β} (adv: Advice α Γ) [Alphabet β] (f: β → α): Advice β Γ :=
      ⟨ fun w => adv (w.map f), by simp ⟩

  end Advice

  structure tCellAutomatonWithAdvice (schema : AcceptanceSchema) (α : Type) where
    Γ: Type
    [alphabetΓ: Alphabet Γ]
    adv: Advice α Γ
    C: tCellAutomaton schema (α × Γ)

  attribute [instance] tCellAutomatonWithAdvice.alphabetΓ

  def tCellAutomatonWithAdvice.L {schema : AcceptanceSchema} (C: tCellAutomatonWithAdvice schema α): Language α :=
    { w | C.C.accepts (C.adv.annotate w) }

  instance {schema : AcceptanceSchema} {Γ: Type} [Alphabet Γ] :
      HAdd (tCellAutomaton schema (α × Γ)) (Advice α Γ) (tCellAutomatonWithAdvice schema α) where
    hAdd C adv := tCellAutomatonWithAdvice.mk Γ adv C

  instance {schema : AcceptanceSchema} [Alphabet α] : DefinesLanguage (tCellAutomatonWithAdvice schema α) α where
    L ca := tCellAutomatonWithAdvice.L ca

  /-- CA class with a fixed advice: the set of CAs of a given schema, reading advice-annotated input.
      `Advised (CA_rt) adv` is the type of CA_rt automata using advice `adv`. -/
  structure Advised (schema : AcceptanceSchema) {Γ : Type} [Alphabet α] [Alphabet Γ] (adv : Advice α Γ) where
    C : tCellAutomaton schema (α × Γ)

  instance {schema : AcceptanceSchema} {Γ : Type} [Alphabet α] [Alphabet Γ] (adv : Advice α Γ) :
      DefinesLanguage (Advised schema adv) α where
    L ca := { w | ca.C.accepts (adv.annotate w) }

  /-- Type-level sugar: `CA_rt β + adv` means `Advised .rt_center adv`, etc.
      Lets us write `ℒ (CA_rt (α × Γ) + adv)` instead of `ℒ (Advised .rt_center adv)`. -/
  macro_rules
    | `(CA_rt $_ + $adv)   => `(Advised .rt_center $adv)
    | `(CA_2n $_ + $adv)   => `(Advised .time_2n_center $adv)
    | `(CAr_rt $_ + $adv)  => `(Advised .rt_right $adv)
    | `(CA_2n_neg_n $_ + $adv) => `(Advised .time_2n_left $adv)

  /-- An advice `f` is weak-RT-closed if for every CA_rt over the extended alphabet,
      there exists a CA_rt over the base alphabet recognizing the same language. -/
  structure Advice.WeakRtClosed {Γ: Type} [Alphabet α] [Alphabet Γ] (f: Advice α Γ) where
    /-- Maps each CA_rt over the extended alphabet to a CA_rt over the base alphabet. -/
    map : CA_rt (α × Γ) → CA_rt α
    /-- The mapped CA recognizes the same language as the original CA with the advice. -/
    spec : ∀ C, (map C).L = { w | C.accepts (f.annotate w) }

  abbrev Advice.weak_rt_closed {Γ: Type} [Alphabet α] [Alphabet Γ] (f: Advice α Γ) :=
    f.WeakRtClosed

  def Advice.rt_closed {Γ: Type} [Alphabet α] [Alphabet Γ] (f: Advice α Γ) :=
    ∀ β [Alphabet β] (π: β → α), (f.lift π).weak_rt_closed

  -- TODO: Redesign weak_lt_closed / lt_closed for the new AcceptanceSchema-based CA_lt
  -- The old definitions used set-based ℒ on CA_lt + advice, which needs rethinking
  -- with the sigma-type-based CA_lt.

  -- def Advice.weak_lt_closed {Γ: Type} [Alphabet α] [Alphabet Γ] (f: Advice α Γ) :=
  --   ℒ (CA_lt (α × Γ) + f) = ℒ (CA_lt α)
  -- def Advice.lt_closed {Γ: Type} [Alphabet α] [Alphabet Γ] (f: Advice α Γ) :=
  --   ∀ β [Alphabet β] (π: β → α), (f.lift π).weak_lt_closed

end Advice

section FiniteStateTransducer

  structure FiniteStateTransducer (α: Type) (β: Type) where
    Q: Type
    [alphabetQ: Alphabet Q]
    δ: Q → α → Q
    q0: Q
    f: Q → β

  namespace FiniteStateTransducer
    attribute [instance] FiniteStateTransducer.alphabetQ

    section
      variable (M: FiniteStateTransducer α β)

      def δ?: M.Q → Option α → M.Q
        | q, none => q
        | q, some a => M.δ q a

      def scanr_step a
      | (q, w) => (M.δ q a, M.f (M.δ q a) :: w)

      def scanr_q (q: M.Q) (w: Word α): Word β :=
        (w.foldr (M.scanr_step) (q, [])).snd

      def scanr w := M.scanr_q M.q0 w

      def scanr_reduce_q (q: M.Q): Word α → M.Q
      | []   => q
      | c::cs => M.δ (scanr_reduce_q q cs) c

      def scanr_reduce := M.scanr_reduce_q M.q0

      def map_input (f: γ → α): FiniteStateTransducer γ β := {
        Q := M.Q
        δ := fun q a => M.δ q (f a)
        q0 := M.q0
        f := M.f
      }

      @[simp, grind =]
      lemma scanr_q_len (q: M.Q) (w: List α):
        (M.scanr_q q w).length = w.length := by
        unfold scanr_q
        induction w with
        | nil => simp []
        | cons a ws ih => simp [scanr_step, ih]


      @[simp, grind =]
      lemma scanr_len (w: List α): (M.scanr w).length = w.length := by
        simp [scanr, scanr_q_len]
    end

  end FiniteStateTransducer

  def FiniteStateTransducer.advice [Alphabet α] [Alphabet β] (M: FiniteStateTransducer α β): Advice α β :=
    ⟨
      fun w => M.scanr w,
      by grind [FiniteStateTransducer.scanr_len]
    ⟩

end FiniteStateTransducer

section CArtTransducer

  abbrev CArtTransducer (α β: Type) := CellAutomaton α？ β

  def CArtTransducer.advice [Alphabet α] [Alphabet β] (C: CArtTransducer α β): Advice α β :=
    ⟨
      C.trace_rt,
      by simp [CellAutomaton.trace_rt]
    ⟩

end CArtTransducer

section TwoStageAdvice

  structure TwoStageAdvice (α: Type) (Γ: Type) [Alphabet α] [Alphabet Γ]  where
    β: Type
    [alphabetβ: Alphabet β]
    C: CArtTransducer α β
    M: FiniteStateTransducer β Γ

  attribute [instance] TwoStageAdvice.alphabetβ

  namespace TwoStageAdvice
    variable {α: Type} {Γ: Type} [Alphabet α] [Alphabet Γ] (adv: TwoStageAdvice α Γ)

    def advice: Advice α Γ := { f := adv.M.scanr ∘ adv.C.trace_rt }

  end TwoStageAdvice

  /-- An advice is two-stage if it can be computed by an RT transducer followed by an FST. -/
  structure Advice.IsTwoStageAdvice [Alphabet α] [Alphabet Γ] (adv: Advice α Γ) where
    witness : TwoStageAdvice α Γ
    spec : witness.advice = adv

  abbrev Advice.is_two_stage_advice [Alphabet α] [Alphabet Γ] (adv: Advice α Γ) :=
    adv.IsTwoStageAdvice

  /-- An advice is a CArt advice if it can be computed by a single RT transducer. -/
  structure Advice.IsCartAdvice [Alphabet α] [Alphabet Γ] (adv: Advice α Γ) where
    witness : CArtTransducer α Γ
    spec : witness.advice = adv

  abbrev Advice.is_cart_advice [Alphabet α] [Alphabet Γ] (adv: Advice α Γ) :=
    adv.IsCartAdvice

end TwoStageAdvice

section AdviceHelpers

  def Advice.prefix_mem (L: Language α) [h: DecidablePred L]: Advice α Bool :=
    { f := fun w => (List.range w.length).map (fun i => decide (L (w⟦0..i+1⟧))) }


  def Advice.exp: Advice α Bool :=
    { f := fun w => (List.range w.length).map fun i => i == 2 ^ (Nat.log2 i) }


  def Advice.from_marker (f: Word α → Option ℕ): Advice α Bool :=
    { f := fun w =>
        let idx := f w
        (List.range w.length).map fun i => some (i + 1) == idx
    }

  def Advice.from_len_marker (f: ℕ → Option ℕ): Advice α Bool :=
    Advice.from_marker (f ∘ List.length)

  def middle_idx (n: ℕ) := n / 2

  def Advice.middle (α): Advice α Bool := Advice.from_len_marker (some ∘ middle_idx)

  -- runs the biggest value 2^k such that 2^(k+1) <= n, if such exists
  def middle_exp_idx (n: ℕ) :=
    (List.range n).map (2 ^ ·)
    |> List.filter (· * 2 ≤ n)
    |> List.max?

  -- Marks the biggest exponent of 2 that is less than or equal to the length of the word
  def Advice.middle_exp (α): Advice α Bool := Advice.from_len_marker middle_exp_idx

  def Advice.shift_left_advice {adv: Advice α Γ} (extension: Word α): Advice α Γ :=
    { f := fun w => (adv (w.append extension)).drop extension.length }

end AdviceHelpers

section LanguageReversal

  variable {α : Type}

  /-- The reverse of a language: L^R = { w^R | w ∈ L }. -/
  def Language.rev (L : Language α) : Language α := { w | w.reverse ∈ L }

  /-- The reverse of a language class (set of languages). -/
  def LanguageClass.rev (S : Set (Language α)) : Set (Language α) := Language.rev '' S

  /-- Language reversal is an involution. -/
  @[simp]
  lemma Language.rev_rev (L : Language α) :
      Language.rev (Language.rev L) = L := by
    ext w
    show w.reverse.reverse ∈ L ↔ w ∈ L
    simp

end LanguageReversal

def ℒ_rev (T : Type*) {α : Type} [Alphabet α] [DefinesLanguage T α] : Set (Language α) :=
  LanguageClass.rev (ℒ T)

end CellularAutomatas
