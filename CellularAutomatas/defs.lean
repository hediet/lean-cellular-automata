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

    notation "⦋" w "⦌"  => embed_config w

    instance {C: CellAutomaton α β} : Coe (Config α) (Config C.Q) := ⟨embed_config⟩


    def project_config {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): Config β :=
      fun p => C.project (c p)


    def next {α β: Type} (C: CellAutomaton α β) (c: Config C.Q): Config C.Q :=
      fun p => C.δ (c (p - 1)) (c p) (c (p + 1))

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

      def trace (c: Config α): Trace β :=
        (C.comp c · 0)

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

      /-- A set state is closed if no matter what, cells having such a state remain in that set. -/
      def delta_closed_set (Q: Set C.Q) := ∀ a (b: Q) c, C.δ a b c ∈ Q
      /-- A state is dead if no matter what, it doesn't change. -/
      def dead (q: C.Q) := C.delta_closed_set {q}

      def left_independent := ∀ (q1 q2 q3 q1'), C.δ q1 q2 q3 = C.δ q1' q2 q3
      def right_independent := ∀ (q1 q2 q3 q3'), C.δ q1 q2 q3 = C.δ q1 q2 q3'

      /-- A state is initial if it cannot be created -/
      def initial (q: C.Q) := ∀ a b c, C.δ a b c = q → b = q

    end states

  end CellAutomaton

end CellAutomaton


section DefinesLanguage

  class DefinesLanguage (CA) (α: outParam (Type)) where
    L: CA -> Language α

  variable {T: Type*} [Alphabet α]

  def ℒ [d: DefinesLanguage T α] (s: (Set T)): Set (Language α) :=
      fun L => ∃ ca: T, ca ∈ s ∧ L = DefinesLanguage.L ca

end DefinesLanguage

section LCellAutomaton

  abbrev LCellAutomaton (α: Type) := CellAutomaton α？ Bool

  def CellAutomaton.border (C: LCellAutomaton α): C.Q := C.embed none
  def CellAutomaton.inner (C: LCellAutomaton α) (a: α): C.Q := C.embed (some a)

  def word_to_config {α : Type} (w : Word α) : Config α？ :=
    fun p => if h : p ≥ 0 ∧ p < w.length then some w[p.toNat] else none

  notation "⟬" w "⟭" => word_to_config w

  instance : Coe (Word α) (Config α？) := ⟨word_to_config⟩


  def embed_word {α β: Type} {C: CellAutomaton α？ β} (w: Word α): Config C.Q :=
    word_to_config w

  notation "⦋" w "⦌" => embed_word w

  instance {C: CellAutomaton α？ β} : Coe (Word α) (Config C.Q) := ⟨embed_word⟩


  def CellAutomaton.trace_rt {α β: Type} (C: CellAutomaton α？ β) (w: Word α): Word β :=
    (List.range w.length).map (C.trace ⟬w⟭)


  @[simp]
  lemma embed_word_word_to_config_eq {α β: Type} {C: CellAutomaton α？ β} (w: Word α):
      C.embed_config (word_to_config w) = ⦋w⦌ := rfl

  @[simp]
  lemma trace_rt_len {α β: Type} (C: CellAutomaton α？ β) (w: Word α):
      (C.trace_rt w).length = w.length := by
    simp [CellAutomaton.trace_rt]

end LCellAutomaton

section tCellAutomaton

  structure tCellAutomaton (α: Type) extends LCellAutomaton α where
    t: ℕ → ℕ
    p: ℕ → ℤ

  def tCellAutomata (α: Type): Set (tCellAutomaton α) := Set.univ

  def tCellAutomaton.accepts {C: tCellAutomaton α} (w: Word α): Bool :=
    C.comp w (C.t w.length) (C.p w.length)

  def tCellAutomaton.L {α: Type} (C: tCellAutomaton α): Language α := { w | C.accepts w }

  instance [Alphabet α] : DefinesLanguage (tCellAutomaton α) α where
    L C := C.L



  instance (C: tCellAutomaton α) (w: Word α) : Decidable (w ∈ C.L) := by
    change Decidable (C.comp w (C.t w.length) (C.p w.length) = true)
    infer_instance


  instance (C: tCellAutomaton α) : DecidablePred C.L := by
    intro w
    change Decidable (w ∈ C.L)
    infer_instance


end tCellAutomaton

section CAClasses

    variable (α: Type)

    def t_rt (S: Set (tCellAutomaton α)) := { C ∈ S | ∀ n, C.t n = n - 1 }
    def t_2n (S: Set (tCellAutomaton α)) := { C ∈ S | ∀ n, C.t n = 2 * n }
    def t_lt (S: Set (tCellAutomaton α)) := { C ∈ S | ∃ c: ℕ, ∀ n, C.t n = c * n }

    def CA   := { C ∈ tCellAutomata α | C.p = fun _ => 0 }
    def CA_rt := CA α |> t_rt α
    def CA_2n := CA α |> t_2n α
    def CA_lt := CA α |> t_lt α

    def CAr  := { C ∈ tCellAutomata α | C.p = fun (n: ℕ) => (n: ℤ) }

    def OCA  := { C ∈ CA α | C.left_independent }
    def OCA_rt := OCA α |> t_rt α
    def OCA_2n := OCA α |> t_2n α
    def OCA_lt := OCA α |> t_lt α

    def OCAr  := { C ∈ CAr α | C.right_independent }
    def OCAr_rt := OCAr α |> t_rt α
    def OCAr_2n := OCAr α |> t_2n α
    def OCAr_lt := OCAr α |> t_lt α

end CAClasses

section Advice

  structure Advice (α: Type) (Γ: Type) where
    f: Word α → Word Γ
    len: ∀ w: Word α, (f w).length = w.length := by simp

  @[simp]
  lemma advice_len {α Γ} (adv: Advice α Γ) (w: Word α): (adv.f w).length = w.length := by
    simp [adv.len]

  def zip_words {α β} (w: List α) (a: List β): Word (α × β) :=
    List.zipWith (·,·) w a

  infixl:65 " ⨂ " => zip_words

  @[app_unexpander zip_words]
  def unexpand_zip_words : Lean.PrettyPrinter.Unexpander
  | `($_ $w $a) => `($w ⨂ $a)
  | _ => throw ()


  namespace Advice
    section
      variable {Γ: Type} (adv: Advice α Γ)

      def annotate (w: Word α): Word (α × Γ) := w ⨂ (adv.f w)

      def prefix_stable: Prop :=
        ∀ w: Word α, ∀ i: ℕ,
          adv.f (w.take i) = (adv.f w).take i
    end

    def compose {Γ₁: Type} {Γ₂: Type} (adv1: Advice α Γ₁) (adv2: Advice Γ₁ Γ₂): Advice α Γ₂ :=
      ⟨ fun w => adv2.f (adv1.f w), by simp [adv1.len, adv2.len] ⟩

  end Advice

  structure tCellAutomatonWithAdvice (α: Type) where
    Γ: Type
    [alphabetΓ: Alphabet Γ]
    adv: Advice α Γ
    C: tCellAutomaton (α × Γ)

  attribute [instance] tCellAutomatonWithAdvice.alphabetΓ

  def tCellAutomatonWithAdvice.L (C: tCellAutomatonWithAdvice α): Language α := { w | C.C.accepts (C.adv.annotate w) }

  instance {Γ: Type} [Alphabet Γ] : HAdd (tCellAutomaton (α × Γ)) (Advice α Γ) (tCellAutomatonWithAdvice α) where
    hAdd C adv := tCellAutomatonWithAdvice.mk Γ adv C

  instance {Γ: Type} [Alphabet Γ] : HAdd (Set (tCellAutomaton (α × Γ))) (Advice α Γ) (Set (tCellAutomatonWithAdvice α)) where
    hAdd S adv := { C + adv | C ∈ S }

  instance [Alphabet α] : DefinesLanguage (tCellAutomatonWithAdvice α) α where
    L ca := tCellAutomatonWithAdvice.L ca

  def Advice.rt_closed {Γ: Type} [Alphabet α] [Alphabet Γ] (f: Advice α Γ) :=
    ℒ (CA_rt (α × Γ) + f) = ℒ (CA_rt α)

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

  def Advice.is_two_stage_advice [Alphabet α] [Alphabet Γ] (adv: Advice α Γ): Prop :=
    ∃ ts_adv: TwoStageAdvice α Γ, ts_adv.advice = adv

end TwoStageAdvice

section AdviceHelpers

  def Advice.prefix_mem (L: Language α) [h: DecidablePred L]: Advice α Bool :=
    { f := fun w => (List.range w.length).map (fun i => decide (L (w⟦0..i+1⟧))) }


  def Advice.exp: Advice α Bool :=
    { f := fun w => (List.range w.length).map fun i => i == 2 ^ (Nat.log2 i) }



  def Advice.from_len_marker (f: ℕ → Option ℕ): Advice α Bool :=
    { f := fun w =>
        let idx := f w.length
        (List.range w.length).map fun i => some (i + 1) == idx
    }



  def middle_idx (n: ℕ) := n / 2

  def Advice.middle (α): Advice α Bool := Advice.from_len_marker (some ∘ middle_idx)

  -- runs the biggest value 2^k such that 2^(k+1) <= n, if such exists
  def exp_middle_idx (n: ℕ) :=
    (List.range n).map (2 ^ ·)
    |> List.filter (· * 2 ≤ n)
    |> List.max?

  -- Marks the biggest exponent of 2 that is less than or equal to the length of the word
  def Advice.exp_middle (α): Advice α Bool := Advice.from_len_marker exp_middle_idx

  def Advice.shift_left_advice {adv: Advice α Γ} (extension: Word α): Advice α Γ :=
    { f := fun w => (adv.f (w.append extension)).drop extension.length }

end AdviceHelpers

end CellularAutomatas
