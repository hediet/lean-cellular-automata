import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod

namespace CellularAutomatas

section Utilities -- MARK: Utilities

  noncomputable def min_nat (set: Set ℕ) :=
    let _dec := Classical.dec;
    if h: ∃ n, n ∈ set
    then some (Nat.find h)
    else none

  def apply_iterated (f: α → α) (a: α) (k: ℕ) := Nat.iterate f k a

end Utilities



section Word -- MARK: Word

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

  infix:50 " ⨉ " => Prod


  abbrev Word (α: Type u) := List α

  namespace Word
    notation:max w "⟦" a ".." b "⟧" => List.extract w a b
    notation:max w "⟦" a "..*⟧" => List.drop a w

    variable {α: Type u} (w: Word α)

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



section LanguageDefinitions -- MARK: LanguageDefinitions

  class DefinesLanguage (CA) (α: outParam (Type)) where
    L: CA -> Language α


  variable {CA: Type*} [Alphabet α]

  def ℒ [d: DefinesLanguage CA α] (s: (Set CA)): Set (Language α) :=
      fun L => ∃ ca: CA, ca ∈ s ∧ L = DefinesLanguage.L ca


end LanguageDefinitions



section CellAutomaton -- MARK: CellAutomaton

  structure CellAutomaton where
    Q: Type
    [alphabetQ: Alphabet Q]
    δ: Q → Q → Q → Q

  attribute [instance] CellAutomaton.alphabetQ


  def Config (Q: Type*) := ℤ → Q

  variable (C: CellAutomaton)

  namespace CellAutomaton

    def next (c: Config C.Q): Config C.Q :=
      fun p => C.δ (c (p - 1)) (c p) (c (p + 1))

    def nextt: Config C.Q → ℕ → Config C.Q := apply_iterated C.next


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

  end CellAutomaton


  def δδ { C: CellAutomaton } (q: C.Q) := C.δ q q q

  def δδt { C: CellAutomaton } (q: C.Q) := apply_iterated δδ q

end CellAutomaton



section LCellAutomaton -- MARK: LCellAutomaton

  /--
  A cellular automaton that can map words to a configuration.
  This is the basis for cellular automata that can recognize languages.
  -/
  structure LCellAutomaton (α: Type) extends CellAutomaton where
    embed: α → Q
    border: Q

  namespace LCellAutomaton

    variable [Alphabet α] (C: LCellAutomaton α)

    def embed_word (w: Word α): Config C.Q :=
      fun p =>
        if h: p ∈ w.range
        then C.embed (w.get' p h)
        else C.border

    /-- To compute the nth configuration of a word, we compute the nth follow configuration of the word's embedding. -/
    def comp (w: Word α) := C.nextt (C.embed_word w)


    def scan_temporal (t: ℕ) (p: ℤ) (w: Word α): Word C.Q :=
      List.map (C.comp w · p) (List.range t)

    def scan_temporal_rt (w: Word α): Word C.Q :=
      C.scan_temporal w.length 0 w

    /-- A state is an internal state if embedding an input does not produce it. -/
    def internal_state (q: C.Q) := ∀ a: α, C.embed a ≠ q


  end LCellAutomaton

end LCellAutomaton



section tCellAutomaton -- MARK: tCellAutomaton

  structure tCellAutomaton (α: Type) extends LCellAutomaton α where
    t: ℕ → ℕ
    p: ℕ → ℕ
    F_pos: Q → Bool

  def tCellAutomaton.L (C: tCellAutomaton α): Language α := fun w =>
    (C.comp w (C.t w.length)) 0 |> C.F_pos

  def tCellAutomatons (α: Type): Set (tCellAutomaton α) := Set.univ

  instance : DefinesLanguage (tCellAutomaton α) α where
    L ca := ca.L


  def tCellAutomaton.similar [Alphabet α] (C1 C2: tCellAutomaton α): Prop := C1.L = C2.L ∧ C1.t = C2.t ∧ C1.p = C2.p

  section

    variable (α: Type)

    def t_rt (S: Set (tCellAutomaton α)) := { C ∈ S | ∀ n, C.t n = n - 1 }
    def t_2n (S: Set (tCellAutomaton α)) := { C ∈ S | ∀ n, C.t n = 2 * n }
    def t_lt (S: Set (tCellAutomaton α)) := { C ∈ S | ∃ c: ℕ, ∀ n, C.t n = c * n }

    def CA   := { C ∈ tCellAutomatons α | C.p = fun _ => 0 }
    def CA_rt := CA α |> t_rt α
    def CA_2n := CA α |> t_2n α
    def CA_lt := CA α |> t_lt α

    def CAr  := { C ∈ tCellAutomatons α | C.p = fun n => n }

    def OCA  := { C ∈ CA α | C.left_independent }
    def OCA_rt := OCA α |> t_rt α
    def OCA_2n := OCA α |> t_2n α
    def OCA_lt := OCA α |> t_lt α

    def OCAr  := { C ∈ CAr α | C.right_independent }
    def OCAr_rt := OCAr α |> t_rt α
    def OCAr_2n := OCAr α |> t_2n α
    def OCAr_lt := OCAr α |> t_lt α

  end

end tCellAutomaton



instance (C: tCellAutomaton α) (w: Word α) : Decidable (w ∈ C.L) := by
  unfold tCellAutomaton.L
  unfold Membership.mem
  unfold Language.instMembershipList
  simp [Set.Mem]
  infer_instance


instance (C: tCellAutomaton α) : DecidablePred C.L :=
  fun w => by
    unfold tCellAutomaton.L
    infer_instance



section tCellAutomatonWithAdvice -- MARK: tCellAutomatonWithAdvice

  structure Advice (α: Type) (Γ: Type) where
    f: Word α → Word Γ
    len: ∀ w: Word α, (f w).length = w.length

  @[simp]
  lemma advice_len {α Γ} (adv: Advice α Γ) (w: Word α): (adv.f w).length = w.length := by
    simp [adv.len]

  def zip_words {α β} (w: List α) (a: List β) := List.zipWith (·,·) w a

  infixl:65 " ⊗ " => zip_words

  @[app_unexpander zip_words]
  def unexpand_zip_words : Lean.PrettyPrinter.Unexpander
  | `($_ $w $a) => `($w ⊗ $a)
  | _ => throw ()


  namespace Advice
    section
      variable {Γ: Type} {adv: Advice α Γ}

      def annotate (w: Word α): Word (α × Γ) := w ⊗ (adv.f w)

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

  def tCellAutomatonWithAdvice.L (C: tCellAutomatonWithAdvice α): Language α := { w | C.C.L (C.adv.annotate w) }


  def tCellAutomatonWithAdvice.with_advice {Γ: Type} [Alphabet Γ] (S: Set (tCellAutomaton (α × Γ))) (adv: Advice α Γ)
      : Set (tCellAutomatonWithAdvice α) :=
    { tCellAutomatonWithAdvice.mk Γ adv C | C ∈ S }

  instance {Γ: Type} [Alphabet Γ] : HAdd (Set (tCellAutomaton (α × Γ))) (Advice α Γ) (Set (tCellAutomatonWithAdvice α)) where
    hAdd S adv := tCellAutomatonWithAdvice.with_advice S adv

  instance [Alphabet α] : DefinesLanguage (tCellAutomatonWithAdvice α) α where
    L ca := tCellAutomatonWithAdvice.L ca




  def Advice.rt_closed {Γ: Type} [Alphabet α] [Alphabet Γ] (f: Advice α Γ) :=
      ℒ (CA_rt (α × Γ) + f) = ℒ (CA_rt α)





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





  structure CArtTransducer (α: Type) (Γ: Type) [Alphabet α] [Alphabet Γ] extends LCellAutomaton α where
    f: Q → Γ


  def CArtTransducer.advice [Alphabet α] [Alphabet Γ] (adv: CArtTransducer α Γ): Advice α Γ :=
    ⟨
      fun w => (adv.scan_temporal_rt w).map adv.f,
      by grind [LCellAutomaton.scan_temporal_rt, LCellAutomaton.scan_temporal]
    ⟩






  structure TwoStageAdvice (α: Type) (Γ: Type) [Alphabet α] [Alphabet Γ]  where
    β: Type
    [alphabetβ: Alphabet β]
    C: CArtTransducer α β
    M: FiniteStateTransducer β Γ

  attribute [instance] TwoStageAdvice.alphabetβ

  namespace TwoStageAdvice
    variable {α: Type} {Γ: Type} [Alphabet α] [Alphabet Γ] {adv: TwoStageAdvice α Γ}

    def advice: Advice α Γ :=
      ⟨
        adv.M.advice.f ∘ adv.C.advice.f,
        by grind [Advice.len]
      ⟩

  end TwoStageAdvice



  def Advice.is_two_stage_advice [Alphabet α] [Alphabet Γ] (adv: Advice α Γ): Prop :=
    ∃ ts_adv: TwoStageAdvice α Γ, adv = ts_adv.advice





  def Advice.prefixes_in_L (L: Language α) [h: DecidablePred L]: Advice α Bool :=
    ⟨
      fun w => (List.range w.length).map (fun i => decide (L (w⟦0..i+1⟧))),
      by simp
    ⟩


  def Advice.exp: Advice α Bool :=
    ⟨
      fun w => (List.range w.length).map fun i => i == 2 ^ (Nat.log2 i),
      by simp
    ⟩



  def Advice.from_len_marker (f: ℕ → Option ℕ): Advice α Bool :=
    ⟨
      fun w =>
        let idx := f w.length
        (List.range w.length).map fun i => some (i + 1) == idx,
      by simp
    ⟩



  def middle_idx (n: ℕ) := n / 2

  def Advice.middle (α): Advice α Bool := Advice.from_len_marker (some ∘ middle_idx)

  #guard (List.range 10).map (fun n => (n, middle_idx n)) =
    [(0,0), (1,0), (2,1), (3,1), (4,2), (5,2), (6,3), (7,3), (8,4), (9,4)]

  #guard (@Advice.middle Unit).f (List.replicate 10 ()) =
    [false, false, false, false, true, false, false, false, false, false]



  -- runs the biggest value 2^k such that 2^(k+1) <= n, if such exists
  def exp_middle_idx (n: ℕ) :=
    (List.range n).map (2 ^ ·)
    |> List.filter (· * 2 ≤ n)
    |> List.max?

  -- Marks the biggest exponent of 2 that is less than or equal to the length of the word
  def Advice.exp_middle (α): Advice α Bool := Advice.from_len_marker exp_middle_idx

  #guard (List.range 10).map (fun n => (n, exp_middle_idx n)) =
    [(0, none), (1, none), (2, some 1), (3, some 1), (4, some 2), (5, some 2), (6, some 2), (7, some 2), (8, some 4), (9, some 4)]

  #guard (@Advice.exp_middle Unit).f (List.replicate 10 ()) =
    [false, false, false, true, false, false, false, false, false, false]



  def Advice.shift_left_advice {adv: Advice α Γ} (extension: Word α): Advice α Γ :=
    ⟨
      fun w => (adv.f (w.append extension)).drop extension.length,
      by simp [adv.len]
    ⟩

end tCellAutomatonWithAdvice
