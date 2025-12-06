import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod


section Utilities -- MARK: Utilities

  noncomputable def min_nat (set: Set ℕ) :=
    let _dec := Classical.dec;
    if h: ∃ n, n ∈ set
    then some (Nat.find h)
    else none

  def apply_iterated (f: α → α) (a: α) (k: ℕ) := Nat.iterate f k a

end Utilities


section Word -- MARK: Word

  class Alphabet (α: Type u) where
    [dec: DecidableEq α]
    [fin: Fintype α]
    [inh: Inhabited α]

  attribute [instance] Alphabet.dec Alphabet.fin Alphabet.inh

  instance AlphabetUnit : Alphabet Unit := ⟨⟩
  instance AlphabetBool : Alphabet Bool := ⟨⟩


  instance ProductAlphabet {α β} [Alphabet α] [Alphabet β] : Alphabet (α × β) := ⟨⟩


  infix:50 " ⨉ " => Prod


  abbrev Word (α: Type u) := List α

  namespace Word
    variable {α: Type u}
    notation:max w "⟦" a ".." b "⟧" => List.extract w a b
    notation:max w "⟦" a "..*⟧" => List.drop a w

    def range (w: Word α): Set ℤ := { i: ℤ | i ≥ 0 ∧ i < w.length }

    instance (w: Word α) (i: ℤ): Decidable (i ∈ w.range) := by
      unfold range
      infer_instance

    def get' (w: Word α) (i: ℤ) (h: i ∈ w.range) := w.get ⟨
      i.toNat,
      by simp only [range, ge_iff_le, Set.mem_setOf_eq] at h; omega
    ⟩
  end Word


end Word



universe v
section LanguageDefinitions -- MARK: LanguageDefinitions

  class DefinesLanguage (CA: Type u) where
    α: Type v
    [inst: Alphabet α]
    L: CA -> Language α

  def ℒ {CA: Type u} [d: DefinesLanguage CA] (s: (Set CA)): Set (Language d.α) :=
    fun L => ∃ ca: CA, ca ∈ s ∧ L = DefinesLanguage.L ca

  class DefinesTime (CA: Type u) where
    α: Type v
    [inst: Alphabet α]
    time: CA -> Word α → WithTop ℕ

  noncomputable def time' {CA: Type u} [dt: DefinesTime CA] (C: CA) (w: Word dt.α): ℕ := (dt.time C w).getD 0



  noncomputable def t_max {CA: Type u} [dt: DefinesTime CA] (ca: CA) (n: ℕ): WithTop ℕ :=
    sSup (dt.time ca '' { w : Word dt.α | w.length = n })

  def halts {CA: Type u} [DefinesTime CA] (ca: CA): Prop :=
    ∀ n: ℕ, t_max ca n ≠ none

  noncomputable def t_max' {CA: Type u} [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ :=
    (t_max ca n).get (by simp_all[halts, Option.isSome_iff_ne_none])


  def with_time { β: Type u } [DefinesTime β] (fns: Set (ℕ → ℕ)) (set: Set β): Set β :=
    fun ca => ca ∈ set ∧ halts ca ∧ ((h: halts ca) → ((t_max' ca h) ∈ fns))


  syntax "t⦃" term "⦄" : term
  macro_rules | `(t⦃ $expr ⦄) => `(with_time { fun $(Lean.mkIdent `n) => $expr })



end LanguageDefinitions



section CellAutomaton -- MARK: CellAutomaton

  structure CellAutomaton where
    Q: Type u
    [decQ: DecidableEq Q]
    [finQ: Fintype Q]
    δ: Q → Q → Q → Q

  instance (A : CellAutomaton) : DecidableEq A.Q := A.decQ
  instance (A : CellAutomaton) : Fintype A.Q   := A.finQ

  def Config (Q: Type*) := ℤ → Q

  variable (C: CellAutomaton)

  namespace CellAutomaton

    def next (c: Config C.Q): Config C.Q :=
      fun i => C.δ (c (i - 1)) (c i) (c (i + 1))

    def nextt: Config C.Q → ℕ → Config C.Q := apply_iterated C.next


    /-- A set is passive if every element stays the same when it is just surrounded by other elements from the set. -/
    def passive_set (Q: Set C.Q) := ∀ (a b c: Q), C.δ a b c = b

    /-- A state is passive if it stays the same when it is just surrounded by itself. -/
    def passive (q: C.Q) := C.passive_set { q }

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
  structure LCellAutomaton (α: Type u) extends CellAutomaton.{u} where
    embed: α → Q
    border: Q

  namespace LCellAutomaton

    def embed_word {α: Type u} [Alphabet α] (C: LCellAutomaton α) (w: Word α): Config C.Q :=
      fun i =>
        if h: i ∈ w.range
        then C.embed (w.get' i h)
        else C.border

    /-- To compute the nth configuration of a word, we compute the nth follow configuration of the word's embedding. -/
    def comp {α: Type u} [Alphabet α] (C: LCellAutomaton α) (w: Word α) := C.nextt (C.embed_word w)

    /-- A state is an internal state if embedding an input does not produce it. -/
    def internal_state {α: Type u} [Alphabet α] {C: LCellAutomaton α} (q: C.Q) := ∀ a: α, C.embed a ≠ q

    instance {α: Type u} (C: LCellAutomaton α) : Inhabited C.Q := ⟨ C.border ⟩

  end LCellAutomaton

end LCellAutomaton

section FCellAutomaton -- MARK: FCellAutomaton

  /-- A cellular automaton that can recognize languages by defining "accepting" and "rejecting" states. -/
  structure FCellAutomaton (α: Type u) extends LCellAutomaton α where
    /--
      * `none`: continue
      * `some true`: accept
      * `some false`: reject
    -/
    state_accepts: Q -> Option Bool

  namespace FCellAutomaton


    def config_accepts {α: Type u} (C: FCellAutomaton α) (c: Config C.Q) := C.state_accepts (c 0)

    noncomputable def time {α: Type u} [Alphabet α] (C: FCellAutomaton α) (w: Word α): Option ℕ :=
      min_nat { t | C.config_accepts (C.comp w t) ≠ none }

    def accepts {α: Type u} [Alphabet α] (C: FCellAutomaton α) (w: Word α) :=
      match C.time w with
      | some t => C.config_accepts (C.comp w t) = some true
      | none => False

    def L {α: Type u} [Alphabet α] (C: FCellAutomaton α): Language α := { w: Word α | C.accepts w }

    def F_pos {α: Type u} { C': FCellAutomaton α } := { q: C'.Q | C'.state_accepts q = some true }
    def F_neg {α: Type u} { C': FCellAutomaton α } := { q: C'.Q | C'.state_accepts q = some false }

    def accept_delta_closed {α: Type u} (C: FCellAutomaton α) := C.delta_closed_set C.F_pos ∧ C.delta_closed_set C.F_neg


    def FCellAutomatons (α: Type u): Set (FCellAutomaton α) := fun _a => true

    instance {α: Type u} [Alphabet α] : DefinesLanguage (FCellAutomaton α) where
      α := α
      L ca := ca.L

    noncomputable instance {α: Type u} [Alphabet α] : DefinesTime (FCellAutomaton α) where
      α := α
      time ca w := ca.time w

    --instance {α: Type u} : Coe (FCellAutomaton α) CellAutomaton where
    --coe ca := ca.toCellAutomaton

  end FCellAutomaton

end FCellAutomaton

section tCellAutomaton -- MARK: tCellAutomaton

  structure tCellAutomaton (α: Type u) extends LCellAutomaton α where
    t: ℕ → ℕ
    p: ℕ → ℕ
    F_pos: Q → Bool

  def tCellAutomaton.L {α: Type u} [Alphabet α] (C: tCellAutomaton α): Language α := fun w =>
    (C.comp w (C.t w.length)) 0 |> C.F_pos

  def tCellAutomatons (α: Type u): Set (tCellAutomaton α) := Set.univ

  instance {α: Type u} [Alphabet α] : DefinesLanguage (tCellAutomaton α) where
    α := α
    L ca := ca.L

  instance {α: Type u} [Alphabet α] : DefinesTime (tCellAutomaton α) where
    α := α
    time ca w := some (ca.t w.length)

  --instance {α: Type u} : Coe (tCellAutomaton α) CellAutomaton where
  --  coe ca := ca.toCellAutomaton

  def tCellAutomaton.similar {α: Type u} [Alphabet α] (C1 C2: tCellAutomaton α): Prop := C1.L = C2.L ∧ C1.t = C2.t ∧ C1.p = C2.p

  section

    variable (α: Type u)

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



instance {α: Type u} [Alphabet α] (C: tCellAutomaton α) (w: Word α) : Decidable (w ∈ C.L) := by
  unfold tCellAutomaton.L
  unfold Membership.mem
  unfold Language.instMembershipList
  simp [Set.Mem]
  infer_instance


instance {α: Type u} [Alphabet α] (C: tCellAutomaton α) : DecidablePred C.L :=
 fun w => by
  unfold tCellAutomaton.L
  infer_instance



section OCellAutomaton -- MARK: OCellAutomaton

  structure Advice (α: Type u) (Γ: Type v) where
    f: Word α → Word Γ
    len: ∀ w: Word α, (f w).length = w.length

  def tensor_product {α β} (w: List α) (a: List β) := List.zipWith (·,·) w a

  infixl:65 " ⊗ " => tensor_product

  @[app_unexpander tensor_product]
  def unexpandTensorProduct : Lean.PrettyPrinter.Unexpander
  | `($_ $w $a) => `($w ⊗ $a)
  | _ => throw ()


  def Advice.annotate {α: Type u} {Γ: Type v} (adv: Advice α Γ) (w: Word α): Word (α × Γ) := w ⊗ (adv.f w)

  def Advice.compose {α: Type u} {Γ₁: Type v} {Γ₂: Type w} (adv1: Advice α Γ₁) (adv2: Advice Γ₁ Γ₂): Advice α Γ₂ :=
    ⟨ fun w => adv2.f (adv1.f w), by simp [adv1.len, adv2.len] ⟩

  def Advice.prefix_stable {α: Type u} {Γ: Type v} (adv: Advice α Γ): Prop :=
    ∀ w: Word α, ∀ i: ℕ,
      adv.f (w.take i) = (adv.f w).take i



  structure OCellAutomaton (α: Type u) where
    /-- The alphabet of the advice. -/
    Γ: Type v
    [instΓ: Alphabet Γ]
    adv: Advice α Γ
    C: tCellAutomaton (α × Γ)

  instance (A : OCellAutomaton α) : Alphabet A.Γ := A.instΓ


  def OCellAutomaton.L {α: Type u} [instA: Alphabet α] (C: OCellAutomaton α): Language α :=
    have : Alphabet C.Γ := C.instΓ
    { w | C.C.L (C.adv.annotate w) }

  def OCellAutomaton.with_advice {α: Type u} {Γ: Type v} [Alphabet Γ] (S: Set (tCellAutomaton (α × Γ))) (adv: Advice α Γ): Set (OCellAutomaton α) :=
    { OCellAutomaton.mk Γ adv C | C ∈ S }

  instance {α: Type u} {Γ: Type v} [Alphabet Γ] : HAdd (Set (tCellAutomaton (α × Γ))) (Advice α Γ) (Set (OCellAutomaton α)) where
    hAdd S adv := OCellAutomaton.with_advice S adv

  instance {α: Type u} [Alphabet α] : DefinesLanguage (OCellAutomaton α) where
    α := α
    L ca := OCellAutomaton.L ca


  def Advice.rt_closed {α: Type u} {Γ: Type v} [Alphabet α] [Alphabet Γ] (f: Advice α Γ) :=
    ℒ (CA_rt (α × Γ) + f) = ℒ (CA_rt α)





  structure FiniteStateMachine (α: Type u) where
    Q: Type u
    [decQ: DecidableEq Q]
    [finQ: Fintype Q]
    δ: Q → α → Q
    q0: Q

  namespace FiniteStateMachine

    instance {α: Type u} (M : FiniteStateMachine α) : DecidableEq M.Q := M.decQ
    instance {α: Type u} (M : FiniteStateMachine α) : Fintype M.Q   := M.finQ
    instance {α: Type u} (M : FiniteStateMachine α) : Inhabited M.Q := ⟨ M.q0 ⟩

    instance Qalpha {α: Type u} (M: FiniteStateMachine α): Alphabet M.Q := ⟨⟩


    def scanr_step {α: Type u} {M: FiniteStateMachine α} q a
    | []   => [M.δ q a]
    | qs@(q::_) => (M.δ q a :: qs)

    def scanr_q {α: Type u} {M: FiniteStateMachine α} (w: Word α) (q: M.Q): Word M.Q :=
      w.foldr (scanr_step q) []

    def scanr {α: Type u} {M: FiniteStateMachine α} w := M.scanr_q w M.q0

    def scanr_reduce {α: Type u} {M: FiniteStateMachine α} (w: Word α): M.Q :=
      match M.scanr w with
      | []   => M.q0
      | q::_ => q

    @[simp, grind =]
    lemma scanr_q_len {α: Type u} {M: FiniteStateMachine α} (q: M.Q) (w: List α):
      (M.scanr_q w q).length = w.length := by
      induction w with
      | nil => simp [scanr_q]
      | cons a ws ih =>
        simp [scanr_q]
        unfold scanr_step
        split
        · next h =>
          change M.scanr_q ws q = [] at h
          rw [← ih]
          rw [h]
          simp
        · next q' tail h =>
          change M.scanr_q ws q = q' :: tail at h
          rw [← ih]
          rw [h]
          simp


    @[simp, grind =]
    lemma scanr_len {α: Type u} (M: FiniteStateMachine α) (w: List α): (M.scanr w).length = w.length := by
      simp [scanr, scanr_q_len]



  end FiniteStateMachine



  instance LCellAutomaton.Qalpha {α: Type u} { C: LCellAutomaton α }: Alphabet C.Q := ⟨⟩

  def LCellAutomaton.scan_temporal {α: Type u} [Alphabet α] (C: LCellAutomaton α) (w: Word α): Word C.Q :=
    List.map (C.comp w · 0) (List.range w.length)

  structure TwoStageAdvice (α: Type u) [Alphabet α] (Γ: Type v) [Alphabet Γ] where
    C: LCellAutomaton α
    M: FiniteStateMachine C.Q
    t: M.Q → Γ

  variable {α: Type u} {Γ: Type v} [Alphabet α] [Alphabet Γ]

  namespace TwoStageAdvice

    def advice (adv: TwoStageAdvice α Γ): Advice α Γ :=
      ⟨
        fun w => w
          |> adv.C.scan_temporal
          |> adv.M.scanr
          |> List.map adv.t,
        by grind [LCellAutomaton.scan_temporal]
      ⟩

  end TwoStageAdvice



  def Advice.is_two_stage_advice (adv: Advice α Γ): Prop :=
    ∃ ts_adv: TwoStageAdvice α Γ, adv = ts_adv.advice



  def Advice.prefixes_in_L (L: Language α) [h: DecidablePred L]: Advice α Bool :=
    ⟨ fun w => (List.range w.length).map (fun i => decide (L (w⟦0..i+1⟧))), by simp ⟩


  def Advice.exp: Advice α Bool :=
    ⟨
      fun w => (List.range w.length).map fun i => i == 2 ^ (Nat.log2 i),
      by simp
    ⟩


  def Advice.shift_left (extension: Word α) (adv: Advice α Γ): Advice α Γ :=
    ⟨
      fun w => (adv.f (w.append extension)).drop extension.length,
      by simp [adv.len]
    ⟩

  def Advice.from_len_marker (f: ℕ → Option ℕ): Advice α Bool :=
    ⟨
      fun w =>
        let idx := f w.length
        (List.range w.length).map fun i => some (i + 1) == idx,
      by simp
    ⟩

  def middle_idx (n: ℕ) := n / 2

  def Advice.middle (α: Type u): Advice α Bool := Advice.from_len_marker (some ∘ middle_idx)

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
  def Advice.exp_middle (α: Type u): Advice α Bool := Advice.from_len_marker exp_middle_idx

  #guard (List.range 10).map (fun n => (n, exp_middle_idx n)) =
    [(0, none), (1, none), (2, some 1), (3, some 1), (4, some 2), (5, some 2), (6, some 2), (7, some 2), (8, some 4), (9, some 4)]

  #guard (@Advice.exp_middle Unit).f (List.replicate 10 ()) =
    [false, false, false, true, false, false, false, false, false, false]


end OCellAutomaton
