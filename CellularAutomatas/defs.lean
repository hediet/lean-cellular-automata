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

    class Alphabet where
        (α: Type u)
        [dec: DecidableEq α]
        [fin: Fintype α]
        [inh: Inhabited α]

    instance (A: Alphabet) : DecidableEq A.α := A.dec
    instance (A: Alphabet) : Fintype A.α     := A.fin
    instance (A: Alphabet) : Inhabited A.α  := A.inh

    def 𝒰 : Alphabet := ⟨ Unit ⟩
    def ℬ : Alphabet := ⟨ Bool ⟩

    def char : Alphabet where
        α := Char
        fin := sorry


    def ProductAlphabet (a b: Alphabet) : Alphabet := ⟨ a.α × b.α ⟩


    infix:50 " ⨉ " => ProductAlphabet


    variable [Alphabet]

    def α := Alphabet.α
    def Word := List α

    namespace Word
        notation w "⟦" a ".." b "⟧" => List.extract w a b

        def range (w: Word): Set ℤ := { i: ℤ | i ≥ 0 ∧ i < w.length }

        instance (w: Word) (i: ℤ): Decidable (i ∈ w.range) := by
            unfold range
            infer_instance

        def get' (w: Word) (i: ℤ) (h: i ∈ w.range) := w.get ⟨
            i.toNat,
            by simp only [range, ge_iff_le, Set.mem_setOf_eq] at h; omega
        ⟩
    end Word


end Word


section LanguageDefinitions -- MARK: LanguageDefinitions
    variable [Alphabet]

    class DefinesLanguage (CA: Type u) where
        A: Alphabet
        L: CA -> Language A.α

    def ℒ {CA: Type u} [d: DefinesLanguage CA] (s: (Set CA)): Set (Language d.A.α) :=
        fun L => ∃ ca: CA, ca ∈ s ∧ L = DefinesLanguage.L ca

    class DefinesTime (CA: Type u) where
        time: CA -> Word → WithTop ℕ

    noncomputable def time' [DefinesTime CA] (C: CA) (w: Word): ℕ := (DefinesTime.time C w).getD 0



    noncomputable def t_max [DefinesTime CA] (ca: CA) (n: ℕ): WithTop ℕ :=
        sSup (DefinesTime.time ca '' { w : Word | w.length = n })

    def halts [DefinesTime CA] (ca: CA): Prop :=
        ∀ n: ℕ, t_max ca n ≠ none

    noncomputable def t_max' [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ :=
        (t_max ca n).get (by simp_all[halts, Option.isSome_iff_ne_none])


    def with_time { β: Type u } [DefinesTime β] (fns: Set (ℕ → ℕ)) (set: Set β): Set β :=
        fun ca => ca ∈ set ∧ halts ca ∧ ((h: halts ca) → ((t_max' ca h) ∈ fns))


    syntax "t⦃" term "⦄" : term
    macro_rules | `(t⦃ $expr ⦄) => `(with_time { fun $(Lean.mkIdent `n) => $expr })



end LanguageDefinitions



section CellAutomaton -- MARK: CellAutomaton
    variable [Alphabet]

    structure CellAutomaton where
        Q: Type u
        [decQ: DecidableEq Q]
        [finQ: Fintype Q]
        δ: Q → Q → Q → Q

    instance (A : CellAutomaton) : DecidableEq A.Q := A.decQ
    instance (A : CellAutomaton) : Fintype A.Q     := A.finQ

    def Config (Q: Type*) := ℤ → Q

    variable (C: CellAutomaton)

    namespace CellAutomaton

        def next (c: Config C.Q): Config C.Q :=
            fun i => C.δ (c (i - 1)) (c i) (c (i + 1))

        def nextt: Config C.Q → ℕ → Config C.Q := apply_iterated C.next


        /-- A set is passive if every element stays the same when it is just surrounded by other elements from the set.  -/
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
    variable [A: Alphabet]

    /--
    A cellular automaton that can map words to a configuration.
    This is the basis for cellular automata that can recognize languages.
    -/
    structure LCellAutomaton [A: Alphabet.{u}] extends CellAutomaton.{u} where
        embed: α → Q
        border: Q

    namespace LCellAutomaton

        def embed_word (C: LCellAutomaton) (w: Word): Config C.Q :=
            fun i =>
                if h: i ∈ w.range
                then C.embed (w.get' i h)
                else C.border

        /-- To compute the nth configuration of a word, we compute the nth follow configuration of the word's embedding. -/
        def comp (C: LCellAutomaton) (w: Word) := C.nextt (C.embed_word w)

        /-- A state is an internal state if embedding an input does not produce it. -/
        def internal_state {C: LCellAutomaton} (q: C.Q) := ∀ a: α, C.embed a ≠ q

        instance (C: LCellAutomaton) : Inhabited C.Q := ⟨ C.border ⟩

    end LCellAutomaton

end LCellAutomaton

section FCellAutomaton -- MARK: FCellAutomaton
    variable [Alphabet]

    /-- A cellular automaton that can recognize languages by defining "accepting" and "rejecting" states. -/
    structure FCellAutomaton extends LCellAutomaton where
        /--
            * `none`: continue
            * `some true`: accept
            * `some false`: reject
        -/
        state_accepts: Q -> Option Bool

    namespace FCellAutomaton


        def config_accepts (C: FCellAutomaton) (c: Config C.Q) := C.state_accepts (c 0)

        noncomputable def time (C: FCellAutomaton) (w: Word): Option ℕ :=
            min_nat { t | C.config_accepts (C.comp w t) ≠ none }

        def accepts (C: FCellAutomaton) (w: Word) :=
            match C.time w with
            | some t => C.config_accepts (C.comp w t) = some true
            | none => False

        def L (C: FCellAutomaton): Language α := { w: Word | C.accepts w }

        def F_pos { C': FCellAutomaton } := { q: C'.Q | C'.state_accepts q = some true }
        def F_neg { C': FCellAutomaton } := { q: C'.Q | C'.state_accepts q = some false }

        def accept_delta_closed (C: FCellAutomaton) := C.delta_closed_set C.F_pos ∧ C.delta_closed_set C.F_neg


        def FCellAutomatons [α: Alphabet]: Set FCellAutomaton := fun _a => true

        instance [α: Alphabet] : DefinesLanguage FCellAutomaton where
            A := α
            L ca := ca.L

        noncomputable instance : DefinesTime FCellAutomaton where
            time ca w := ca.time w

        instance : Coe FCellAutomaton CellAutomaton where
            coe ca := ca.toCellAutomaton

    end FCellAutomaton

end FCellAutomaton

section tCellAutomaton -- MARK: tCellAutomaton

    structure tCellAutomaton {a: Alphabet} extends @LCellAutomaton a where
        t: ℕ → ℕ
        p: ℕ → ℕ
        F_pos: Q → Bool

    def tCellAutomaton.L (C: @tCellAutomaton A): Language A.α := fun w =>
        (C.comp w (C.t w.length)) 0 |> C.F_pos

    def tCellAutomatons.{u} [α: Alphabet.{u}]: Set (@tCellAutomaton.{u} α) := Set.univ

    instance {A: Alphabet} : DefinesLanguage (@tCellAutomaton A) where
        A := A
        L ca := ca.L

    instance {A: Alphabet} : DefinesTime (@tCellAutomaton A) where
        time ca w := some (ca.t w.length)

    instance [A: Alphabet] : Coe (@tCellAutomaton A) CellAutomaton where
        coe ca := ca.toCellAutomaton

    def tCellAutomaton.similar (C1 C2: @tCellAutomaton A): Prop := C1.L = C2.L ∧ C1.t = C2.t ∧ C1.p = C2.p

    section

        variable [A: Alphabet]

        def t_rt  (S: Set (@tCellAutomaton A)) := { C ∈ S | ∀ n, C.t n = n - 1 }
        def t_2n (S: Set (@tCellAutomaton A)) := { C ∈ S | ∀ n, C.t n = 2 * n }
        def t_lt  (S: Set (@tCellAutomaton A)) := { C ∈ S | ∃ c: ℕ, ∀ n, C.t n = c * n }

        def CA    := { C ∈ tCellAutomatons | C.p = fun _ => 0 }
        def CA_rt := CA |> t_rt
        def CA_2n := CA |> t_2n
        def CA_lt := CA |> t_lt

        def CAr   := { C ∈ tCellAutomatons | C.p = fun n => n }

        def OCA    := { C ∈ CA | C.left_independent }
        def OCA_rt := OCA |> t_rt
        def OCA_2n := OCA |> t_2n
        def OCA_lt := OCA |> t_lt

        def OCAr   := { C ∈ CAr | C.right_independent }
        def OCAr_rt := OCAr |> t_rt
        def OCAr_2n := OCAr |> t_2n
        def OCAr_lt := OCAr |> t_lt

    end

end tCellAutomaton



instance {A: Alphabet} (C: tCellAutomaton) (w: Word) : Decidable (w ∈ C.L) := by
    unfold tCellAutomaton.L
    unfold Membership.mem
    unfold Language.instMembershipList
    simp [Set.Mem]
    infer_instance


instance {A: Alphabet} (C: @tCellAutomaton A) : DecidablePred C.L :=
  fun w => by
    unfold tCellAutomaton.L
    infer_instance



section OCellAutomaton -- MARK: OCellAutomaton

    structure Advice.{u} (A Γ: Alphabet.{u}) where
        f: @Word A → @Word Γ
        len: ∀ w: @Word A, (f w).length = w.length

    def tensor_product {α β} (w: List α) (a: List β) := List.zipWith (·,·) w a

    infixl:65 " ⊗ " => tensor_product

    @[app_unexpander tensor_product]
    def unexpandTensorProduct : Lean.PrettyPrinter.Unexpander
      | `($_ $w $a) => `($w ⊗ $a)
      | _ => throw ()


    def Advice.annotate {A Γ: Alphabet} (adv: Advice A Γ) (w: @Word A): @Word (A ⨉ Γ) := w ⊗ (adv.f w)

    def Advice.compose {A Γ₁ Γ₂: Alphabet} (adv1: Advice A Γ₁) (adv2: Advice Γ₁ Γ₂): Advice A Γ₂ :=
        ⟨ fun w => adv2.f (adv1.f w), by simp [adv1.len, adv2.len] ⟩

    def Advice.prefix_stable {A Γ: Alphabet} (adv: Advice A Γ): Prop :=
        ∀ w: @Word A, ∀ i: ℕ,
            adv.f (w⟦0..i⟧) = (adv.f w)⟦0..i⟧



    structure OCellAutomaton [A: Alphabet] where
        /-- The alphabet of the advice. -/
        Γ: Alphabet
        adv: Advice A Γ
        C: @tCellAutomaton (A ⨉ Γ)


    def OCellAutomaton.L {A: Alphabet} (C: @OCellAutomaton A): Language α := { w | C.adv.annotate w ∈ C.C.L }

    def OCellAutomaton.with_advice (A Γ: Alphabet) (S: Set (@tCellAutomaton (A ⨉ Γ))) (adv: Advice A Γ): Set (@OCellAutomaton A) :=
        { @OCellAutomaton.mk A Γ adv C | C ∈ S }

    instance [A: Alphabet] [Γ: Alphabet] : HAdd (Set (@tCellAutomaton (ProductAlphabet A Γ))) (Advice A Γ) (Set (@OCellAutomaton A)) where
        hAdd S adv := @OCellAutomaton.with_advice A Γ S adv

    instance [A: Alphabet] : DefinesLanguage OCellAutomaton where
        A := A
        L ca := OCellAutomaton.L ca


    def Advice.rt_closed {A: Alphabet} {Γ: Alphabet} (f: Advice A Γ) :=
        ℒ (@CA_rt (A ⨉ Γ) + f) = ℒ (@CA_rt A)





    structure FiniteStateMachine.{u} [A: Alphabet.{u}] where
        Q: Type u
        [decQ: DecidableEq Q]
        [finQ: Fintype Q]
        δ: Q → α → Q
        q0: Q

    namespace FiniteStateMachine

        instance [A: Alphabet] (M : FiniteStateMachine) : DecidableEq M.Q := M.decQ
        instance [A: Alphabet] (M : FiniteStateMachine) : Fintype M.Q     := M.finQ
        instance [A: Alphabet] (M : FiniteStateMachine) : Inhabited M.Q := ⟨ M.q0 ⟩

        def Qalpha {A: Alphabet} (M: @FiniteStateMachine A): Alphabet := ⟨ M.Q ⟩

        def scan_left {A: Alphabet} {M: FiniteStateMachine} (w: @Word A): @Word M.Qalpha :=
            (List.scanl M.δ M.q0 w).tail

        def scan_right_rev {A: Alphabet} (M: FiniteStateMachine): (w: @Word A) -> @Word M.Qalpha :=
            List.reverse ∘ M.scan_left ∘ List.reverse

    end FiniteStateMachine



    def LCellAutomaton.Qalpha {A: Alphabet} { C: @LCellAutomaton A }: Alphabet := ⟨ C.Q ⟩

    def LCellAutomaton.scan_temporal {A: Alphabet} (C: LCellAutomaton) (w: @Word A): @Word C.Qalpha :=
        List.map (C.comp w · 0) (List.range w.length)

    structure TwoStageAdvice (A: Alphabet) (O: Alphabet) where
        C: @LCellAutomaton A
        M: @FiniteStateMachine C.Qalpha
        t: M.Qalpha.α -> O.α

    namespace TwoStageAdvice

        def advice {A O: Alphabet} (adv: TwoStageAdvice A O): Advice A O :=
            ⟨
                fun w => w
                    |> adv.C.scan_temporal
                    |> adv.M.scan_right_rev
                    |> List.map adv.t ,
                by simp [LCellAutomaton.scan_temporal, FiniteStateMachine.scan_right_rev, FiniteStateMachine.scan_left]
            ⟩

    end TwoStageAdvice



    def Advice.is_two_stage_advice {A O: Alphabet} (adv: Advice A O): Prop :=
        ∃ ts_adv: TwoStageAdvice A O, adv = ts_adv.advice



    def Advice.prefixes_in_L {A: Alphabet} (L: Language A.α) [h: DecidablePred L]: Advice A ℬ :=
        ⟨ fun w => (List.range w.length).map (fun i => decide (L (w⟦0..i+1⟧))), by simp ⟩


    def Advice.exp {A: Alphabet}: Advice A ℬ :=
        ⟨
            fun w => (List.range w.length).map fun i => i == 2 ^ (Nat.log2 i),
            by simp
        ⟩


    def Advice.shift_left {A Γ: Alphabet} (extension: @Word A) (adv: Advice A Γ): Advice A Γ :=
        ⟨
            fun w => (adv.f (w.append extension)).drop extension.length,
            by simp [adv.len]
        ⟩


    -- runs the biggest value 2^k such that 2^(k+1) <= n, if such exists
    def exp_middle_idx (n: ℕ) :=
        (List.range n).map (2 ^ ·)
        |> List.filter (· * 2 ≤ n)
        |> List.max?

    -- Marks the biggest exponent of 2 that is less than or equal to the length of the word
    def Advice.exp_middle {A: Alphabet}: Advice A ℬ :=
        ⟨
            fun w =>
                let idx := exp_middle_idx w.length
                (List.range w.length).map fun i => some (i + 1) == idx,
            by simp
        ⟩

    #eval! (List.range 10).map (fun n => (n, exp_middle_idx n))
    #eval! (@Advice.exp 𝒰).f (List.replicate 8 ())

end OCellAutomaton
