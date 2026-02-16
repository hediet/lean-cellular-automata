import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.ca

variable [Alphabet]

inductive cQ' (Q: Type u) where
  | border
  | state (s border: Q)
deriving Inhabited, BEq, Repr, Fintype, DecidableEq

syntax "[" term "|" term "]" : term
macro_rules | `([$a | $b]) => `(cQ'.state $a $b)

def cQ'.unwrap (q: cQ' Q) (b: Q) :=
  match q with
  | border => b
  | state s _b => s

open cQ'
infix:50 " ?? " => cQ'.unwrap

def cC'_L (C: LCellAutomaton): LCellAutomaton :=
  let _inv_fin_q := C.inv_fin_q;
  let _inv_decidable_q := C.inv_decidable_q;

  {
    Q := cQ' C.Q,
    δ
      | a@([_ | br]), b,            c
      | a,            b@([_ | br]), c
      | a,            b,            c@([_ | br])  => [ C.δ (a ?? br) (b ?? br) (c ?? br) | δδ br ]
      | border,       border,     border          => border
    embed a := state (C.embed a) C.border,
    border := border
  }

theorem cC'_L_passive (C: LCellAutomaton): (cC'_L C).passive (cC'_L C).border := by
  simp [CellAutomaton.passive, CellAutomaton.passive_set, cC'_L]

theorem cC'_L_initial (C: LCellAutomaton): (cC'_L C).initial (cC'_L C).border := by
  unfold CellAutomaton.initial cC'_L
  intro a b c a_1
  simp_all only
  split at a_1
  next x x_1 x_2 st br => simp_all only [reduceCtorEq]
  next x x_1 x_2 st br x_3 => simp_all only [imp_false, reduceCtorEq]
  next x x_1 x_2 st br x_3 x_4 => simp_all only [imp_false, reduceCtorEq]
  next x x_1 x_2 => simp_all only

theorem cC'_L_comp (C: LCellAutomaton) (w: Word) (wlen: w.length > 0) (t: ℕ) (i: ℤ):
  (cC'_L C).comp w t i = if i ∈ w.cone t then state (C.comp w t i) (δδt C.border t) else border := by
    let C' := cC'_L C
    induction t generalizing i
    case zero =>
      simp only [LCellAutomaton.comp_zero, Word.cone_zero_eq_range, δδt_zero, cC'_L]
      unfold LCellAutomaton.embed_word
      split
      case isTrue h => simp []
      case isFalse h => simp []

    case succ t ih =>
      have ih2 (i: ℤ): (C'.comp w t i).unwrap (δδt C.border t) = C.comp w t i := by
        rw [ih i]
        simp [unwrap]
        split
        case h_1 h =>
          split at h
          case isTrue => simp_all only [reduceCtorEq, cC'_L]
          case isFalse hSplit => simp [C.comp_outside_word_cone_eq_border_pow_t hSplit]
        case h_2 s b h =>
          split at h
          case isFalse hSplit => simp_all only [reduceCtorEq, cC'_L]
          case isTrue =>
            injection h with s_ b_
            simp_all

      simp [LCellAutomaton.comp_succ_eq]
      set c' := C'.comp w t
      conv =>
        pattern C'.next c' i
        unfold CellAutomaton.next
      dsimp [C', cC'_L]
      split
      case h_1 _a _b _c st br p | h_2 _a _b _c st br p alt | h_3 _a _b _c st br p alt1 alt2 =>
        conv =>
          pattern state st br ?? br
          simp [unwrap]

        rw [ih] at p
        split at p
        case isFalse h => simp_all only [reduceCtorEq, C', c', cC'_L]
        case isTrue h =>
          injection p with st_eq border_eq
          have : i ∈ w.cone (t + 1) := by
            try simp [Word.cone_prop' h]
            try simp [Word.cone_prop'' h]

          rw [border_eq] at ih2
          simp [this, δδt_succ, border_eq, ih2, ←st_eq]
          simp [CellAutomaton.next]

      case h_4 h1 h2 h3 =>
        suffices : i ∉ w.cone (t + 1)
        · simp [this]
        rw [ih (i-1)] at h1
        rw [ih i] at h2
        rw [ih (i+1)] at h3
        simp_all [ite_eq_right_iff, reduceCtorEq, imp_false, c', C', Word.cone_succ_not wlen]
