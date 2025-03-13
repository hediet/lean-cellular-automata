import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice

variable [Alphabet]

private def φ {C: LCellAutomaton} (b: C.Q) (c: C.Q) := (b, fun a => C.δ a b c)

private def Sp (C: LCellAutomaton): LCellAutomaton := by
  have x := C.inv_fin_q
  have y := C.inv_decidable_q

  exact {
    Q := C.Q × (C.Q → C.Q)
    δ := fun a b c => φ (C.δ a.fst b.fst c.fst) (c.snd b.fst),
    border := φ C.border C.border,
    embed := fun a => φ (C.embed a) C.border,
  }

private lemma sp_border_passive {C: LCellAutomaton} (h: C.passive C.border):
  (Sp C).passive (Sp C).border := by
  simp [CellAutomaton.passive, CellAutomaton.passive_set, Sp, φ, CellAutomaton.δ_of_passive h]

private lemma fst_prop {w} {C: LCellAutomaton} (t: ℕ) (i: ℤ):
    ((Sp C).comp w t i).fst = C.comp w t i := by
  induction t generalizing i with
  | zero =>
    simp [LCellAutomaton.embed_word, Sp, φ]
    grind
  | succ t ih =>
    rw [LCellAutomaton.comp_succ_eq, LCellAutomaton.comp_succ_eq]
    rw [CellAutomaton.next]
    conv in (Sp C).δ => simp [Sp, φ]
    simp [ih, CellAutomaton.next]

private lemma snd_prop (C: LCellAutomaton) (w) (t: ℕ) (i: ℤ) (h: t + i + 1 ≥ w.length):
  ((Sp C).comp w t i).snd (C.comp w t (i - 1)) = C.comp w (t + 1) i := by

  induction t generalizing i with
  | zero =>
    rw [LCellAutomaton.comp_succ_eq, LCellAutomaton.comp_zero, LCellAutomaton.comp_zero]
    set c := C.embed_word w
    simp [LCellAutomaton.embed_word, Sp]
    have cp1_border : c (i+1) = C.border := by
      have: i + 1 ∉ w.range := by simp [Word.range]; omega
      simp [c, LCellAutomaton.embed_word, this]

    split
    case zero.isTrue h_if =>
      have : C.embed (w.get' i h_if) = c i := by simp [c, LCellAutomaton.embed_word, h_if]
      simp [φ, this, cp1_border, CellAutomaton.next]
    case zero.isFalse h_if =>
      have : c i = C.border := by simp [c, LCellAutomaton.embed_word, h_if]
      simp [φ, this, cp1_border, CellAutomaton.next]

  | succ t ih =>
    rw [LCellAutomaton.comp_succ_eq, CellAutomaton.next]
    set c' := (Sp C).comp w t
    conv in (Sp C).δ => simp [Sp]
    set c := C.comp w t
    simp [c', fst_prop]
    rw [←CellAutomaton.next]

    have ih := ih (i + 1) (by omega)
    simp [c'] at ih
    rw [ih]
    unfold φ
    simp
    rw [←LCellAutomaton.comp_succ_eq]
    rw [←CellAutomaton.next]
    rw [←LCellAutomaton.comp_succ_eq]



theorem one_step_speed_up_dead (C: tCellAutomaton.{u}) (h1: ∀ n, C.t n ≥ n) (h2: C.dead C.border):
  ∃ C': tCellAutomaton.{u},
    C'.L = C.L
    ∧ C'.t = Nat.pred ∘ C.t := by

  set LC' := Sp C.toLCellAutomaton
  set t' := Nat.pred ∘ C.t
  set F_pos' := { s: LC'.Q | s.snd (C.border) ∈ C.F_pos }
  set C' := tCellAutomaton.mk LC' t' F_pos'

  use C'
  constructor
  case h.right => simp [t', C']

  funext w
  set n := w.length

  cases c: n
  case h.left.h.zero =>
    have : w = [] := by simp_all only [ge_iff_le, List.length_eq_zero_iff, n]
    rw [this]

    have border_passive := (CellAutomaton.passive_of_dead h2)

    have C'_border_passive: C'.passive C'.border := by
       have := sp_border_passive border_passive
       simp [C', LC', this]

    simp [tCellAutomaton.accepts_empty_iff_of_passive border_passive,
      tCellAutomaton.accepts_empty_iff_of_passive C'_border_passive]
    simp [F_pos', C', LC', Sp, φ, CellAutomaton.δ_of_passive border_passive]


  case h.left.h.succ n' =>

  suffices : ((C'.comp w (t' n) 0).snd C.border ∈ C.F_pos) ↔ C.comp w (C.t n) 0 ∈ C.F_pos
  · have r : (C'.comp w (t' n) 0).snd C.border ∈ C.F_pos ↔ (C'.comp w (t' n) 0) ∈ C'.F_pos := by simp [C', F_pos']
    rw [r] at this
    simp [n] at this
    simp [tCellAutomaton.L]
    exact this

  have : C.comp w ((C.t n)-1) (0-1) = C.border := by
    apply LCellAutomaton.dead_border_comp
    · simp_all
    · simp [Word.range]
  rw [←this]
  simp only [Function.comp_apply, Nat.pred_eq_sub_one, C', LC', t']
  have x := snd_prop C.toLCellAutomaton w ((C.t n)-1) 0


  rw [x]

  have : C.t n - 1 + 1 = C.t n := by
    have : C.t n ≥ n := by simp_all
    have : C.t n > 0 := by omega
    omega

  simp [this]

  have : w.length = n := by simp [n]
  rw [this]

  suffices : ↑(C.t n - 1) + 0 + (1: ℤ) = C.t n;
  · rw [this]
    simp [h1]

  have : C.t n ≥ 1 := by
    rw [c]
    have := h1 (n' + 1)
    omega

  omega


theorem one_step_speed_up (C: tCellAutomaton.{u}) (h1: ∃ c, ∀ n, C.t n ≤ c * (n + 1)) (h2: ∀ n, C.t n ≥ n):
  ∃ C': tCellAutomaton.{u},
    C'.L = C.L
    ∧ C'.t = Nat.pred ∘ C.t := by

  have ⟨ C'', C''_L, C''_t, C''_dead ⟩ := tCellAutomaton.linear_time_dead_border C h1
  rw [←C''_t] at h2
  rw [←C''_L, ←C''_t]
  apply one_step_speed_up_dead C'' h2 C''_dead



private lemma speed_up_k (C : tCellAutomaton.{u}) (k: ℕ) (h1: ∃ c, ∀ n, C.t n ≤ c * (n + 1)) (h2 : ∀ n, C.t n ≥ n + k - 1):
    ∃ C': tCellAutomaton.{u},
      C'.L = C.L
      ∧ C'.t = (Nat.iterate Nat.pred k) ∘ C.t := by
induction k generalizing C with
| zero =>
  use C
  simp
| succ k ih =>
  obtain ⟨ C', h'_L, h'_t ⟩ := one_step_speed_up C h1 (by intro n; specialize h2 n; omega)
  obtain ⟨ C'', h''_L, h''_t ⟩ := ih C' (by
    obtain ⟨ c, hc ⟩ := h1
    use c
    intro n
    specialize hc n
    rw [h'_t]
    simp
    omega
  ) (by
    intro n
    specialize h2 n
    rw [h'_t]
    simp
    omega
  )
  use C''
  simp_all [Function.comp_assoc]



-- question: Why do I need .{u} here twice?
theorem const_speed_up: ℒ ({ C ∈ tCellAutomatons.{u} | ∃ k, ∀ n, C.t n = n + k - 1 }) = ℒ (RT.{u}) := by
  apply Set.Subset.antisymm
  · intro L ⟨ C, hL1, hL2 ⟩
    simp [tCellAutomatons] at hL1
    obtain ⟨ k, hk ⟩ := hL1

    have ⟨ C', h ⟩ := speed_up_k C k (by use (k+1); intro n; specialize hk n; rw [hk]; grind ) (by simp [hk])
    use C'
    constructor
    · unfold RT
      constructor
      · simp [tCellAutomatons]
      intro n

      specialize hk n
      rw [h.2, Function.comp_apply, hk, Nat.pred_iterate]
      omega

    · simp [DefinesLanguage.L, h.1, hL2]

  · intro L ⟨ C, hL1, hL2 ⟩
    simp [RT] at hL1
    use C
    constructor
    · simp [tCellAutomatons]
      use 0
      intro n
      simp [hL1.2 n]
    · simp_all
