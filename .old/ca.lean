import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some_defs
import CellularAutomatas.find_some

lemma neq_of_internal_state {C: LCellAutomaton} (q: C.Q) {w i} (h1: i ∈ w.cone 0) (h3: C.internal_state q): C.embed_word w i ≠ q := by
  rw [LCellAutomaton.embed_word_eq_embed h1]
  aesop

lemma next_eq_of_initial {C: LCellAutomaton} { q: C.Q } {c: Config C.Q} {i: ℤ} (h1: C.initial q) (h2: C.next c i = q): c i = q := by
  subst h2
  apply h1
  · rfl

lemma comp_eq_of_initial {C: LCellAutomaton} { q: C.Q } {w: Word} {t: ℕ} {i: ℤ} (h1: C.initial q) (h2: C.comp w (t+1) i = q):
    C.comp w t i = q := by
  simp [LCellAutomaton.comp_succ_eq] at h2
  exact next_eq_of_initial h1 h2

lemma LCellAutomaton.initial_internal_of_cone (C: LCellAutomaton) { q: C.Q } {w: Word} {t: ℕ} {i: ℤ} (h1: i ∈ w.cone 0) (h2: C.initial q) (h3: C.internal_state q):
    C.comp w t i ≠ q := by

  induction t
  case zero =>
    simp [h3, neq_of_internal_state q h1]
  case succ t ih =>
    by_contra eq
    simp_all only [ne_eq, not_true_eq_false, comp_eq_of_initial h2 eq]


lemma LCellAutomaton.dead_border_comp {C: LCellAutomaton} (h1: C.dead C.border) (w: Word) (t: ℕ) {n: ℤ} (h2: n ∉ w.range):
    C.comp w t n = C.border := by
  induction t generalizing n with
  | zero =>
    simp [LCellAutomaton.comp_zero, LCellAutomaton.embed_word, h2]
  | succ t ih =>
    rw [LCellAutomaton.comp_succ_eq, CellAutomaton.next]
    simp [ih h2, CellAutomaton.delta_of_dead h1]

lemma next_initial { C: LCellAutomaton } { q: C.Q } { w: Word } { t: ℕ } (h1: C.initial q) (h2: C.next (C.comp w t) i = q): C.comp w t i = q :=
  by
  subst h2
  apply h1
  · rfl












def FCellAutomaton.comp_accepts (C: FCellAutomaton) (w) := C.config_accepts ∘ C.comp w


-- noncomputable def FCellAutomaton.accepts' {C: FCellAutomaton} (w) := find_some (C.comp_accepts w) == some true

lemma FCellAutomaton.time_eq {C: FCellAutomaton} {w}: C.time w = find_some_idx (C.comp_accepts w) := by
  simp [←min_nat_eq, FCellAutomaton.time, comp_accepts, FCellAutomaton.config_accepts]

lemma FCellAutomaton.time_eq_none_iff {C: FCellAutomaton} {w} : C.time w = none ↔ ∀ t, C.comp_accepts w t = none := by
  simp [FCellAutomaton.time_eq, find_some_idx_eq_none_iff]


lemma FCellAutomaton.time_eq_some_iff {C: FCellAutomaton} {w t}:
    C.time w = some t ↔ ∃ val, C.comp_accepts w t = some val ∧ ∀ i < t, C.comp_accepts w i = none := by
  simp only [FCellAutomaton.time_eq, find_some_idx_eq_some_iff]




lemma FCellAutomaton.comp_accepts_eq_config_accepts_comp {C: FCellAutomaton} {w} {t}: C.comp_accepts w t = C.config_accepts (C.comp w t) := by
  simp [comp_accepts]

lemma FCellAutomaton.accepts_iff {C: FCellAutomaton} {w}: C.accepts w ↔ find_some (C.comp_accepts w) = some true := by
  simp only [FCellAutomaton.accepts, FCellAutomaton.time_eq, find_some_idx, ←comp_accepts_eq_config_accepts_comp, find_some]
  cases c: find_some_idxd (C.comp_accepts w)
  case none =>
    simp_all
  case some val =>
    rw [find_some_idxd_eq_some_iff] at c
    simp only [Option.map_some, c]



def FCellAutomaton.comp_state_accepts { C: FCellAutomaton } (q: C.Q) :=
  find_some_bounded (C.state_accepts ∘ δδt q) C.inv_fin_q.card == some true

@[simp]
lemma FCellAutomaton.uniform_config_accepts_eq {C: FCellAutomaton}: (C.config_accepts ∘ uniform_config) = C.state_accepts := by
  funext
  simp [FCellAutomaton.config_accepts, uniform_config]


def FCellAutomaton.state_accepts_repeatingFunction (C: FCellAutomaton): RepeatingFunction (C.state_accepts ∘ δδt C.border) := by
  apply repeating_function_of_composition
  unfold δδt
  apply repeating_function_of_iterate_fin_type (C.inv_fin_q)


lemma FCellAutomaton.accepts_empty_iff_comp_state_accepts_border {C: FCellAutomaton}: C.accepts [] ↔ C.comp_state_accepts C.border = true := by
  simp only [accepts_iff, comp_accepts, LCellAutomaton.comp_empty_eq_uniform, comp_state_accepts, beq_iff_eq]
  simp only [←Function.comp_assoc, FCellAutomaton.uniform_config_accepts_eq]
  rw [←find_some_bounded_eq_find_some_of_repeating_function (FCellAutomaton.state_accepts_repeatingFunction C)]
  simp [FCellAutomaton.state_accepts_repeatingFunction, repeating_function_of_composition, repeating_function_of_iterate_fin_type ]



instance h {C: FCellAutomaton}: Nonempty C.Q := ⟨ C.border ⟩

@[simp]
lemma FCellAutomaton.Q_card_gt_zero {C: FCellAutomaton}: C.inv_fin_q.card > 0 := by
  have x := C.inv_fin_q.card_ne_zero
  omega

lemma FCellAutomaton.state_pow_accepts_of_passive {C: FCellAutomaton} {q: C.Q} (h: C.passive q): C.comp_state_accepts q = (C.state_accepts q = some true) := by
  simp [FCellAutomaton.comp_state_accepts, find_some_bounded_eq_some_iff, CellAutomaton.δδt_of_passive h]
  intro h2
  use 0
  simp

lemma FCellAutomaton.accepts_empty_passive {C: FCellAutomaton} (h: C.passive C.border):
    C.accepts [] ↔ C.state_accepts C.border = some true := by
  rw [FCellAutomaton.accepts_empty_iff_comp_state_accepts_border]
  rw [FCellAutomaton.state_pow_accepts_of_passive h]





lemma L_eq_iff (C C': FCellAutomaton): C'.L = C.L ↔ (∀ w, C'.accepts w ↔ C.accepts w) := by
  unfold FCellAutomaton.L
  rw [Set.ext_iff]
  rfl



noncomputable def FCellAutomaton.time' (C: FCellAutomaton) (w: Word): ℕ := (C.time w).getD 0


lemma FCellAutomaton.accepts_iff_time (C: FCellAutomaton) (w: Word):
    C.accepts w ↔ C.comp_accepts w (C.time' w) = some true := by
  unfold FCellAutomaton.time'
  rw [time_eq]
  rw [C.accepts_iff]
  rw [find_some_eq_val_at_find_some_idx (C.comp_accepts w)]


inductive TimeCases (C: FCellAutomaton) (w): Prop
| none (h1: C.time w = none) (h2: C.time' w = 0)
| some t (h1: C.time w = some t) (h2: C.time' w = t)

lemma tc C w: TimeCases C w := by
  cases c: C.time w
  case none => simp [TimeCases.none, c, FCellAutomaton.time']
  case some => simp [TimeCases.some, c, FCellAutomaton.time']

lemma comp_accepts_eq {C: FCellAutomaton} {t: ℕ} {w: Word}: C.comp_accepts w t = C.state_accepts (C.comp w t 0) := by
  simp [FCellAutomaton.comp_accepts, FCellAutomaton.config_accepts]


@[simp]
lemma accept_delta_closed' (C: FCellAutomaton) (h: C.accept_delta_closed) (k: ℕ):
    C.comp_accepts w (C.time' w + k) = C.comp_accepts w (C.time' w) := by
  induction k
  case zero => simp
  case succ k ih =>
    cases tc C w
    case none h1 h2 => simp_all [FCellAutomaton.time_eq_none_iff.mp h1]
    case some t h1 h2 =>
      simp_all only []

      have ⟨ accepts, ⟨ h_accepts, _ ⟩ ⟩ := FCellAutomaton.time_eq_some_iff.mp h1

      rw [←ih]
      simp only [comp_accepts_eq] at *

      have : (t + (k + 1)) = (t + k) + 1 := by omega
      simp only [this, LCellAutomaton.comp_succ_eq]
      set c := C.comp w (t + k)
      unfold FCellAutomaton.accept_delta_closed at h

      cases c_accepts: accepts
      case false =>
        have : c 0 ∈ C.F_neg := by simp_all [FCellAutomaton.F_neg]
        have : (C.next c) 0 ∈ C.F_neg := CellAutomaton.next_state_of_closed_set_state (h.2) this
        have : C.state_accepts ((C.next c) 0) = some accepts := by simp_all [FCellAutomaton.F_neg]
        simp_all

      case true =>
        have : c 0 ∈ C.F_pos := by simp_all [FCellAutomaton.F_pos]
        have : (C.next c) 0 ∈ C.F_pos := CellAutomaton.next_state_of_closed_set_state (h.1) this
        have : C.state_accepts ((C.next c) 0) = some accepts := by simp_all [FCellAutomaton.F_pos]
        simp_all



lemma accept_delta_closed { C: FCellAutomaton } (h: C.accept_delta_closed) (k: ℕ):
  C.accepts w ↔ C.comp_accepts w (C.time' w + k) = some true
:= by simp [accept_delta_closed' C h, C.accepts_iff_time]











lemma tCellAutomaton.accepts_empty_iff_of_passive {C: tCellAutomaton} (h: C.passive C.border):
    C.L [] ↔ C.border ∈ C.F_pos := by
  simp [tCellAutomaton.L, LCellAutomaton.comp_empty_eq_uniform, CellAutomaton.δδt_of_passive h]


lemma tCellAutomaton.accepts_empty_iff {C: tCellAutomaton}:
    C.L [] ↔ δδt C.border (C.t 0) ∈ C.F_pos := by
  simp [tCellAutomaton.L, LCellAutomaton.comp_empty_eq_uniform]
