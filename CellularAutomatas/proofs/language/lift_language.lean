import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

/-!
# Language lifting from α to Option α

Lifts languages and CAs from alphabet α to Option α, using a product CA with
a Q-track (simulating C) and a Bool-track (validating all symbols are `some _`).

Key results:
- `Language.lift`: { w.map some | w ∈ L }
- `liftCA`: product CA that simulates C on the Q-track and validates on the Bool-track
- `lift_mem_ca_rt`, `lift_mem_ca_2n`: lifting preserves membership in ℒ(CA_rt), ℒ(CA_2n)
- `unlift_mem_ca_rt`: projecting back from Option α to α
- `Language.lift_rev`: lifting commutes with reversal
-/

namespace CellularAutomatas

variable {α : Type} [Alphabet α]

/-! ## Language lifting -/

/-- Lift a language from α to Option α: { w.map some | w ∈ L }. -/
def Language.lift (L : Language α) : Language (Option α) :=
  { w | ∃ v ∈ L, w = v.map some }

omit [Alphabet α] in
/-- Lifting preserves membership. -/
lemma Language.mem_lift_iff (L : Language α) (w : Word (Option α)) :
    w ∈ (Language.lift L) ↔ ∃ v ∈ L, w = v.map some := Iff.rfl

/-- Lift a tCellAutomaton from α to Option α.
Product of:
- **Q-track**: simulates C, mapping `none` inputs to border (`C.embed none`).
- **Valid-track** (Bool): checks all input symbols are `some _`.
  Propagates right-to-left: `δ_valid(l, c, r) = c && r`.
  After n−1 steps at position 0, valid = ∧ᵢ (w[i] is some). -/
private def liftCA {schema : AcceptanceSchema} (C : tCellAutomaton schema α) : tCellAutomaton schema (Option α) where
  Q := C.Q × Bool
  δ l c r := (C.δ l.1 c.1 r.1, c.2 && r.2)
  embed x := match x with
    | none => (C.embed none, true)
    | some none => (C.embed none, false)
    | some (some a) => (C.embed (some a), true)
  project qv := C.project qv.1 && qv.2

omit [Alphabet α] in
/-- Initial config equality: the Q-component of liftCA's embedded config for `w.map some`
    equals C's embedded config for `w`. -/
private lemma liftCA_embed_Q_eq {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word α) (p : ℤ) :
    (⦋w.map some⦌ p : (liftCA C).Q).1 = (⦋w⦌ p : C.Q) := by
  simp only [CellAutomaton.embed_config, word_to_config, liftCA]
  split_ifs with h1 h2 h2
  · -- Both in range
    simp only [List.length_map] at h1
    have hp_lt : p.toNat < w.length := by omega
    simp only [List.getElem_map]
  · -- h1: in w.map some range, h2: NOT in w range — impossible
    simp only [List.length_map] at h1
    omega
  · -- h1: NOT in w.map some range, h2: in w range — impossible
    simp only [List.length_map] at h1
    omega
  · -- Both out of range
    rfl

omit [Alphabet α] in
/-- Helper: The Q-component of liftCA state equals C's state when inputs match.

At any time t and position p, if the input is `w.map some`, the Q-track of liftCA
evolves identically to C on `w`. -/
private lemma liftCA_Q_component {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word α) (t : ℕ) (p : ℤ) :
    ((liftCA C).toCellAutomaton.nextt ⦋w.map some⦌ t p).1 =
    C.toCellAutomaton.nextt ⦋w⦌ t p := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero]
    exact liftCA_embed_Q_eq C w p
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- After unfolding, liftCA's δ is (C.δ l.1 c.1 r.1, l.2 && c.2 && r.2)
    -- So the .1 projection gives C.δ l.1 c.1 r.1
    -- We need to show this equals C.δ (ih at p-1) (ih at p) (ih at p+1)
    show (C.δ ((liftCA C).toCellAutomaton.nextt ⦋w.map some⦌ t (p - 1)).1
              ((liftCA C).toCellAutomaton.nextt ⦋w.map some⦌ t p).1
              ((liftCA C).toCellAutomaton.nextt ⦋w.map some⦌ t (p + 1)).1)
       = C.δ (C.toCellAutomaton.nextt ⦋w⦌ t (p - 1))
             (C.toCellAutomaton.nextt ⦋w⦌ t p)
             (C.toCellAutomaton.nextt ⦋w⦌ t (p + 1))
    rw [ih (p - 1), ih p, ih (p + 1)]

omit [Alphabet α] in
/-- Initial Bool is true at all positions when input is `w.map some`. -/
private lemma liftCA_embed_Bool_true {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word α) (p : ℤ) :
    (⦋w.map some⦌ p : (liftCA C).Q).2 = true := by
  simp only [CellAutomaton.embed_config, word_to_config, liftCA]
  split_ifs with h
  · -- In range: some (some w[p]) → (_, true)
    simp only [List.length_map] at h
    simp only [List.getElem_map]
  · -- Out of range: none → (_, true)
    rfl

omit [Alphabet α] in
/-- δ of liftCA gives (C.δ on first components, c.2 && r.2). -/
private lemma liftCA_δ_snd {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (l c r : (liftCA C).Q) :
    ((liftCA C).δ l c r).2 = (c.2 && r.2) := rfl

omit [Alphabet α] in
/-- Bool stays true at all positions for all times when input is `w.map some`.
    Proof: δ_bool(l, c, r) = c && r. If all initial bools are true, conjunctions stay true. -/
private lemma liftCA_Bool_true_all {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word α) (t : ℕ) (p : ℤ) :
    ((liftCA C).toCellAutomaton.nextt ⦋w.map some⦌ t p).2 = true := by
  induction t generalizing p with
  | zero =>
    simp only [CellAutomaton.nextt_zero]
    exact liftCA_embed_Bool_true C w p
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    rw [liftCA_δ_snd, ih p, ih (p + 1)]
    rfl

omit [Alphabet α] in
/-- Helper: For w = v.map some, the Bool component at position 0 at time t is true
    (as long as t < v.length, the Bool track sees only `some (some _)` inputs). -/
private lemma liftCA_Bool_true_for_map_some {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (v : Word α) (t : ℕ) :
    ((liftCA C).toCellAutomaton.nextt ⦋v.map some⦌ t 0).2 = true :=
  liftCA_Bool_true_all C v t 0

omit [Alphabet α] in
/-- Initial Bool at position i is false when w[i] = none. -/
private lemma liftCA_embed_Bool_false_at_none {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word (Option α))
    (i : ℕ) (hi : i < w.length) (hn : w[i] = none) :
    (⦋w⦌ (i : ℤ) : (liftCA C).Q).2 = false := by
  simp only [CellAutomaton.embed_config, word_to_config]
  have h_range : (i : ℤ) ≥ 0 ∧ (i : ℤ) < w.length := by omega
  rw [dif_pos h_range]
  simp only [Int.toNat_natCast, hn, liftCA]

omit [Alphabet α] in
/-- If an initial Bool in range [p, p+t] is false, then Bool at position p at time t is false.
    This is because δ_bool(l, c, r) = c && r, so false propagates from right to left. -/
private lemma liftCA_Bool_false_propagates {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word (Option α))
    (t : ℕ) (p : ℤ) (j : ℕ) (hj : j ≤ t)
    (h_init_false : (⦋w⦌ (p + j) : (liftCA C).Q).2 = false) :
    ((liftCA C).toCellAutomaton.nextt ⦋w⦌ t p).2 = false := by
  induction t generalizing p j with
  | zero =>
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simp only [CellAutomaton.nextt_zero, Nat.cast_zero, add_zero] at h_init_false ⊢
    exact h_init_false
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next, liftCA_δ_snd]
    cases Nat.lt_or_eq_of_le hj with
    | inl hj_lt =>
      have hj' : j ≤ t := Nat.lt_succ_iff.mp hj_lt
      rw [ih p j hj' h_init_false, Bool.false_and]
    | inr hj_eq =>
      subst hj_eq
      have h_init' : (⦋w⦌ ((p + 1) + t) : (liftCA C).Q).2 = false := by
        simp only [Nat.cast_succ] at h_init_false
        convert h_init_false using 2
        ring
      rw [ih (p + 1) t (Nat.le_refl t) h_init', Bool.and_false]

omit [Alphabet α] in
/-- Helper: If w contains `none` at some position i (where i ≤ t),
    then the Bool component at position 0 at time t is false. -/
private lemma liftCA_Bool_false_for_none {schema : AcceptanceSchema} (C : tCellAutomaton schema α) (w : Word (Option α))
    (i : ℕ) (hi : i < w.length) (hn : w[i] = none) (ht : i ≤ t) :
    ((liftCA C).toCellAutomaton.nextt ⦋w⦌ t 0).2 = false := by
  apply liftCA_Bool_false_propagates C w t 0 i ht
  simp only [Int.zero_add]
  exact liftCA_embed_Bool_false_at_none C w i hi hn

omit [Alphabet α] in
/-- Given a list w : List (Option α) where all elements are `some _`,
    extract the underlying values and show w = result.map some. -/
private lemma all_some_eq_map_some (w : List (Option α))
    (h : ∀ i : ℕ, (hi : i < w.length) → ∃ a, w[i] = some a) :
    w = (w.filterMap id).map some := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, ha⟩ := h 0 (by simp [List.length_cons])
    simp only [List.getElem_cons_zero] at ha
    rw [List.filterMap_cons, ha]
    simp only [id, List.map_cons, List.cons.injEq, true_and]
    exact ih (fun i hi => h (i + 1) (by simp [List.length_cons]; omega))

/-- liftCA C has the same language as Language.lift C.L, provided:
- C.t n ≥ n - 1 (time covers all word positions)
- C.p n = 0 (checks position 0)

**Proof sketch:**
- **Forward:** If `(liftCA C).accepts w = true`, then the Bool component at position 0
  at time `t(n) ≥ n - 1` is true. By Bool propagation, all symbols `w[i]` must be `some _`.
  So `w = v.map some` for some `v`. The Q-track simulates C on `v`, so `C.accepts v = true`.
- **Backward:** If `w = v.map some` for `v ∈ C.L`, the Bool track stays true (all inputs
  are `some (some _)`), and the Q-track computes C on `v`. So `(liftCA C).accepts w = true`. -/
private lemma liftCA_L_eq_lift {schema : AcceptanceSchema} (C : tCellAutomaton schema α)
    (ht : ∀ n, schema.t n ≥ n - 1) (hp : ∀ n, schema.p n = 0) :
    (liftCA C).L = Language.lift C.L := by
  ext w
  constructor
  · -- (liftCA C).accepts w → ∃ v ∈ C.L, w = v.map some
    intro hw
    -- The Bool at position 0 at time C.t |w| ≥ |w| - 1 is true
    -- By contrapositive of liftCA_Bool_false_for_none: all w[i] ≠ none for i < |w|
    have h_all_some : ∀ i : ℕ, (hi : i < w.length) → ∃ a, w[i] = some a := by
      intro i hi
      by_contra h_none
      push_neg at h_none
      have h_is_none : w[i] = none := by
        cases hw' : w[i] with
        | none => rfl
        | some a => exact (h_none a hw').elim
      have h_covers : i ≤ schema.t w.length := by have := ht w.length; omega
      have h_bool_false := liftCA_Bool_false_for_none C w i hi h_is_none h_covers
      -- liftCA C accepts w means project qv = true where qv = nextt at (t, p)
      -- project qv = C.project qv.1 && qv.2
      -- h_bool_false says qv.2 = false at (t, 0)
      -- since p = 0 for liftCA, project = C.project (...).1 && false = false ≠ true
      have hp' : schema.p w.length = 0 := hp w.length
      -- Build the contradiction: (liftCA C).accepts w = false but hw says it's true
      have h_acc_false : (liftCA C).accepts w = false := by
        unfold tCellAutomaton.accepts
        unfold liftCA at h_bool_false ⊢
        simp only [CellAutomaton.comp_apply, Function.comp, CellAutomaton.project_config_apply, hp',
                   h_bool_false, Bool.and_false]
      have h_acc_true : (liftCA C).accepts w = true := hw
      rw [h_acc_false] at h_acc_true
      exact Bool.false_ne_true h_acc_true
    -- w = v.map some where v = w.filterMap id
    have h_w_eq := all_some_eq_map_some w h_all_some
    use w.filterMap id
    refine ⟨?_, h_w_eq⟩
    -- Show v ∈ C.L where v = w.filterMap id
    -- We have hw : w ∈ (liftCA C).L, and after rw [h_w_eq], hw is about v.map some
    rw [h_w_eq] at hw
    -- Now hw : (w.filterMap id).map some ∈ (liftCA C).L
    -- Goal: w.filterMap id ∈ C.L
    set v := w.filterMap id with hv_def
    -- Show that (liftCA C).accepts (v.map some) = C.accepts v
    have h_lift_eq : (liftCA C).accepts (v.map some) = C.accepts v := by
      unfold tCellAutomaton.accepts
      have hp' : schema.p v.length = 0 := hp v.length
      simp only [List.length_map, liftCA, CellAutomaton.comp_apply, Function.comp,
                 CellAutomaton.project_config, hp']
      have h_bool := liftCA_Bool_true_for_map_some C v (schema.t v.length)
      have h_q := liftCA_Q_component C v (schema.t v.length) (schema.p v.length)
      unfold liftCA at h_bool h_q
      simp only [hp'] at h_q
      simp only [h_q, h_bool, Bool.and_true]
    -- Now `hw : v.map some ∈ (liftCA C).L` i.e. `(liftCA C).accepts (v.map some) = true`
    -- And `h_lift_eq` says this equals `C.accepts v`
    have hw' : (liftCA C).accepts (v.map some) = true := hw
    rw [h_lift_eq] at hw'
    exact hw'
  · -- ∃ v ∈ C.L, w = v.map some → (liftCA C).accepts w
    rintro ⟨v, hv, rfl⟩
    -- Goal: v.map some ∈ (liftCA C).L, i.e. (liftCA C).accepts (v.map some) = true
    -- hv : v ∈ C.L, i.e. C.accepts v = true
    have h_lift_eq : (liftCA C).accepts (v.map some) = C.accepts v := by
      unfold tCellAutomaton.accepts
      have hp' : schema.p v.length = 0 := hp v.length
      simp only [List.length_map, liftCA, CellAutomaton.comp_apply, Function.comp,
                 CellAutomaton.project_config, hp']
      have h_bool := liftCA_Bool_true_for_map_some C v (schema.t v.length)
      have h_q := liftCA_Q_component C v (schema.t v.length) (schema.p v.length)
      unfold liftCA at h_bool h_q
      simp only [hp'] at h_q
      simp only [h_q, h_bool, Bool.and_true]
    show v.map some ∈ (liftCA C).L
    calc (liftCA C).accepts (v.map some)
        = C.accepts v := h_lift_eq
      _ = true := hv

/-- If L ∈ ℒ(CA_rt β), then (Language.lift L) ∈ ℒ(CA_rt (Option β)). -/
lemma lift_mem_ca_rt (L : Language α) (hL : L ∈ ℒ (CA_rt α)) :
    (Language.lift L) ∈ ℒ (CA_rt (Option α)) := by
  obtain ⟨C, hCL⟩ := hL
  refine ⟨liftCA C, ?_⟩
  subst hCL
  have ht : ∀ n, AcceptanceSchema.rt_center.t n ≥ n - 1 := fun n => by simp [AcceptanceSchema.rt_center]
  have hp : ∀ n, AcceptanceSchema.rt_center.p n = 0 := fun _ => rfl
  exact (liftCA_L_eq_lift C ht hp).symm

/-- If (Language.lift L) ∈ ℒ(CA_rt (Option β)), then L ∈ ℒ(CA_rt β).

Uses map_embed with f = some: (C.map_embed some).L = { w | w.map some ∈ C.L }.
Since C.L = lift(L) = { v.map some | v ∈ L }, membership reduces to
w.map some = v.map some for some v ∈ L, which by injectivity of some gives w = v. -/
lemma unlift_mem_ca_rt (L : Language α) (hL : (Language.lift L) ∈ ℒ (CA_rt (Option α))) :
    L ∈ ℒ (CA_rt α) := by
  obtain ⟨C, hCL⟩ := hL
  refine ⟨C.map_embed some, ?_⟩
  ext w
  show w ∈ L ↔ w ∈ (C.map_embed some).L
  rw [map_embed_L]
  -- Goal: w ∈ L ↔ w.map some ∈ C.L
  -- hCL : Language.lift L = C.L (modulo DefinesLanguage)
  have : w.map some ∈ C.L ↔ w.map some ∈ Language.lift L := by
    constructor <;> intro h
    · rw [hCL]; exact h
    · rw [hCL] at h; exact h
  rw [this]
  simp only [Language.lift]
  constructor
  · intro hw; exact ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, heq⟩
    exact List.map_injective_iff.mpr (Option.some_injective α) heq ▸ hv

/-- If L ∈ ℒ(CA_2n β), then (Language.lift L) ∈ ℒ(CA_2n (Option β)). -/
lemma lift_mem_ca_2n (L : Language α) (hL : L ∈ ℒ (CA_2n α)) :
    (Language.lift L) ∈ ℒ (CA_2n (Option α)) := by
  obtain ⟨C, hCL⟩ := hL
  refine ⟨liftCA C, ?_⟩
  subst hCL
  have ht : ∀ n, AcceptanceSchema.time_2n_center.t n ≥ n - 1 := fun n => by
    simp [AcceptanceSchema.time_2n_center]; omega
  have hp : ∀ n, AcceptanceSchema.time_2n_center.p n = 0 := fun _ => rfl
  exact (liftCA_L_eq_lift C ht hp).symm

omit [Alphabet α] in
/-- Lifting commutes with reversal: lift(L^R) = (lift L)^R -/
lemma Language.lift_rev (L : Language α) :
    Language.lift (Language.rev L) = Language.rev (Language.lift L) := by
  ext w
  simp only [Language.lift, Language.rev]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.reverse, hv, by simp [List.map_reverse]⟩
  · rintro ⟨v, hv, hrev⟩
    refine ⟨v.reverse, ?_, ?_⟩
    · show v.reverse.reverse ∈ L; simp [hv]
    · have : w = w.reverse.reverse := by simp
      rw [this, hrev]; simp [List.map_reverse]

end CellularAutomatas
