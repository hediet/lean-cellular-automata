import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.language.ca_rt_rev_eq_car_rt

/-!
# ℒ(CAr_rt) ⊆ ℒ(CA_2n)

This file proves that right-reading real-time CA languages are contained in 2n-time CA languages.

## Key idea

Given a CAr_rt CA that reads at position n-1 at time n-1, we construct a CA_2n CA that:
1. Runs the original CA in the first component
2. Shifts the result leftward in the second component

The second component propagates values from position n-1 toward position 0:
- At each time step, it copies from its right neighbor
- At the rightmost position (adjacent to border), it takes from the first component

After n-1 additional steps, the value at (t=n-1, p=n-1) arrives at position 0.
Total time: 2(n-1), reading at position 0.

## Construction

State: C.Q × C.Q × Bool
- First component: original CA state
- Second component: shifted state (propagating leftward)
- Bool: marker for "outer border" region (positions ≥ n)

Delta:
- If current cell is border: maintain border status
- If right neighbor is border: inject first component into second
- Otherwise: shift second component from right neighbor
-/

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [Alphabet α]

/-! ## The shift construction -/

/-- State for the shifted CA: (original, shifted, is_outer_border) -/
abbrev ShiftState (C : LCellAutomaton α) := C.Q × C.Q × Bool

/-- Build a CA_2n from a CAr_rt by adding a leftward-shifting second component. -/
def shiftCA (C : LCellAutomaton α) : LCellAutomaton α where
  Q := ShiftState C
  δ l c r :=
    let comp1' := C.δ l.1 c.1 r.1
    if c.2.2 then
      -- I am outer border: maintain border status
      (comp1', comp1', true)
    else if r.2.2 then
      -- Right is outer border: inject first component into second
      (comp1', comp1', false)
    else
      -- Interior: shift from right's second component
      (comp1', r.2.1, false)
  embed a :=
    match a with
    | none => (C.border, C.border, true)
    | some x => (C.inner x, C.inner x, false)
  project q := C.project q.2.1  -- Read from shifted component

instance (C : LCellAutomaton α) : Alphabet (ShiftState C) := inferInstance

/-- The timed version of shiftCA for CA_2n. -/
def shiftTCA (C : tCellAutomaton α) : tCellAutomaton α where
  toCellAutomaton := shiftCA C.toCellAutomaton
  t n := 2 * (n - 1)
  p _ := 0

/-! ## Helper definitions -/

/-- Extract the first component from shiftCA state. -/
def extractComp1 (C : LCellAutomaton α) (q : ShiftState C) : C.Q := q.1

/-- Extract the second component from shiftCA state. -/
def extractComp2 (C : LCellAutomaton α) (q : ShiftState C) : C.Q := q.2.1

/-- Extract the border flag from shiftCA state. -/
def extractFlag (C : LCellAutomaton α) (q : ShiftState C) : Bool := q.2.2

/-! ## Key shift invariant -/

omit [Alphabet α] in
/-- Helper: position p is in inner region (not border). -/
lemma shiftCA_inner_not_border (C : LCellAutomaton α) (w : Word α) (t : ℕ) (p : ℤ)
    (hp : 0 ≤ p) (hpt : p < w.length) :
    ((shiftCA C).nextt ⦋w⦌ t p).2.2 = false := by
  induction t with
  | zero =>
    -- At time 0, positions in range are initialized with border flag = false
    have h_in_range : p ∈ w.range := ⟨hp, hpt⟩
    simp only [nextt_zero]
    rw [embed_word_at_eq1 (C := shiftCA C) w p h_in_range]
    rfl
  | succ t ih =>
    -- At time t+1, delta preserves non-border flag when current cell is non-border
    simp only [nextt_succ, next]
    -- Unfold shiftCA to expose the if-then-else structure
    show (shiftCA C).δ _ ((shiftCA C).nextt ⦋w⦌ t p) _ |>.2.2 = false
    -- By IH, (nextt t p).2.2 = false, so let's substitute that
    have h_curr := ih
    simp only [shiftCA] at h_curr ⊢
    -- The delta checks c.2.2 = true first. Since c.2.2 = false (by IH), we go to else branch.
    -- The outer if condition is `c.2.2 = true` which simplifies via ih.
    simp only [h_curr, ↓reduceIte, Bool.false_eq_true]
    -- Now we have: (if r.2.2 = true then (_, _, false) else (_, _, false)).2.2
    split
    · rfl  -- true branch: (_, _, false).2.2 = false
    · rfl  -- false branch: (_, _, false).2.2 = false

omit [Alphabet α] in
/-- Helper: position p is outside the word (border region). -/
lemma shiftCA_outer_is_border (C : LCellAutomaton α) (w : Word α) (t : ℕ) (p : ℤ)
    (hp : p ∉ w.range) :
    ((shiftCA C).nextt ⦋w⦌ t p).2.2 = true := by
  induction t with
  | zero =>
    simp only [nextt_zero]
    rw [embed_word_at_eq2 (C := shiftCA C) w p hp]; rfl
  | succ t ih =>
    simp only [nextt_succ, next]
    show (shiftCA C).δ _ ((shiftCA C).nextt ⦋w⦌ t p) _ |>.2.2 = true
    -- The current cell has flag = true (by IH), so we hit the first branch "I am outer border"
    unfold shiftCA
    -- ih : ((shiftCA C).nextt ⦋w⦌ t p).2.2 = true
    -- The goal has form: (let comp1' := ... ; if c.2.2 = true then (comp1', comp1', true) else ...).2.2 = true
    -- Let's use dsimp to evaluate the let and then handle the if
    dsimp only
    split
    · -- true branch: result is (_, _, true).2.2 = true ✔
      rfl
    · -- false branch: this contradicts ih
      next h_false => exact absurd ih h_false

omit [Alphabet α] in
/-- Helper: at position n-1, comp2 equals comp1 (at all times). -/
lemma shiftCA_comp2_eq_comp1_at_boundary (C : LCellAutomaton α) (w : Word α) (t : ℕ)
    (hw : w.length ≥ 1) :
    extractComp2 C ((shiftCA C).nextt ⦋w⦌ t (w.length - 1)) =
    extractComp1 C ((shiftCA C).nextt ⦋w⦌ t (w.length - 1)) := by
  induction t with
  | zero =>
    -- At time 0, embed (some x) = (C.inner x, C.inner x, false)
    -- So .2.1 = .1
    unfold extractComp1 extractComp2
    simp only [nextt_zero, CellAutomaton.embed_config, shiftCA]
    -- Need to show that for any a : Option α,
    -- (match a with | none => (C.border, C.border, true) | some x => (C.inner x, C.inner x, false)).2.1 =
    -- (match a with | none => (C.border, C.border, true) | some x => (C.inner x, C.inner x, false)).1
    split
    · rfl  -- none case: C.border = C.border
    · rfl  -- some case: C.inner x = C.inner x
  | succ t ih =>
    -- At position n-1, right neighbor is border, so comp2 := comp1
    -- The right neighbor ((↑(w.length - 1) + 1)) has border flag = true
    -- So the delta function takes the branch: (comp1', comp1', false)
    -- Hence .2.1 = .1 = comp1'
    -- Note: ↑(w.length - 1) = (↑w.length - 1 : ℤ) when w.length ≥ 1
    have hp : (↑(w.length - 1) : ℤ) = ↑w.length - 1 := by omega
    have h1 : ((shiftCA C).nextt ⦋w⦌ t (↑w.length - 1)).2.2 = false := by
      rw [← hp]
      exact shiftCA_inner_not_border C w t (↑(w.length - 1)) (by omega) (by omega)
    have h_right_border : (↑w.length - 1 : ℤ) + 1 ∉ w.range := by
      simp only [Word.range, Set.mem_setOf_eq, not_and, not_lt]; intro _; omega
    have h2 : ((shiftCA C).nextt ⦋w⦌ t ((↑w.length - 1) + 1)).2.2 = true :=
      shiftCA_outer_is_border C w t ((↑w.length - 1 : ℤ) + 1) h_right_border
    unfold extractComp1 extractComp2
    simp only [nextt_succ, next]
    -- Goal: ((shiftCA C).δ l c r).2.1 = ((shiftCA C).δ l c r).1
    -- where c.2.2 = false and r.2.2 = true
    show ((shiftCA C).δ _ _ _).2.1 = ((shiftCA C).δ _ _ _).1
    generalize hl : (shiftCA C).nextt ⦋w⦌ t ((↑w.length - 1) - 1) = l
    generalize hr : (shiftCA C).nextt ⦋w⦌ t ((↑w.length - 1) + 1) = r
    generalize hc : (shiftCA C).nextt ⦋w⦌ t (↑w.length - 1) = c
    have hc' : c.2.2 = false := by rw [← hc]; exact h1
    have hr' : r.2.2 = true := by rw [← hr]; exact h2
    simp only [shiftCA, hc', hr', Bool.false_eq_true, ↓reduceIte]

omit [Alphabet α] in
/-- Helper: extractComp1 commutes with shiftCA's delta. -/
lemma shiftCA_delta_comp1 (C : LCellAutomaton α) (l c r : ShiftState C) :
    extractComp1 C ((shiftCA C).δ l c r) = C.δ (extractComp1 C l) (extractComp1 C c) (extractComp1 C r) := by
  unfold extractComp1 shiftCA
  dsimp only
  split
  · rfl
  · split <;> rfl

omit [Alphabet α] in
/-- Helper: extractComp1 commutes with shiftCA's embed. -/
lemma shiftCA_embed_comp1 (C : LCellAutomaton α) (a : Option α) :
    extractComp1 C ((shiftCA C).embed a) = C.embed a := by
  cases a <;> rfl

omit [Alphabet α] in
/-- Helper: extractComp1 of shiftCA equals C at all positions (including out-of-bounds). -/
lemma shiftCA_comp1_eq_C_general (C : LCellAutomaton α) (w : Word α) (t : ℕ) (p : ℤ) :
    extractComp1 C ((shiftCA C).nextt ⦋w⦌ t p) = C.nextt ⦋w⦌ t p := by
  induction t generalizing p with
  | zero =>
    unfold extractComp1
    simp only [nextt_zero, CellAutomaton.embed_config]
    change extractComp1 C ((shiftCA C).embed (word_to_config w p)) = C.embed (word_to_config w p)
    rw [shiftCA_embed_comp1]
  | succ t ih =>
    simp only [nextt_succ, next, shiftCA_delta_comp1]
    congr 1 <;> exact ih _

omit [Alphabet α] in
/-- Helper: comp1 tracks C's state at all positions. -/
lemma shiftCA_comp1_eq_C (C : LCellAutomaton α) (w : Word α) (t : ℕ) (p : ℤ)
    (_hp : 0 ≤ p) (_hpt : p < w.length) :
    extractComp1 C ((shiftCA C).nextt ⦋w⦌ t p) = C.nextt ⦋w⦌ t p :=
  shiftCA_comp1_eq_C_general C w t p

omit [Alphabet α] in
/-- Helper: comp1 at position n-1 tracks C's state there. -/
lemma shiftCA_comp1_eq_C_at_boundary (C : LCellAutomaton α) (w : Word α) (t : ℕ)
    (hw : w.length ≥ 1) :
    extractComp1 C ((shiftCA C).nextt ⦋w⦌ t (w.length - 1)) =
    C.nextt ⦋w⦌ t (w.length - 1) :=
  shiftCA_comp1_eq_C C w t (w.length - 1) (by omega) (by omega)

omit [Alphabet α] in
/-- The shift invariant: at time t ≥ n-1-p, position p, the second component equals
    the first component at time t-(n-1-p), position n-1.

This captures the essence of the construction: the value from position n-1
propagates leftward at speed 1. After n-1-p steps, it reaches position p.
-/
lemma shiftCA_shift_invariant (C : LCellAutomaton α) (w : Word α) (t : ℕ) (p : ℤ)
    (hw : w.length ≥ 1) (hp : 0 ≤ p) (hpt : p < w.length)
    (ht : t ≥ w.length - 1 - p.toNat) :
    extractComp2 C ((shiftCA C).nextt ⦋w⦌ t p) =
    C.nextt ⦋w⦌ (t - (w.length - 1 - p.toNat)) (w.length - 1) := by
  -- Prove by induction on distance d = (n-1) - p
  obtain ⟨d, hd⟩ : ∃ d, w.length - 1 - p.toNat = d := ⟨_, rfl⟩
  induction d generalizing t p with
  | zero =>
    -- d = 0 means p.toNat = w.length - 1, so p = ↑(w.length - 1)
    -- At this position, comp2 = comp1 = C by the boundary lemmas
    have hp' : p = ↑(w.length - 1) := by omega
    rw [hd, Nat.sub_zero, hp']
    -- Now goal: extractComp2 C ((shiftCA C).nextt ⦋w⦌ t ↑(w.length - 1)) = C.nextt ⦋w⦌ t ↑(w.length - 1)
    -- Both lemmas use (w.length - 1 : ℕ) which coerces to ℤ
    have h1 : extractComp2 C ((shiftCA C).nextt ⦋w⦌ t (w.length - 1)) =
              extractComp1 C ((shiftCA C).nextt ⦋w⦌ t (w.length - 1)) :=
      shiftCA_comp2_eq_comp1_at_boundary C w t hw
    have h2 : extractComp1 C ((shiftCA C).nextt ⦋w⦌ t (w.length - 1)) =
              C.nextt ⦋w⦌ t (w.length - 1) :=
      shiftCA_comp1_eq_C_at_boundary C w t hw
    -- The coercion ↑(w.length - 1) should be equal to (w.length - 1 : ℕ) coerced
    simp only [Nat.cast_sub (by omega : 1 ≤ w.length), Nat.cast_one] at h1 h2 ⊢
    exact h1.trans h2
  | succ d ih =>
    -- d > 0, so p < n-1; comp2 at p comes from right neighbor at t-1
    -- Key: at interior position p, delta gives comp2' = r.2.1 (shift from right)
    -- So comp2 at (t, p) = comp2 at (t-1, p+1)
    -- By IH at (t-1, p+1), this equals C.nextt at (t-1-d, n-1) = C.nextt at (t-(d+1), n-1)

    -- First establish that p+1 is also in the interior (distance d from boundary)
    have hp1_dist : w.length - 1 - (p + 1).toNat = d := by omega

    -- We have t ≥ d+1, so t ≥ 1 and t-1 ≥ d
    have ht_pos : t ≥ 1 := by omega
    have ht' : t - 1 ≥ d := by omega

    -- p+1 is in range since p < n-1 implies p+1 < n
    have hp1_pos : 0 ≤ p + 1 := by omega
    have hp1_lt : p + 1 < w.length := by omega

    -- Apply IH at (t-1, p+1)
    have ht'_alt : t - 1 ≥ w.length - 1 - (p + 1).toNat := by omega
    have ih_app := ih (t - 1) (p + 1) hp1_pos hp1_lt ht'_alt hp1_dist

    -- Now show comp2 at (t, p) = comp2 at (t-1, p+1)
    -- This follows from the delta function taking the "interior shift" branch
    have h_curr : ((shiftCA C).nextt ⦋w⦌ (t - 1) p).2.2 = false :=
      shiftCA_inner_not_border C w (t - 1) p hp hpt
    have h_right : ((shiftCA C).nextt ⦋w⦌ (t - 1) (p + 1)).2.2 = false :=
      shiftCA_inner_not_border C w (t - 1) (p + 1) hp1_pos hp1_lt

    -- Unfold to expose the delta
    unfold extractComp2
    conv_lhs =>
      rw [show t = t - 1 + 1 by omega]
      simp only [nextt_succ, next]
    show ((shiftCA C).δ _ _ _).2.1 = _

    -- Generalize the neighbors
    generalize hl : (shiftCA C).nextt ⦋w⦌ (t - 1) (p - 1) = l
    generalize hr : (shiftCA C).nextt ⦋w⦌ (t - 1) (p + 1) = r
    generalize hc : (shiftCA C).nextt ⦋w⦌ (t - 1) p = c
    have hc' : c.2.2 = false := by rw [← hc]; exact h_curr
    have hr' : r.2.2 = false := by rw [← hr]; exact h_right

    -- Delta takes the third branch: (comp1', r.2.1, false)
    simp only [shiftCA, hc', hr', Bool.false_eq_true, ↓reduceIte]
    -- Goal: r.2.1 = C.nextt ⦋w⦌ (t - (d + 1)) (↑(w.length - 1))
    -- r = (shiftCA C).nextt ⦋w⦌ (t - 1) (p + 1), so r.2.1 = extractComp2 at (t-1, p+1)
    rw [← hr]
    -- ih_app: extractComp2 C ((shiftCA C).nextt ⦋w⦌ (t - 1) (p + 1)) = C.nextt ⦋w⦌ (t - 1 - d) (↑(w.length - 1))
    -- Goal: ((shiftCA C).nextt ⦋w⦌ (t - 1) (p + 1)).2.1 = ... which is extractComp2
    show extractComp2 C ((shiftCA C).nextt ⦋w⦌ (t - 1) (p + 1)) = _
    rw [ih_app]
    -- t - (d + 1) = t - 1 - d
    congr 1
    omega

omit [Alphabet α] in
/-- The main acceptance equivalence:
    At time 2(n-1), position 0, the shiftCA's second component equals
    the original CA's state at time n-1, position n-1. -/
lemma shiftCA_accepts_eq (C : LCellAutomaton α) (w : Word α) (hw : w.length ≥ 1) :
    (shiftCA C).comp w (2 * (w.length - 1)) 0 = C.comp w (w.length - 1) (w.length - 1) := by
  -- This follows from shiftCA_shift_invariant at t = 2(n-1), p = 0
  have h := shiftCA_shift_invariant C w (2 * (w.length - 1)) 0 hw (by omega) (by omega) (by omega)
  simp only [Int.toNat_zero, Nat.sub_zero] at h
  have h_time : 2 * (w.length - 1) - (w.length - 1) = w.length - 1 := by omega
  simp only [h_time] at h
  -- h : extractComp2 C ((shiftCA C).nextt ⦋w⦌ (2*(n-1)) 0) = C.nextt ⦋w⦌ (n-1) (n-1)
  -- Use congrArg with C.project to get the desired equality
  have h' : C.project (extractComp2 C ((shiftCA C).nextt ⦋w⦌ (2 * (w.length - 1)) 0)) =
            C.project (C.nextt ⦋w⦌ (w.length - 1) (w.length - 1)) := congrArg C.project h
  -- comp = project ∘ nextt
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold]
  simp only [shiftCA, extractComp2] at h'
  exact h'

/-! ## Main theorems -/

/-- The shiftTCA is in CA_2n. -/
lemma shiftTCA_in_CA_2n (C : tCellAutomaton α) (_hC : C ∈ CAr_rt α) :
    shiftTCA C ∈ CA_2n α := by
  simp only [CA_2n, t_2n, CA, tCellAutomata,
             Set.mem_setOf_eq, Set.mem_univ, true_and]
  constructor
  · rfl
  · intro n; rfl

/-- The language of shiftTCA equals the language of C. -/
theorem shiftTCA_L_eq (C : tCellAutomaton α) (hC : C ∈ CAr_rt α) :
    (shiftTCA C).L = C.L := by
  ext w
  simp only [tCellAutomaton.L]
  unfold tCellAutomaton.accepts shiftTCA
  -- Get the time and position functions from CAr_rt
  have h_t : C.t w.length = w.length - 1 := hC.2 w.length
  have h_p : C.p w.length = ↑w.length - 1 := by
    simp only [CAr_rt, t_rt, tCellAutomata, Set.mem_setOf_eq] at hC
    have h := congr_fun hC.1.2 w.length
    omega
  -- The goal reduces to comparing comp at shifted coordinates
  -- shiftTCA reads at (t=2(n-1), p=0), C reads at (t=n-1, p=n-1)
  -- By shiftCA_accepts_eq, these are equal for non-empty words
  show (shiftCA C.toCellAutomaton).comp w (2 * (w.length - 1)) 0 = true ↔
       C.comp w (C.t w.length) (C.p w.length) = true
  rw [h_t, h_p]
  by_cases hw : w.length = 0
  · -- Empty word case: both sides project C.border
    -- For empty word, time and position are both 0 (or 0 - 1 = -1)
    have hw' : w = [] := List.eq_nil_of_length_eq_zero hw
    subst hw'
    -- comp [] 0 p = project (nextt ⦋[]⦌ 0 p) = project (embed_config [] p) = project (embed none)
    -- For shiftCA: project = C.project ∘ (·.2.1), and embed none = (C.border, C.border, true)
    -- So (shiftCA C).project ((shiftCA C).embed none) = C.project C.border
    -- For C: project C.border
    -- Both equal C.project C.border
    simp only [List.length_nil, Nat.zero_sub, Nat.mul_zero, Int.ofNat_zero,
               CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold,
               shiftCA, CellAutomaton.border]
    -- After simp, both sides should be C.project C.border = true ↔ C.project C.border = true
    rfl
  · -- Non-empty word case: use shiftCA_accepts_eq
    have hw' : w.length ≥ 1 := Nat.one_le_iff_ne_zero.mpr hw
    rw [shiftCA_accepts_eq C.toCellAutomaton w hw']

/-- ℒ(CAr_rt) ⊆ ℒ(CA_2n): Right-reading RT languages are contained in 2n-time languages. -/
theorem car_rt_subset_ca_2n : ℒ (CAr_rt α) ⊆ ℒ (CA_2n α) := by
  intro L hL
  obtain ⟨C, hC, hCL⟩ := hL
  use shiftTCA C
  constructor
  · exact shiftTCA_in_CA_2n C hC
  · calc L = C.L := hCL
      _ = (shiftTCA C).L := (shiftTCA_L_eq C hC).symm

end CellularAutomatas
