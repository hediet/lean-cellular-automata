import CellularAutomatas.proofs.advice_theory.marked_prefix.async_driven

namespace CellularAutomatas.AsyncHalfLine.FiniteStrip

open CellAutomaton

/-- A finite-strip cell may advance when every neighbor inside the strip is
at least as high.  The two missing neighbors are literal dead states. -/
def ready (M : ℕ) (g : ℕ → ℕ) (p : ℕ) : Prop :=
  (p = 0 ∨ g p ≤ g (p - 1)) ∧
    (p + 1 = M ∨ g p ≤ g (p + 1))

instance (M : ℕ) (g : ℕ → ℕ) (p : ℕ) : Decidable (ready M g p) :=
  inferInstanceAs (Decidable ((_ ∨ _) ∧ (_ ∨ _)))

def tick (M : ℕ) (release : Bool) (g : ℕ → ℕ) (p : ℕ) : ℕ :=
  if g p = 0 then
    if release then 1 else 0
  else if ready M g p then g p + 1 else g p

/-- Height zero means uninitialized; height `k+1` means generation `k`. -/
def height (M : ℕ) (R : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, p => if R p = 0 then 1 else 0
  | t + 1, p => tick M (decide (t + 1 = R p)) (height M R t) p

lemma tick_bounds (M : ℕ) (release : Bool) (g : ℕ → ℕ) (p : ℕ) :
    g p ≤ tick M release g p ∧ tick M release g p ≤ g p + 1 := by
  unfold tick
  split
  · split <;> omega
  · split <;> omega

lemma tick_increases (M : ℕ) (release : Bool) (g : ℕ → ℕ) (p : ℕ)
    (h : g p < tick M release g p) :
    g p = 0 ∨ ready M g p := by
  unfold tick at h
  split at h
  · exact Or.inl ‹g p = 0›
  · right
    split at h
    · assumption
    · omega

/-- Adjacent cells inside the strip always have heights differing by at most
one.  No assertion is made across either dead boundary. -/
lemma height_skew (M : ℕ) (R : ℕ → ℕ) (t p : ℕ) (hp : p + 1 < M) :
    height M R t p ≤ height M R t (p + 1) + 1 ∧
    height M R t (p + 1) ≤ height M R t p + 1 := by
  induction t generalizing p with
  | zero =>
    simp only [height]
    split <;> split <;> omega
  | succ t ih =>
    apply AsyncHalfLine.edge_preserved
      (ih p hp) (tick_bounds M _ _ p) (tick_bounds M _ _ (p + 1))
    · intro h
      rcases tick_increases M _ _ p h with hz | hr
      · omega
      · rcases hr.2 with hboundary | hedge
        · omega
        · exact hedge
    · intro h
      rcases tick_increases M _ _ (p + 1) h with hz | hr
      · omega
      · rcases hr.1 with hboundary | hedge
        · omega
        · simpa only [Nat.add_sub_cancel] using hedge

lemma height_zero_iff (M : ℕ) (R : ℕ → ℕ) (t p : ℕ) :
    height M R t p = 0 ↔ t < R p := by
  induction t with
  | zero => simp [height]
  | succ t ih =>
    simp only [height, tick]
    split
    · rename_i hz
      have ht := ih.mp hz
      simp only [decide_eq_true_eq]
      split <;> omega
    · rename_i hz
      have ht : R p ≤ t := by omega
      split <;> omega

lemma height_eq_zero_of_lt (M : ℕ) (R : ℕ → ℕ) (t p : ℕ)
    (hbefore : t < R p) :
    height M R t p = 0 :=
  (height_zero_iff M R t p).mpr hbefore

lemma height_le_succ (M : ℕ) (R : ℕ → ℕ) (t p : ℕ) :
    height M R t p ≤ height M R (t + 1) p := by
  rw [height]
  exact (tick_bounds M _ _ p).1

/-- A strip cell's ghost height is monotone in physical time. -/
theorem height_mono_time (M : ℕ) (R : ℕ → ℕ) (p : ℕ) :
    Monotone (fun t => height M R t p) := by
  intro t u htu
  induction u with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    exact le_rfl
  | succ u ih =>
    by_cases heq : t = u + 1
    · subst t
      exact le_rfl
    · exact le_trans (ih (by omega)) (height_le_succ M R u p)

lemma height_at_release (M : ℕ) (R : ℕ → ℕ) (p : ℕ) :
    height M R (R p) p = 1 := by
  cases hr : R p with
  | zero => simp [height, hr]
  | succ t =>
    have hz : height M R t p = 0 :=
      (height_zero_iff M R t p).mpr (by omega)
    simp [height, tick, hz, hr]

/-- Threshold form of the finite-strip update.  Local skew is needed only for
neighbors that are actually in the strip. -/
lemma tick_level_iff (M : ℕ) (release : Bool) (g : ℕ → ℕ) (p k : ℕ)
    (hleft : p ≠ 0 → g p ≤ g (p - 1) + 1)
    (hright : p + 1 ≠ M → g p ≤ g (p + 1) + 1) :
    k + 2 ≤ tick M release g p ↔
      k + 1 ≤ g p ∧
      (p = 0 ∨ k + 1 ≤ g (p - 1)) ∧
      (p + 1 = M ∨ k + 1 ≤ g (p + 1)) := by
  unfold tick
  split
  · split <;> omega
  · split
    · rename_i hready
      rcases hready with ⟨hl, hr⟩
      constructor
      · intro h
        refine ⟨by omega, ?_, ?_⟩
        · rcases hl with hp | hl
          · exact Or.inl hp
          · exact Or.inr (by omega)
        · rcases hr with hp | hr
          · exact Or.inl hp
          · exact Or.inr (by omega)
      · intro h
        omega
    · rename_i hready
      constructor
      · intro h
        refine ⟨by omega, ?_, ?_⟩
        · by_cases hp : p = 0
          · exact Or.inl hp
          · exact Or.inr (by have := hleft hp; omega)
        · by_cases hp : p + 1 = M
          · exact Or.inl hp
          · exact Or.inr (by have := hright hp; omega)
      · rintro ⟨hc, hl, hr⟩
        by_contra h
        have heq : g p = k + 1 := by omega
        apply hready
        constructor
        · rcases hl with hp | hl
          · exact Or.inl hp
          · exact Or.inr (by simpa only [heq] using hl)
        · rcases hr with hp | hr
          · exact Or.inl hp
          · exact Or.inr (by simpa only [heq] using hr)

/-- Once all releases in a nonempty finite strip have happened by `T`, every
cell completes one further simulated generation per physical tick. -/
theorem height_uniform_completion (M : ℕ) (R : ℕ → ℕ) (T k p : ℕ)
    (hp : p < M) (hrelease : ∀ q, q < M → R q ≤ T) :
    k + 1 ≤ height M R (T + k) p := by
  induction k generalizing p with
  | zero =>
    have hnonzero : height M R T p ≠ 0 := by
      intro hz
      have hbefore := (height_zero_iff M R T p).mp hz
      exact (Nat.not_lt_of_ge (hrelease p hp)) hbefore
    exact Nat.one_le_iff_ne_zero.mpr hnonzero
  | succ k ih =>
    have hleft :
        p ≠ 0 →
          height M R (T + k) p ≤ height M R (T + k) (p - 1) + 1 := by
      intro hzero
      have hskew := (height_skew M R (T + k) (p - 1) (by omega)).2
      simpa only [show p - 1 + 1 = p from by omega] using hskew
    have hright :
        p + 1 ≠ M →
          height M R (T + k) p ≤ height M R (T + k) (p + 1) + 1 := by
      intro hboundary
      have hle : p + 1 ≤ M := Nat.succ_le_iff.mpr hp
      exact (height_skew M R (T + k) p
        (Nat.lt_of_le_of_ne hle hboundary)).1
    rw [show T + (k + 1) = (T + k) + 1 by omega, height,
      tick_level_iff M _ _ p k hleft hright]
    refine ⟨ih p hp, ?_, ?_⟩
    · by_cases hzero : p = 0
      · exact Or.inl hzero
      · exact Or.inr (ih (p - 1) (by omega))
    · by_cases hboundary : p + 1 = M
      · exact Or.inl hboundary
      · exact Or.inr (ih (p + 1) (by omega))

abbrev State (Q : Type) := AsyncHalfLine.State Q

def readBoundary {Q : Type} (dead : Q) (boundary : Bool)
    (k : Fin 3) (state : State Q) : Option Q :=
  if boundary then some dead else AsyncHalfLine.read k state

/-- Both boundary bits are part of the finite transition.  They are consulted
only after initialization, so a packet at time zero is embedded directly. -/
def step {Q : Type} (δ : Q → Q → Q → Q) (dead : Q)
    (atLeft atRight : Bool) (packet : Option Q)
    (left center right : State Q) : State Q :=
  match center with
  | none => packet.map (fun q => (0, q, q))
  | some (k, current, _) =>
    match readBoundary dead atLeft k left,
        readBoundary dead atRight k right with
    | some l, some r => some (k + 1, δ l current r, current)
    | _, _ => center

lemma step_left_independent {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (atRight : Bool) (packet : Option Q)
    (left left' center right : State Q) :
    step δ dead true atRight packet left center right =
      step δ dead true atRight packet left' center right := by
  cases center with
  | none => rfl
  | some state =>
    rcases state with ⟨k, current, previous⟩
    rfl

lemma step_right_independent {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (atLeft : Bool) (packet : Option Q)
    (left center right right' : State Q) :
    step δ dead atLeft true packet left center right =
      step δ dead atLeft true packet left center right' := by
  cases center with
  | none => rfl
  | some state =>
    rcases state with ⟨k, current, previous⟩
    cases atLeft <;> rfl

lemma step_congr_boundaries {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (atLeft atRight : Bool) (packet : Option Q)
    (left center right left' center' right' : State Q)
    (hcenter : center = center')
    (hleft : atLeft = false → left = left')
    (hright : atRight = false → right = right') :
    step δ dead atLeft atRight packet left center right =
      step δ dead atLeft atRight packet left' center' right' := by
  subst center'
  cases atLeft <;> cases atRight <;> simp_all [step, readBoundary]

lemma step_encode_active {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (atLeft atRight : Bool) (packet : Option Q)
    (x xleft xright : ℕ → Q) {centerHeight leftHeight rightHeight : ℕ}
    (hcenter : 0 < centerHeight)
    (hleft : atLeft = false →
      centerHeight ≤ leftHeight + 1 ∧ leftHeight ≤ centerHeight + 1)
    (hright : atRight = false →
      centerHeight ≤ rightHeight + 1 ∧ rightHeight ≤ centerHeight + 1)
    (hnext : ∀ generation,
      x (generation + 1) =
        δ (if atLeft then dead else xleft generation) (x generation)
          (if atRight then dead else xright generation)) :
    step δ dead atLeft atRight packet
        (AsyncHalfLine.encode leftHeight xleft)
        (AsyncHalfLine.encode centerHeight x)
        (AsyncHalfLine.encode rightHeight xright) =
      AsyncHalfLine.encode
        (if (atLeft = true ∨ centerHeight ≤ leftHeight) ∧
            (atRight = true ∨ centerHeight ≤ rightHeight)
          then centerHeight + 1 else centerHeight) x := by
  have hencoded :
      AsyncHalfLine.encode centerHeight x =
        some (AsyncHalfLine.tag (centerHeight - 1),
          x (centerHeight - 1), x (centerHeight - 2)) := by
    simp only [AsyncHalfLine.encode, Nat.ne_of_gt hcenter, ↓reduceIte]
  have hone : centerHeight - 1 + 1 = centerHeight := by omega
  have hnext' := hnext (centerHeight - 1)
  rw [hone] at hnext'
  cases atLeft <;> cases atRight
  · simp only [Bool.false_eq_true, false_or, Bool.false_eq_true,
      ↓reduceIte] at hnext' ⊢
    rw [hencoded]
    simp only [step, readBoundary]
    rw [AsyncHalfLine.read_encode xleft hcenter (hleft rfl),
      AsyncHalfLine.read_encode xright hcenter (hright rfl)]
    by_cases hl : centerHeight ≤ leftHeight <;>
      by_cases hr : centerHeight ≤ rightHeight
    · simp [hl, hr, AsyncHalfLine.encode_succ hcenter, hnext']
    · simp [hl, hr, hencoded]
    · simp [hl, hr, hencoded]
    · simp [hl, hr, hencoded]
  · simp only [Bool.false_eq_true, false_or, true_or,
      and_true, ↓reduceIte] at hnext' ⊢
    rw [hencoded]
    simp only [step, readBoundary, ↓reduceIte]
    rw [AsyncHalfLine.read_encode xleft hcenter (hleft rfl)]
    by_cases hl : centerHeight ≤ leftHeight
    · simp [hl, AsyncHalfLine.encode_succ hcenter, hnext']
    · simp [hl, hencoded]
  · simp only [true_or, Bool.false_eq_true, false_or,
      true_and, ↓reduceIte] at hnext' ⊢
    rw [hencoded]
    simp only [step, readBoundary, ↓reduceIte]
    rw [AsyncHalfLine.read_encode xright hcenter (hright rfl)]
    by_cases hr : centerHeight ≤ rightHeight
    · simp [hr, AsyncHalfLine.encode_succ hcenter, hnext']
    · simp [hr, hencoded]
  · simp only [true_or, and_self, ↓reduceIte] at hnext' ⊢
    rw [hencoded]
    simp only [step, readBoundary]
    rw [AsyncHalfLine.encode_succ hcenter, hnext']
    simp

/-- Synchronous evolution on positions `p < M`, with literal dead states on
both missing-neighbor branches. -/
def synchronous {Q : Type} (δ : Q → Q → Q → Q) (dead : Q)
    (M : ℕ) (input : ℕ → Q) : ℕ → ℕ → Q
  | 0, p => input p
  | generation + 1, p =>
      δ (if p = 0 then dead
          else synchronous δ dead M input generation (p - 1))
        (synchronous δ dead M input generation p)
        (if p + 1 = M then dead
          else synchronous δ dead M input generation (p + 1))

abbrev packet {Q : Type} :=
  @AsyncHalfLine.packet Q

/-- The right recursive argument is clamped at the boundary.  Its value is
ignored there, but clamping keeps this specification entirely on `p < M`. -/
def run {Q : Type} (δ : Q → Q → Q → Q) (dead : Q)
    (M : ℕ) (R : ℕ → ℕ) (input : ℕ → Q) : ℕ → ℕ → State Q
  | 0, p => (packet R input 0 p).map (fun q => (0, q, q))
  | t + 1, p =>
      step δ dead (decide (p = 0)) (decide (p + 1 = M))
        (packet R input (t + 1) p)
        (run δ dead M R input t (p - 1))
        (run δ dead M R input t p)
        (run δ dead M R input t (if p + 1 = M then p else p + 1))

lemma run_before_release {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (M : ℕ) (R : ℕ → ℕ) (input : ℕ → Q) (t p : ℕ)
    (ht : t < R p) :
    run δ dead M R input t p = none := by
  induction t with
  | zero =>
    simp only [run, packet, AsyncHalfLine.packet,
      if_neg (by omega : ¬0 = R p), Option.map_none]
  | succ t ih =>
    rw [run, ih (by omega)]
    simp only [step, packet, AsyncHalfLine.packet,
      if_neg (by omega : ¬t + 1 = R p), Option.map_none]

/-- The finite-state run stores exactly the synchronous current and previous
generations selected by its ghost height. -/
theorem run_encode {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (M : ℕ) (R : ℕ → ℕ) (input : ℕ → Q) (t p : ℕ) (hp : p < M) :
    run δ dead M R input t p =
      AsyncHalfLine.encode (height M R t p)
        (fun generation => synchronous δ dead M input generation p) := by
  induction t generalizing p with
  | zero =>
    by_cases hrelease : R p = 0
    · simp [run, packet, AsyncHalfLine.packet, height,
        AsyncHalfLine.encode, synchronous, AsyncHalfLine.tag, hrelease]
    · simp [run, packet, AsyncHalfLine.packet, height,
        AsyncHalfLine.encode, hrelease, Ne.symm hrelease]
  | succ t ih =>
    let rightPosition := if p + 1 = M then p else p + 1
    have hrightPosition : rightPosition < M := by
      unfold rightPosition
      split <;> omega
    rw [run, ih (p - 1) (by omega), ih p hp, ih rightPosition hrightPosition]
    change step δ dead (decide (p = 0)) (decide (p + 1 = M))
      (packet R input (t + 1) p)
      (AsyncHalfLine.encode (height M R t (p - 1))
        (fun generation => synchronous δ dead M input generation (p - 1)))
      (AsyncHalfLine.encode (height M R t p)
        (fun generation => synchronous δ dead M input generation p))
      (AsyncHalfLine.encode (height M R t rightPosition)
        (fun generation => synchronous δ dead M input generation rightPosition)) = _
    by_cases hzero : height M R t p = 0
    · by_cases hrelease : t + 1 = R p
      · simp [AsyncHalfLine.encode, hzero, step, packet,
          AsyncHalfLine.packet, hrelease, height, tick,
          synchronous, AsyncHalfLine.tag]
      · simp [AsyncHalfLine.encode, hzero, step, packet,
          AsyncHalfLine.packet, hrelease, height, tick]
    · have hpositive : 0 < height M R t p := Nat.pos_of_ne_zero hzero
      have hleft :
          decide (p = 0) = false →
            height M R t p ≤ height M R t (p - 1) + 1 ∧
            height M R t (p - 1) ≤ height M R t p + 1 := by
        intro hflag
        have hpzero : p ≠ 0 := by
          intro hpzero
          subst p
          simp at hflag
        have hskew := height_skew M R t (p - 1) (by omega)
        simpa only [show p - 1 + 1 = p from by omega] using hskew.symm
      have hright :
          decide (p + 1 = M) = false →
            height M R t p ≤ height M R t rightPosition + 1 ∧
            height M R t rightPosition ≤ height M R t p + 1 := by
        intro hflag
        have hboundary : p + 1 ≠ M := by
          intro hboundary
          subst M
          simp at hflag
        have hposition : rightPosition = p + 1 := by
          simp [rightPosition, hboundary]
        simpa only [hposition] using height_skew M R t p (by omega)
      rw [step_encode_active δ dead _ _ _ _ _ _ hpositive hleft hright
        (by
          intro generation
          by_cases hboundary : p + 1 = M
          · simp [synchronous, hboundary]
          · simp [synchronous, rightPosition, hboundary])]
      simp only [height, tick, hzero, ↓reduceIte, decide_eq_true_eq, ready]
      by_cases hboundary : p + 1 = M <;>
        simp [rightPosition, hboundary]

lemma run_at_generation {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (M : ℕ) (R : ℕ → ℕ) (input : ℕ → Q)
    (t p generation : ℕ) (hp : p < M)
    (hheight : height M R t p = generation + 1) :
    run δ dead M R input t p =
      some (AsyncHalfLine.tag generation,
        synchronous δ dead M input generation p,
        synchronous δ dead M input (generation - 1) p) := by
  rw [run_encode δ dead M R input t p hp, hheight]
  simp only [AsyncHalfLine.encode, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceIte, Nat.add_sub_cancel,
    show generation + 1 - 2 = generation - 1 from by omega]

/-- Operational form of the uniform bound: at time `T+k`, each strip cell
stores some generation at least `k`, together with its predecessor. -/
theorem run_after_uniform_completion {Q : Type}
    (δ : Q → Q → Q → Q) (dead : Q)
    (M : ℕ) (R : ℕ → ℕ) (input : ℕ → Q) (T k p : ℕ)
    (hp : p < M) (hrelease : ∀ q, q < M → R q ≤ T) :
    ∃ generation, k ≤ generation ∧
      run δ dead M R input (T + k) p =
        some (AsyncHalfLine.tag generation,
          synchronous δ dead M input generation p,
          synchronous δ dead M input (generation - 1) p) := by
  let generation := height M R (T + k) p - 1
  have hbound := height_uniform_completion M R T k p hp hrelease
  have hheight : height M R (T + k) p = generation + 1 := by
    dsimp only [generation]
    omega
  exact ⟨generation, by omega,
    run_at_generation δ dead M R input (T + k) p generation hp hheight⟩

/-- A dead state occupying either exterior half-line remains literally dead. -/
lemma dead_exterior {α β : Type}
    (C : CellAutomaton α β) (dead : C.Q) (hdead : C.dead dead)
    (c : Config C.Q) (M t : ℕ) (p : ℤ)
    (hc : ∀ q : ℤ, q < 0 ∨ (M : ℤ) ≤ q → c q = dead)
    (hp : p < 0 ∨ (M : ℤ) ≤ p) :
    C.nextt c t p = dead := by
  induction t with
  | zero => exact hc p hp
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    exact hdead _ _ _ ih

/-- Finite synchronous evolution agrees with the full-line CA when both
exterior half-lines start in one absorbing dead state. -/
theorem synchronous_eq_nextt {α β : Type}
    (C : CellAutomaton α β) (dead : C.Q) (hdead : C.dead dead)
    (c : Config C.Q) (M generation p : ℕ) (hp : p < M)
    (hc : ∀ q : ℤ, q < 0 ∨ (M : ℤ) ≤ q → c q = dead) :
    synchronous C.δ dead M (fun q : ℕ => c q) generation p =
      C.nextt c generation (p : ℤ) := by
  induction generation generalizing p with
  | zero => rfl
  | succ generation ih =>
    have hleft :
        (if p = 0 then dead
          else synchronous C.δ dead M (fun q : ℕ => c q)
            generation (p - 1)) =
          C.nextt c generation ((p : ℤ) - 1) := by
      split
      · rename_i hzero
        subst p
        exact (dead_exterior C dead hdead c M generation (-1) hc
          (by omega)).symm
      · rw [ih (p - 1) (by omega)]
        congr 1
        omega
    have hright :
        (if p + 1 = M then dead
          else synchronous C.δ dead M (fun q : ℕ => c q)
            generation (p + 1)) =
          C.nextt c generation ((p : ℤ) + 1) := by
      split
      · rename_i hboundary
        exact (dead_exterior C dead hdead c M generation
          ((p : ℤ) + 1) hc (by
            right
            exact_mod_cast hboundary.ge)).symm
      · rename_i hboundary
        rw [ih (p + 1) (by omega)]
        congr 1
    calc
      synchronous C.δ dead M (fun q : ℕ => c q) (generation + 1) p =
          C.δ (C.nextt c generation ((p : ℤ) - 1))
            (C.nextt c generation p)
            (C.nextt c generation ((p : ℤ) + 1)) := by
        rw [synchronous, hleft, hright, ih p hp]
      _ = C.nextt c (generation + 1) (p : ℤ) := by
        rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]

/-- The stored current and previous values can therefore be read directly as
full-line CA iterates under a dead exterior on both sides. -/
theorem run_at_generation_eq_nextt {α β : Type}
    (C : CellAutomaton α β) (dead : C.Q) (hdead : C.dead dead)
    (c : Config C.Q) (M : ℕ)
    (hc : ∀ q : ℤ, q < 0 ∨ (M : ℤ) ≤ q → c q = dead)
    (R : ℕ → ℕ) (t p generation : ℕ) (hp : p < M)
    (hheight : height M R t p = generation + 1) :
    run C.δ dead M R (fun q : ℕ => c q) t p =
      some (AsyncHalfLine.tag generation,
        C.nextt c generation (p : ℤ),
        C.nextt c (generation - 1) (p : ℤ)) := by
  rw [run_at_generation C.δ dead M R _ t p generation hp hheight,
    synchronous_eq_nextt C dead hdead c M generation p hp hc,
    synchronous_eq_nextt C dead hdead c M (generation - 1) p hp hc]

/-- A finite controller supplies both boundary bits and initialization
packets to the asynchronous strip. -/
structure Driven where
  {α ι β : Type}
  inner : CellAutomaton ι β
  controller : CellAutomaton α ((Bool × Bool) × Option ι)
  dead : inner.Q
  padding : β

namespace Driven

variable (e : Driven)

/-- Radius-one product of the controller with the finite asynchronous state. -/
def C : CellAutomaton e.α e.β where
  Q := e.controller.Q × State e.inner.Q
  δ := fun left center right =>
    let controllerState := e.controller.δ left.1 center.1 right.1
    let signal := e.controller.project controllerState
    (controllerState, step e.inner.δ e.dead signal.1.1 signal.1.2
      (signal.2.map e.inner.embed) left.2 center.2 right.2)
  embed := fun input =>
    let controllerState := e.controller.embed input
    (controllerState,
      ((e.controller.project controllerState).2.map e.inner.embed).map
        (fun state => (0, state, state)))
  project := fun state =>
    AsyncHalfLine.output e.inner.project e.padding state.2

/-- Boundary bits are required only after release because initialization
ignores them.  No controller behavior is prescribed outside `p < M`. -/
structure ControllerSpec
    (M : ℕ) (c : Config e.α) (R : ℕ → ℕ) (input : ℕ → e.ι) : Prop where
  packets : ∀ t p : ℕ, p < M →
    (e.controller.comp ⦋c⦌ t (p : ℤ)).2 =
      packet R input t p
  boundaries : ∀ t p : ℕ, p < M → R p < t →
    (e.controller.comp ⦋c⦌ t (p : ℤ)).1 =
      (decide (p = 0), decide (p + 1 = M))

lemma controller_track (c : Config e.α) (t : ℕ) (p : ℤ) :
    (e.C.nextt ⦋c⦌ t p).1 = e.controller.nextt ⦋c⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    change e.controller.δ
      ((e.C.nextt ⦋c⦌ t (p - 1)).1)
      ((e.C.nextt ⦋c⦌ t p).1)
      ((e.C.nextt ⦋c⦌ t (p + 1)).1) = _
    rw [ih (p - 1), ih p, ih (p + 1)]

/-- The data layer uses the controller output after the controller's next
transition, i.e. the signal at physical time `t+1`. -/
lemma data_step (c : Config e.α) (t : ℕ) (p : ℤ) :
    (e.C.nextt ⦋c⦌ (t + 1) p).2 =
      step e.inner.δ e.dead
        (e.controller.comp ⦋c⦌ (t + 1) p).1.1
        (e.controller.comp ⦋c⦌ (t + 1) p).1.2
        ((e.controller.comp ⦋c⦌ (t + 1) p).2.map e.inner.embed)
        ((e.C.nextt ⦋c⦌ t (p - 1)).2)
        ((e.C.nextt ⦋c⦌ t p).2)
        ((e.C.nextt ⦋c⦌ t (p + 1)).2) := by
  rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
  change step e.inner.δ e.dead
    (e.controller.project (e.controller.δ
      ((e.C.nextt ⦋c⦌ t (p - 1)).1)
      ((e.C.nextt ⦋c⦌ t p).1)
      ((e.C.nextt ⦋c⦌ t (p + 1)).1))).1.1
    (e.controller.project (e.controller.δ
      ((e.C.nextt ⦋c⦌ t (p - 1)).1)
      ((e.C.nextt ⦋c⦌ t p).1)
      ((e.C.nextt ⦋c⦌ t (p + 1)).1))).1.2
    ((e.controller.project (e.controller.δ
      ((e.C.nextt ⦋c⦌ t (p - 1)).1)
      ((e.C.nextt ⦋c⦌ t p).1)
      ((e.C.nextt ⦋c⦌ t (p + 1)).1))).2.map e.inner.embed)
    _ _ _ = _
  rw [e.controller_track c t (p - 1),
    e.controller_track c t p,
    e.controller_track c t (p + 1)]
  simp only [CellAutomaton.comp_apply,
    CellAutomaton.nextt_succ, CellAutomaton.next_apply]

/-- Without a packet at a position, its data layer stays uninitialized.
Neither neighboring behavior nor boundary signals are constrained. -/
lemma data_none_of_no_packets
    (c : Config e.α) (p : ℤ)
    (hpacket : ∀ t, (e.controller.comp ⦋c⦌ t p).2 = none)
    (t : ℕ) :
    (e.C.nextt ⦋c⦌ t p).2 = none := by
  induction t with
  | zero =>
    have hzero := hpacket 0
    change (e.controller.project (e.controller.embed (c p))).2 = none at hzero
    change
      ((e.controller.project (e.controller.embed (c p))).2.map
        e.inner.embed).map (fun state => (0, state, state)) = none
    rw [hzero]
    rfl
  | succ t ih =>
    rw [e.data_step c t p, hpacket (t + 1), ih]
    rfl

/-- Consequently a position that never receives a packet always projects to
the driven automaton's padding symbol. -/
lemma comp_of_no_packets
    (c : Config e.α) (p : ℤ)
    (hpacket : ∀ t, (e.controller.comp ⦋c⦌ t p).2 = none)
    (t : ℕ) :
    e.C.comp ⦋c⦌ t p = e.padding := by
  change
    AsyncHalfLine.output e.inner.project e.padding
      ((e.C.nextt ⦋c⦌ t p).2) = e.padding
  rw [e.data_none_of_no_packets c p hpacket t]
  rfl

theorem data_track
    (M : ℕ) (c : Config e.α) (R : ℕ → ℕ) (input : ℕ → e.ι)
    (hs : e.ControllerSpec M c R input) (t p : ℕ) (hp : p < M) :
    (e.C.nextt ⦋c⦌ t (p : ℤ)).2 =
      run e.inner.δ e.dead M R
        (fun q => e.inner.embed (input q)) t p := by
  induction t generalizing p with
  | zero =>
    have hpacket := hs.packets 0 p hp
    change
      (e.controller.project (e.controller.embed (c (p : ℤ)))).2 = _
      at hpacket
    change
      ((e.controller.project (e.controller.embed (c (p : ℤ)))).2.map
        e.inner.embed).map (fun state => (0, state, state)) = _
    rw [hpacket, AsyncHalfLine.packet_map]
    rfl
  | succ t ih =>
    rw [e.data_step, hs.packets (t + 1) p hp, AsyncHalfLine.packet_map]
    by_cases hactive : R p < t + 1
    · rw [hs.boundaries (t + 1) p hp hactive]
      rw [run]
      apply step_congr_boundaries
      · exact ih p hp
      · intro hleft
        have hpzero : p ≠ 0 := by
          intro hpzero
          subst p
          simp at hleft
        have hcast : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by omega
        rw [hcast, ih (p - 1) (by omega)]
      · intro hright
        have hboundary : p + 1 ≠ M := by
          intro hboundary
          subst M
          simp at hright
        have hcast : (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ) := by omega
        simp only [if_neg hboundary]
        rw [hcast, ih (p + 1) (by omega)]
    · have hbefore : t < R p := by omega
      rw [ih p hp, run_before_release _ _ _ _ _ t p hbefore]
      rw [run, run_before_release _ _ _ _ _ t p hbefore]
      rfl

lemma comp_eq_output
    (M : ℕ) (c : Config e.α) (R : ℕ → ℕ) (input : ℕ → e.ι)
    (hs : e.ControllerSpec M c R input) (t p : ℕ) (hp : p < M) :
    e.C.comp ⦋c⦌ t (p : ℤ) =
      AsyncHalfLine.output e.inner.project e.padding
        (run e.inner.δ e.dead M R
          (fun q => e.inner.embed (input q)) t p) := by
  change
    AsyncHalfLine.output e.inner.project e.padding
      ((e.C.nextt ⦋c⦌ t (p : ℤ)).2) = _
  rw [e.data_track M c R input hs t p hp]

lemma comp_of_run
    (M : ℕ) (c : Config e.α) (R : ℕ → ℕ) (input : ℕ → e.ι)
    (hs : e.ControllerSpec M c R input) (t p : ℕ) (hp : p < M)
    (generation : Fin 3) (current previous : e.inner.Q)
    (hstate : run e.inner.δ e.dead M R
        (fun q => e.inner.embed (input q)) t p =
      some (generation, current, previous)) :
    e.C.comp ⦋c⦌ t (p : ℤ) = e.inner.project current := by
  rw [e.comp_eq_output M c R input hs t p hp, hstate]
  rfl

end Driven
end CellularAutomatas.AsyncHalfLine.FiniteStrip
