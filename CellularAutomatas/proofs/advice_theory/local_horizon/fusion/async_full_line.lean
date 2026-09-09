import CellularAutomatas.proofs.advice_theory.marked_prefix.asynchronous_half_line
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Int.Interval

namespace CellularAutomatas.AsyncFullLine

open AsyncHalfLine (State tag read encode)

/-- Both neighbors participate, at every integer position. -/
def ready (g : ℤ → ℕ) (p : ℤ) : Prop :=
  g p ≤ g (p - 1) ∧ g p ≤ g (p + 1)

instance (g : ℤ → ℕ) (p : ℤ) : Decidable (ready g p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def tick (release : Bool) (g : ℤ → ℕ) (p : ℤ) : ℕ :=
  if g p = 0 then if release then 1 else 0
  else if ready g p then g p + 1 else g p

/-- Height zero is a ghost; height `k + 1` stores target generation `k`.
The initialization packet is consumed at its actual release time. -/
def height (R : ℤ → ℕ) : ℕ → ℤ → ℕ
  | 0, p => if R p = 0 then 1 else 0
  | t + 1, p => tick (decide (t + 1 = R p)) (height R t) p

lemma tick_bounds (r : Bool) (g : ℤ → ℕ) (p : ℤ) :
    g p ≤ tick r g p ∧ tick r g p ≤ g p + 1 := by
  unfold tick
  split
  · show _ ∧ _
    split <;> omega
  · show _ ∧ _
    split <;> omega

lemma tick_increases (r : Bool) (g : ℤ → ℕ) (p : ℤ)
    (h : g p < tick r g p) : g p = 0 ∨ ready g p := by
  unfold tick at h
  split at h
  · show g p = 0 ∨ ready g p
    exact Or.inl ‹g p = 0›
  · show g p = 0 ∨ ready g p
    right
    split at h
    · assumption
    · omega

lemma height_skew (R : ℤ → ℕ) (t : ℕ) (p : ℤ) :
    height R t p ≤ height R t (p + 1) + 1 ∧
    height R t (p + 1) ≤ height R t p + 1 := by
  induction t generalizing p with
  | zero =>
    show _ ∧ _
    simp only [height]
    split <;> split <;> omega
  | succ t ih =>
    show _ ∧ _
    apply AsyncHalfLine.edge_preserved (ih p)
      (tick_bounds _ _ p) (tick_bounds _ _ (p + 1))
    · intro h
      show height R t p ≤ height R t (p + 1)
      rcases tick_increases _ _ p h with hz | hr
      · omega
      · exact hr.2
    · intro h
      show height R t (p + 1) ≤ height R t p
      rcases tick_increases _ _ (p + 1) h with hz | hr
      · omega
      · simpa only [add_sub_cancel_right] using hr.1

lemma height_skew_left (R : ℤ → ℕ) (t : ℕ) (p : ℤ) :
    height R t p ≤ height R t (p - 1) + 1 ∧
    height R t (p - 1) ≤ height R t p + 1 := by
  have h := height_skew R t (p - 1)
  simpa only [sub_add_cancel] using h.symm

lemma height_mono (R : ℤ → ℕ) (p : ℤ) :
    Monotone (fun t => height R t p) := by
  apply monotone_nat_of_le_succ
  intro t
  show height R t p ≤ tick _ (height R t) p
  exact (tick_bounds _ _ _).1

lemma height_zero_iff (R : ℤ → ℕ) (t : ℕ) (p : ℤ) :
    height R t p = 0 ↔ t < R p := by
  induction t with
  | zero =>
    show height R 0 p = 0 ↔ 0 < R p
    simp [height]
  | succ t ih =>
    show height R (t + 1) p = 0 ↔ t + 1 < R p
    simp only [height, tick]
    split
    · rename_i hz
      have ht := ih.mp hz
      simp only [decide_eq_true_eq]
      split <;> omega
    · rename_i hz
      have ht : R p ≤ t := by omega
      split <;> omega

lemma height_at_release (R : ℤ → ℕ) (p : ℤ) :
    height R (R p) p = 1 := by
  cases hr : R p with
  | zero =>
    show height R 0 p = 1
    simp [height, hr]
  | succ t =>
    show height R (t + 1) p = 1
    have hz : height R t p = 0 := (height_zero_iff R t p).mpr (by omega)
    simp [height, tick, hz, hr]

/-- A threshold propagates whenever all three previous heights reached it. -/
lemma tick_level (r : Bool) (g : ℤ → ℕ) (p : ℤ) (k : ℕ)
    (hc : k + 1 ≤ g p) (hl : k + 1 ≤ g (p - 1))
    (hr : k + 1 ≤ g (p + 1)) :
    k + 2 ≤ tick r g p := by
  unfold tick
  have hz : g p ≠ 0 := by omega
  rw [if_neg hz]
  split
  · show k + 2 ≤ g p + 1
    omega
  · rename_i hn
    show k + 2 ≤ g p
    by_contra h
    apply hn
    show g p ≤ g (p - 1) ∧ g p ≤ g (p + 1)
    omega

/-- Only the finite radius-`k` cone must have been released by `T`. -/
lemma height_cone (R : ℤ → ℕ) (T k : ℕ) (p : ℤ)
    (hR : ∀ z : ℤ, |z - p| ≤ (k : ℤ) → R z ≤ T) :
    k + 1 ≤ height R (T + k) p := by
  induction k generalizing p with
  | zero =>
    show 1 ≤ height R (T + 0) p
    have hr := hR p (by simp)
    have hz := height_zero_iff R T p
    simp only [Nat.add_zero]
    omega
  | succ k ih =>
    show k + 1 + 1 ≤ height R (T + (k + 1)) p
    have local_bound (q : ℤ) (hq : |q - p| ≤ 1) :
        ∀ z : ℤ, |z - q| ≤ (k : ℤ) → R z ≤ T := by
      intro z hz
      apply hR z
      have hq' := abs_le.mp hq
      have hz' := abs_le.mp hz
      apply abs_le.mpr
      constructor <;> push_cast <;> omega
    have hc := ih p (local_bound p (by simp))
    have hl := ih (p - 1) (local_bound (p - 1) (abs_le.mpr (by constructor <;> omega)))
    have hr := ih (p + 1) (local_bound (p + 1) (abs_le.mpr (by constructor <;> omega)))
    rw [show T + (k + 1) = (T + k) + 1 by omega, height]
    exact tick_level _ _ _ _ hc hl hr

/-- Every fixed finite cone has a finite release bound. -/
lemma exists_cone_bound (R : ℤ → ℕ) (p : ℤ) (k : ℕ) :
    ∃ T : ℕ, ∀ z : ℤ, |z - p| ≤ (k : ℤ) → R z ≤ T := by
  let cone := Finset.Icc (p - (k : ℤ)) (p + (k : ℤ))
  refine ⟨cone.sup R, ?_⟩
  intro z hz
  show R z ≤ cone.sup R
  apply Finset.le_sup
  have hz' := abs_le.mp hz
  exact Finset.mem_Icc.mpr (by omega)

lemma height_eventually (R : ℤ → ℕ) (p : ℤ) (k : ℕ) :
    ∃ t : ℕ, k + 1 ≤ height R t p := by
  obtain ⟨T, hT⟩ := exists_cone_bound R p k
  exact ⟨T + k, height_cone R T k p hT⟩

/-- Bounded one-step increments ensure that no finite generation is skipped. -/
lemma height_hits (R : ℤ → ℕ) (p : ℤ) (k : ℕ) :
    ∃ t : ℕ, height R t p = k + 1 := by
  have reached := height_eventually R p k
  refine ⟨Nat.find reached, ?_⟩
  have h := Nat.find_spec reached
  cases ht : Nat.find reached with
  | zero =>
    show height R 0 p = k + 1
    rw [ht] at h
    by_cases hr : R p = 0
    · show height R 0 p = k + 1
      simp [height, hr] at h ⊢
      omega
    · show height R 0 p = k + 1
      simp [height, hr] at h
  | succ t =>
    show height R (t + 1) p = k + 1
    have hprev := Nat.find_min reached (show t < Nat.find reached by omega)
    have hb := (tick_bounds (decide (t + 1 = R p)) (height R t) p).2
    rw [ht] at h
    change tick _ (height R t) p = k + 1
    change k + 1 ≤ tick _ (height R t) p at h
    omega

/-- The finite modulo-three protocol, with no distinguished origin. -/
def step {Q : Type} (δ : Q → Q → Q → Q)
    (packet : Option Q) (left center right : State Q) : State Q :=
  match center with
  | none => packet.map (fun q => (0, q, q))
  | some (k, current, _) =>
    match read k left, read k right with
    | some l, some r => some (k + 1, δ l current r, current)
    | _, _ => center

lemma step_eq_half_line {Q : Type} (δ : Q → Q → Q → Q) (dummy : Q)
    (packet : Option Q) (left center right : State Q) :
    step δ packet left center right =
      AsyncHalfLine.step δ dummy false packet left center right := by
  cases center with
  | none => rfl
  | some frame =>
    rcases frame with ⟨k, current, previous⟩
    rfl

lemma step_encode_active {Q : Type} (δ : Q → Q → Q → Q)
    (packet : Option Q) (x xl xr : ℕ → Q) {c l r : ℕ}
    (hc : 0 < c) (hl : c ≤ l + 1 ∧ l ≤ c + 1)
    (hr : c ≤ r + 1 ∧ r ≤ c + 1)
    (hx : ∀ k, x (k + 1) = δ (xl k) (x k) (xr k)) :
    step δ packet (encode l xl) (encode c x) (encode r xr) =
      encode (if c ≤ l ∧ c ≤ r then c + 1 else c) x := by
  rw [step_eq_half_line δ (x 0)]
  simpa only [Bool.false_eq_true, false_or, Bool.false_eq_true, ↓reduceIte] using
    AsyncHalfLine.step_encode_active δ (x 0) false packet x xl xr hc hl hr hx

def packet {Q : Type} (R : ℤ → ℕ) (initial : Config Q)
    (t : ℕ) (p : ℤ) : Option Q :=
  if t = R p then some (initial p) else none

/-- The mathematical driven run consumes time-zero packets in its initial state. -/
def run {Q : Type} (δ : Q → Q → Q → Q) (R : ℤ → ℕ) (initial : Config Q) :
    ℕ → ℤ → State Q
  | 0, p => (packet R initial 0 p).map (fun q => (0, q, q))
  | t + 1, p => step δ (packet R initial (t + 1) p)
      (run δ R initial t (p - 1)) (run δ R initial t p)
      (run δ R initial t (p + 1))

/-- Simulation of an arbitrary full-integer-line target; no dead-border hypotheses. -/
lemma run_encode {α β : Type} (target : CellAutomaton α β)
    (R : ℤ → ℕ) (initial : Config target.Q) (t : ℕ) (p : ℤ) :
    run target.δ R initial t p =
      encode (height R t p) (fun k => target.nextt initial k p) := by
  induction t generalizing p with
  | zero =>
    show run target.δ R initial 0 p = _
    by_cases hp : R p = 0
    · simp [run, packet, height, encode, tag, hp]
    · simp [run, packet, height, encode, hp, Ne.symm hp]
  | succ t ih =>
    show run target.δ R initial (t + 1) p = _
    rw [run, ih, ih, ih]
    by_cases hz : height R t p = 0
    · by_cases hp : t + 1 = R p
      · simp [encode, hz, step, packet, hp, height, tick, tag]
      · simp [encode, hz, step, packet, hp, height, tick]
    · have hc : 0 < height R t p := Nat.pos_of_ne_zero hz
      rw [step_encode_active target.δ _ _ _ _ hc
        (height_skew_left R t p) (height_skew R t p)
        (by intro k; rw [CellAutomaton.nextt_succ]; rfl)]
      simp only [height, tick, hz, ↓reduceIte, ready]

lemma run_at_generation {α β : Type} (target : CellAutomaton α β)
    (R : ℤ → ℕ) (initial : Config target.Q) (t k : ℕ) (p : ℤ)
    (h : height R t p = k + 1) :
    run target.δ R initial t p =
      some (tag k, target.nextt initial k p, target.nextt initial (k - 1) p) := by
  rw [run_encode, h]
  simp only [encode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel, show k + 1 - 2 = k - 1 from by omega]

end CellularAutomatas.AsyncFullLine
