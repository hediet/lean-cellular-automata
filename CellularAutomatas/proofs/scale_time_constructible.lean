import CellularAutomatas.proofs.time_constructible

namespace CellularAutomatas

/-!
# Proof that t(n) = c*n is Time-Constructible for c ≥ 1

A slow signal propagates left at speed 1/c using a counter.
Cell p becomes active at time c*(n-p). Position 0 becomes active at time c*n.

## Construction
- State: Fin (c+1), counter from 0 to c
- Border embeds as c (active), inside as 0
- δ: if right = c (active), increment counter (capped at c); else stay
- Active = counter at c
- Position p becomes active at time c * (n - p)
-/

variable (c : ℕ) [NeZero c]

/-- State space: counter 0..c, where c means "active" -/
abbrev ScaleState := Fin (c + 1)

/-- The active state (counter = c). -/
def scaleActive : ScaleState c := ⟨c, Nat.lt_succ_self c⟩

def scaleTimerCA : CellAutomaton Unit？ Bool where
  Q := ScaleState c
  δ := fun _left mid right =>
    if right = scaleActive c then
      if h : mid.val + 1 < c + 1 then ⟨mid.val + 1, h⟩ else mid
    else mid
  embed := fun a => match a with
    | none => scaleActive c
    | some () => ⟨0, Nat.zero_lt_succ c⟩
  project := fun s => s = scaleActive c

/-- Border cells are always active. -/
lemma scaleTimerCA_border (n t : ℕ) (p : ℤ) (hp : ¬(0 ≤ p ∧ p < n)) :
    (scaleTimerCA c).nextt ⦋unitWord n⦌ t p = scaleActive c := by
  induction t with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, word_to_config,
               unitWord_length, scaleTimerCA]
    have hcond : ¬(0 ≤ p ∧ p < ↑n) := hp
    simp only [hcond, dite_false]
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next]
    unfold scaleTimerCA
    simp only [scaleTimerCA] at ih
    rw [ih]
    -- scaleActive c = ⟨c, _⟩, so c + 1 < c + 1 is false
    simp only [scaleActive, Nat.add_lt_add_iff_right, lt_irrefl, dite_false, ite_self]

/-- Helper: δ function behavior for scaleTimerCA. -/
lemma scaleTimerCA_delta (left mid right : ScaleState c) :
    (scaleTimerCA c).δ left mid right =
    if right = scaleActive c then
      if h : mid.val + 1 < c + 1 then ⟨mid.val + 1, h⟩ else mid
    else mid := by
  simp only [scaleTimerCA]

/-- Counter value at inside position p at time t. -/
lemma scaleTimerCA_counter (n t p : ℕ) (hp : p < n) :
    ((scaleTimerCA c).nextt ⦋unitWord n⦌ t p).val = min c (t - c * (n - p - 1)) := by
  -- Induction on t
  induction t generalizing p with
  | zero =>
    -- At t = 0, inside cells have counter 0
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, word_to_config,
               unitWord_length, Nat.zero_sub, Nat.min_zero, scaleTimerCA]
    -- The inside condition holds
    have hcond : 0 ≤ (p : ℤ) ∧ (p : ℤ) < n := by omega
    simp only [hcond, and_self, dite_true]
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next]
    -- Get right neighbor's state
    by_cases hp1 : p + 1 < n
    · -- Right neighbor is inside
      have ih_self := ih p hp
      have ih_right := ih (p + 1) hp1
      have h_right_eq : n - (p + 1) - 1 = n - p - 2 := by omega
      rw [h_right_eq] at ih_right
      -- Apply the δ helper
      rw [scaleTimerCA_delta]
      -- Coercion fact: ↑p + 1 = ↑(p + 1) in ℤ
      have h_coerce : (↑p + 1 : ℤ) = ↑(p + 1) := by omega
      simp only [h_coerce]
      -- Case on whether right neighbor is active
      by_cases h_right_active : (scaleTimerCA c).nextt ⦋unitWord n⦌ t (↑(p + 1) : ℤ) = scaleActive c
      · -- Right is active
        simp only [h_right_active, ↓reduceIte]
        -- Counter at right = c means t ≥ c * (n - p - 2) + c
        have h_right_val : ((scaleTimerCA c).nextt ⦋unitWord n⦌ t (↑(p + 1) : ℤ)).val = c := by
          simp only [h_right_active, scaleActive]
        rw [ih_right] at h_right_val
        -- h_right_val : min c (t - c * (n - p - 2)) = c means t ≥ c * (n - p - 1)
        have h_t_ge : t ≥ c * (n - p - 1) := by
          simp only [Nat.min_def] at h_right_val
          split_ifs at h_right_val with h_cmp
          · -- c ≤ t - c * (n - p - 2) means t ≥ c * (n - p - 2) + c
            have h_np : c * (n - p - 1) = c * (n - p - 2) + c := by
              have h_dist : n - p - 1 = n - p - 2 + 1 := by omega
              rw [h_dist]; ring
            -- From h_cmp: c ≤ t - c * (n - p - 2)
            -- This means t ≥ c * (n - p - 2) + c
            have h_add : t ≥ c * (n - p - 2) + c := by
              have h_nontriv : t ≥ c * (n - p - 2) := by
                by_contra h_neg
                push_neg at h_neg
                have h_sub_zero : t - c * (n - p - 2) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h_neg)
                rw [h_sub_zero] at h_cmp
                have : c > 0 := NeZero.pos c
                omega
              omega
            rw [← h_np] at h_add
            exact h_add
          · -- contradiction case
            have h_lt : t - c * (n - p - 2) < c := Nat.lt_of_not_le h_cmp
            rw [h_right_val] at h_lt
            exact (Nat.lt_irrefl c h_lt).elim
        -- Increment the counter (capped at c)
        by_cases h_incr : ((scaleTimerCA c).nextt ⦋unitWord n⦌ t (p : ℤ)).val + 1 < c + 1
        · simp only [h_incr, dite_true]
          rw [ih_self]
          simp only [Nat.min_def]
          split_ifs with h1 h2 <;> omega
        · simp only [h_incr, dite_false]
          rw [ih_self]
          push_neg at h_incr
          simp only [Nat.min_def]
          split_ifs with h1 h2 <;> omega
      · -- Right is not active
        simp only [h_right_active, ↓reduceIte]
        -- Counter at right ≠ c means t < c * (n - p - 1)
        have h_right_val : ((scaleTimerCA c).nextt ⦋unitWord n⦌ t (↑(p + 1) : ℤ)).val ≠ c := by
          intro h_eq
          apply h_right_active
          rw [Fin.ext_iff]; simp only [scaleActive, h_eq]
        rw [ih_right] at h_right_val
        have h_t_lt : t < c * (n - p - 1) := by
          simp only [Nat.min_def, ne_eq] at h_right_val
          split_ifs at h_right_val with h_cmp
          · -- h_cmp says c ≤ t - c*(n-p-2), and h_right_val : c ≠ c, contradiction
            omega
          · -- h_cmp: ¬(c ≤ t - c*(n-p-2)), i.e., t - c*(n-p-2) < c
            push_neg at h_cmp
            have h_np2 : c * (n - p - 1) = c * (n - p - 2) + c := by
              have h_dist : n - p - 1 = n - p - 2 + 1 := by omega
              rw [h_dist]; ring
            omega
        -- Counter stays at 0
        have h_curr_zero : t - c * (n - p - 1) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h_t_lt)
        have h_next_le : t + 1 - c * (n - p - 1) ≤ 1 := by omega
        rw [ih_self, h_curr_zero]
        simp only [Nat.min_zero, Nat.min_def]
        split_ifs with h1 <;> omega
    · -- Right neighbor is border (p = n - 1)
      have hp_eq : p = n - 1 := by omega
      have hp1_border : ¬(0 ≤ (p + 1 : ℤ) ∧ (p + 1 : ℤ) < n) := by omega
      have ih_self := ih p hp
      -- Apply the δ helper
      rw [scaleTimerCA_delta]
      -- Coercion fact
      have h_coerce : (↑p + 1 : ℤ) = ↑(p + 1) := by omega
      simp only [h_coerce]
      -- Right is border = scaleActive c
      have h_right_eq : (scaleTimerCA c).nextt ⦋unitWord n⦌ t (↑(p + 1) : ℤ) = scaleActive c :=
        scaleTimerCA_border c n t (↑(p + 1)) hp1_border
      simp only [h_right_eq, ↓reduceIte]
      -- Since p = n - 1, delay = c * (n - p - 1) = c * 0 = 0
      have h_delay : c * (n - p - 1) = 0 := by
        have : n - p - 1 = 0 := by omega
        simp [this]
      by_cases h_incr : ((scaleTimerCA c).nextt ⦋unitWord n⦌ t (p : ℤ)).val + 1 < c + 1
      · simp only [h_incr, dite_true]
        rw [ih_self, h_delay, Nat.sub_zero]
        simp only [Nat.sub_zero]  -- normalize t + 1 - 0 → t + 1
        -- h_incr says min c t + 1 < c + 1, i.e., min c t < c
        have h_min_lt : min c t < c := by omega
        -- If min c t < c, then t < c (since min c t = min(c, t) and if t ≥ c then min = c)
        have h_t_lt : t < c := by
          by_contra h
          push_neg at h
          have : min c t = c := Nat.min_eq_left h
          omega
        -- Use explicit case analysis
        by_cases h1 : c ≤ t
        · -- h1: c ≤ t contradicts h_t_lt
          omega
        · -- ¬(c ≤ t), i.e., t < c
          by_cases h2 : c ≤ t + 1
          · -- c ≤ t + 1 with t < c means c = t + 1
            have h_eq : t + 1 = c := le_antisymm h_t_lt h2
            simp [Nat.min_def, h1, h2, h_eq]
          · -- t + 1 < c
            simp [Nat.min_def, h1, h2]
      · simp only [h_incr, dite_false]
        rw [ih_self, h_delay, Nat.sub_zero]
        simp only [Nat.sub_zero]  -- normalize
        -- h_incr says counter.val + 1 ≥ c + 1
        -- After rw ih_self, counter.val = min c t
        -- So min c t + 1 ≥ c + 1, i.e., min c t ≥ c
        have h_min_ge : min c t ≥ c := by
          simp only [not_lt] at h_incr
          omega
        have h_min_eq : min c t = c := le_antisymm (Nat.min_le_left c t) h_min_ge
        -- Since min c t = c, we have c ≤ t
        have h_c_le_t : c ≤ t := by
          by_contra h
          push_neg at h
          have : min c t = t := Nat.min_eq_right (Nat.le_of_lt h)
          omega
        simp only [Nat.min_def]
        have h_c_le_t1 : c ≤ t + 1 := Nat.le_succ_of_le h_c_le_t
        simp [h_c_le_t, h_c_le_t1]

/-- Inside cell at position p is active iff t ≥ c * (n - p). -/
lemma scaleTimerCA_inside_active_iff (n t : ℕ) (p : ℕ) (hp : p < n) :
    (scaleTimerCA c).nextt ⦋unitWord n⦌ t p = scaleActive c ↔ t ≥ c * (n - p) := by
  rw [Fin.ext_iff, scaleTimerCA_counter c n t p hp]
  simp only [scaleActive, Fin.val_mk]
  -- min c (t - c * (n - p - 1)) = c ↔ t ≥ c * (n - p)
  -- Key fact: c * (n - p) = c * (n - p - 1) + c when n > p
  have h_np_pos : n - p ≥ 1 := Nat.sub_pos_of_lt hp
  have h_key : c * (n - p) = c * (n - p - 1) + c := by
    have h_dist : n - p - 1 + 1 = n - p := Nat.sub_add_cancel h_np_pos
    calc c * (n - p) = c * (n - p - 1 + 1) := by rw [h_dist]
      _ = c * (n - p - 1) + c * 1 := by rw [Nat.mul_add]
      _ = c * (n - p - 1) + c := by ring
  constructor
  · intro h
    simp only [Nat.min_def] at h
    split_ifs at h with h1
    · -- c ≤ t - c * (n - p - 1) and min = c: trivially t ≥ c *(n-p-1) + c
      have h_add : t ≥ c * (n - p - 1) + c := by
        by_contra h_neg
        push_neg at h_neg
        have h_sub_zero : t - c * (n - p - 1) < c := by
          by_cases h_ge : t ≥ c * (n - p - 1)
          · omega
          · have h_zero : t - c * (n - p - 1) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_le h_ge))
            have hc : c > 0 := NeZero.pos c
            omega
        omega
      omega
    · -- ¬(c ≤ t - c * (n - p - 1)) and t - c * (n - p - 1) = c: contradiction
      have h_lt : t - c * (n - p - 1) < c := Nat.lt_of_not_le h1
      omega
  · intro h
    simp only [Nat.min_def]
    -- t ≥ c * (n - p) = c * (n - p - 1) + c, so t - c * (n - p - 1) ≥ c
    have h_ge : t ≥ c * (n - p - 1) + c := by omega
    have h' : t - c * (n - p - 1) ≥ c := by
      have h_base : t ≥ c * (n - p - 1) := by omega
      omega
    split_ifs with h1
    · rfl
    · omega

/-- Position 0 is active at time c*n. -/
lemma scaleTimerCA_signal (n : ℕ) :
    (scaleTimerCA c).project ((scaleTimerCA c).nextt ⦋unitWord n⦌ (c * n) 0) = true := by
  cases hn : n with
  | zero =>
    have hp : ¬(0 ≤ (0 : ℤ) ∧ (0 : ℤ) < 0) := by omega
    simp only [Nat.mul_zero]
    rw [scaleTimerCA_border c 0 0 0 hp]
    simp only [scaleTimerCA, scaleActive, decide_true]
  | succ n' =>
    have hp : (0 : ℕ) < n' + 1 := by omega
    have h := (scaleTimerCA_inside_active_iff c (n' + 1) (c * (n' + 1)) 0 hp).mpr (by simp)
    -- The goal involves `0` which is `(0 : ℤ)` by coercion
    -- h involves `↑0` which is also `(0 : ℤ)`
    -- They should be definitionally equal, use convert
    convert decide_eq_true h

/-- Position 0 is not active before time c*n. -/
lemma scaleTimerCA_no_signal (n k : ℕ) (hk : k < c * n) :
    (scaleTimerCA c).project ((scaleTimerCA c).nextt ⦋unitWord n⦌ k 0) = false := by
  cases hn : n with
  | zero =>
    simp only [hn, Nat.mul_zero] at hk
    omega
  | succ n' =>
    have hp : (0 : ℕ) < n' + 1 := by omega
    have h_not_active : ¬(k ≥ c * (n' + 1 - 0)) := by
      simp only [Nat.sub_zero, hn] at hk ⊢
      omega
    have h_iff := scaleTimerCA_inside_active_iff c (n' + 1) k 0 hp
    have h_ne : (scaleTimerCA c).nextt ⦋unitWord (n' + 1)⦌ k (↑0 : ℤ) ≠ scaleActive c := by
      intro h_eq
      exact h_not_active (h_iff.mp h_eq)
    convert decide_eq_false h_ne

/-- The function n ↦ c * n is time-constructible. -/
def scaleTimeConstructible' (c : ℕ) [NeZero c] : TimeConstructible (fun n => c * n) where
  timer := scaleTimerCA c
  signal_at_t := scaleTimerCA_signal c
  no_signal_before := scaleTimerCA_no_signal c

end CellularAutomatas
