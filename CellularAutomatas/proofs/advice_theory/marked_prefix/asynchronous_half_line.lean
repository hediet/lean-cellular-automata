import CellularAutomatas.defs

namespace CellularAutomatas.AsyncHalfLine

/- Height zero means uninitialized; height `k+1` means generation `k`. -/
def ready (g : ℕ → ℕ) (p : ℕ) : Prop :=
  (p = 0 ∨ g p ≤ g (p - 1)) ∧ g p ≤ g (p + 1)

instance (g : ℕ → ℕ) (p : ℕ) : Decidable (ready g p) :=
  inferInstanceAs (Decidable ((_ ∨ _) ∧ _))

def tick (release : Bool) (g : ℕ → ℕ) (p : ℕ) : ℕ :=
  if g p = 0 then if release then 1 else 0
  else if ready g p then g p + 1 else g p

def height (R : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, p => if R p = 0 then 1 else 0
  | t + 1, p => tick (decide (t + 1 = R p)) (height R t) p

lemma tick_bounds (r : Bool) (g : ℕ → ℕ) (p : ℕ) :
    g p ≤ tick r g p ∧ tick r g p ≤ g p + 1 := by
  unfold tick
  split
  · split <;> omega
  · split <;> omega

lemma tick_increases (r : Bool) (g : ℕ → ℕ) (p : ℕ)
    (h : g p < tick r g p) : g p = 0 ∨ ready g p := by
  unfold tick at h
  split at h
  · exact Or.inl ‹g p = 0›
  · right
    split at h
    · assumption
    · omega

/-- The higher endpoint cannot advance while its neighbor is behind. -/
lemma edge_preserved {a b a' b' : ℕ}
    (hskew : a ≤ b + 1 ∧ b ≤ a + 1)
    (ha : a ≤ a' ∧ a' ≤ a + 1) (hb : b ≤ b' ∧ b' ≤ b + 1)
    (hab : a < a' → a ≤ b) (hba : b < b' → b ≤ a) :
    a' ≤ b' + 1 ∧ b' ≤ a' + 1 := by
  by_cases h₁ : a < a'
  · have := hab h₁
    by_cases h₂ : b < b'
    · have := hba h₂
      omega
    · omega
  · by_cases h₂ : b < b'
    · have := hba h₂
      omega
    · omega

lemma height_skew (R : ℕ → ℕ) (t p : ℕ) :
    height R t p ≤ height R t (p + 1) + 1 ∧
    height R t (p + 1) ≤ height R t p + 1 := by
  induction t generalizing p with
  | zero =>
    simp only [height]
    split <;> split <;> omega
  | succ t ih =>
    apply edge_preserved (ih p) (tick_bounds _ _ p) (tick_bounds _ _ (p + 1))
    · intro h
      rcases tick_increases _ _ p h with hz | hr
      · omega
      · exact hr.2
    · intro h
      rcases tick_increases _ _ (p + 1) h with hz | hr
      · omega
      · rcases hr.1 with hp | hp
        · omega
        · simpa only [Nat.add_sub_cancel] using hp

lemma height_zero_iff (R : ℕ → ℕ) (t p : ℕ) :
    height R t p = 0 ↔ t < R p := by
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

lemma height_at_release (R : ℕ → ℕ) (p : ℕ) :
    height R (R p) p = 1 := by
  cases hr : R p with
  | zero => simp [height, hr]
  | succ t =>
    have hz : height R t p = 0 := (height_zero_iff R t p).mpr (by omega)
    simp [height, tick, hz, hr]

lemma uninitialized_blocks (R : ℕ → ℕ) (t p : ℕ)
    (h : height R t p = 0) : height R t (p + 1) ≤ 1 := by
  have := (height_skew R t p).2
  omega

/-- Skew makes threshold propagation exact even after the center passes it. -/
lemma tick_level_iff (r : Bool) (g : ℕ → ℕ) (p k : ℕ)
    (hl : p ≠ 0 → g p ≤ g (p - 1) + 1)
    (hr : g p ≤ g (p + 1) + 1) :
    k + 2 ≤ tick r g p ↔
      k + 1 ≤ g p ∧ (p = 0 ∨ k + 1 ≤ g (p - 1)) ∧ k + 1 ≤ g (p + 1) := by
  unfold tick
  split
  · rename_i hz
    split <;> omega
  · split
    · rename_i hready
      rcases hready with ⟨hl', hr'⟩
      constructor
      · intro h
        refine ⟨by omega, ?_, by omega⟩
        rcases hl' with hp | hl'
        · exact Or.inl hp
        · exact Or.inr (by omega)
      · intro h
        omega
    · rename_i hready
      constructor
      · intro h
        refine ⟨by omega, ?_, by omega⟩
        by_cases hp : p = 0
        · exact Or.inl hp
        · have := hl hp
          exact Or.inr (by omega)
      · rintro ⟨hc, hl', hr'⟩
        by_contra h
        have heq : g p = k + 1 := by omega
        apply hready
        exact ⟨by simpa only [heq] using hl', by omega⟩

/-- Interface for the independent arithmetic proof; no closed form required. -/
structure ArrivalSpec (R : ℕ → ℕ) (H : ℕ → ℕ → ℕ) : Prop where
  zero : ∀ p, H p 0 = R p
  step_zero : ∀ k, H 0 (k + 1) = 1 + max (H 0 k) (H 1 k)
  step_succ : ∀ p k, H (p + 1) (k + 1) =
    1 + max (H p k) (max (H (p + 1) k) (H (p + 2) k))

lemma arrival_step_iff {R H} (hs : ArrivalSpec R H) (p k t : ℕ) :
    H p (k + 1) ≤ t + 1 ↔
      H p k ≤ t ∧ (p = 0 ∨ H (p - 1) k ≤ t) ∧ H (p + 1) k ≤ t := by
  cases p with
  | zero =>
    rw [hs.step_zero]
    simp only [Nat.zero_add, true_or, true_and]
    omega
  | succ p =>
    rw [hs.step_succ]
    simp only [Nat.succ_ne_zero, false_or, Nat.add_sub_cancel]
    change 1 + max (H p k) (max (H (p + 1) k) (H (p + 2) k)) ≤ t + 1 ↔
      H (p + 1) k ≤ t ∧ H p k ≤ t ∧ H (p + 2) k ≤ t
    omega

lemma arrival_step_pos {R H} (hs : ArrivalSpec R H) (p k : ℕ) :
    0 < H p (k + 1) := by
  cases p with
  | zero => rw [hs.step_zero]; omega
  | succ p => rw [hs.step_succ]; omega

lemma height_reaches_iff {R H} (hs : ArrivalSpec R H) (t p k : ℕ) :
    k + 1 ≤ height R t p ↔ H p k ≤ t := by
  induction t generalizing p k with
  | zero =>
    cases k with
    | zero =>
      rw [hs.zero]
      simp only [height]
      split <;> omega
    | succ k =>
      have := arrival_step_pos hs p k
      simp only [height]
      split <;> omega
  | succ t ih =>
    cases k with
    | zero =>
      rw [hs.zero]
      have := height_zero_iff R (t + 1) p
      omega
    | succ k =>
      have hl : p ≠ 0 → height R t p ≤ height R t (p - 1) + 1 := by
        intro hp
        have h := (height_skew R t (p - 1)).2
        simpa only [show p - 1 + 1 = p from by omega] using h
      rw [height, tick_level_iff _ _ _ _ hl (height_skew R t p).1,
        arrival_step_iff hs]
      simp only [ih]

lemma arrival_step_strict {R H} (hs : ArrivalSpec R H) (p k : ℕ) :
    H p k < H p (k + 1) := by
  cases p with
  | zero => rw [hs.step_zero]; omega
  | succ p => rw [hs.step_succ]; omega

lemma height_at_arrival {R H} (hs : ArrivalSpec R H) (p k : ℕ) :
    height R (H p k) p = k + 1 := by
  have h₁ := (height_reaches_iff hs (H p k) p k).mpr (by omega)
  have h₂ := height_reaches_iff hs (H p k) p (k + 1)
  have h₃ := arrival_step_strict hs p k
  omega

lemma height_eq_iff {R H} (hs : ArrivalSpec R H) (t p k : ℕ) :
    height R t p = k + 1 ↔ H p k ≤ t ∧ t < H p (k + 1) := by
  have h₁ := height_reaches_iff hs t p k
  have h₂ := height_reaches_iff hs t p (k + 1)
  omega

/- The runtime state contains no natural-number clock. -/
def tag (k : ℕ) : Fin 3 := ⟨k % 3, Nat.mod_lt _ (by decide)⟩

lemma tag_eq_iff {k l : ℕ} (h : k ≤ l + 1 ∧ l ≤ k + 1) :
    tag l = tag k ↔ l = k := by
  simp only [tag, Fin.mk.injEq]
  omega

lemma tag_ahead_iff {k l : ℕ} (h : k ≤ l + 1 ∧ l ≤ k + 1) :
    tag l = tag (k + 1) ↔ l = k + 1 := by
  simp only [tag, Fin.mk.injEq]
  omega

lemma tag_succ (k : ℕ) : tag (k + 1) = tag k + 1 := by
  apply Fin.ext
  simp only [tag, Fin.val_add, Fin.val_one]
  omega

abbrev State (Q : Type) := Option (Fin 3 × Q × Q)

def read {Q : Type} (k : Fin 3) : State Q → Option Q
  | none => none
  | some (l, current, previous) =>
    if l = k then some current else if l = k + 1 then some previous else none

lemma read_frame {Q : Type} (x : ℕ → Q) {k l : ℕ}
    (h : k ≤ l + 1 ∧ l ≤ k + 1) :
    read (tag k) (some (tag l, x l, x (l - 1))) =
      if k ≤ l then some (x k) else none := by
  simp only [read, ← tag_succ, tag_eq_iff h, tag_ahead_iff h]
  by_cases hsame : l = k
  · subst l
    simp
  · by_cases hahead : l = k + 1
    · subst l
      simp
    · have hbehind : ¬k ≤ l := by omega
      simp [hsame, hahead, hbehind]

def encode {Q : Type} (h : ℕ) (x : ℕ → Q) : State Q :=
  if h = 0 then none else some (tag (h - 1), x (h - 1), x (h - 2))

lemma read_encode {Q : Type} (x : ℕ → Q) {c n : ℕ}
    (hc : 0 < c) (h : c ≤ n + 1 ∧ n ≤ c + 1) :
    read (tag (c - 1)) (encode n x) =
      if c ≤ n then some (x (c - 1)) else none := by
  cases n with
  | zero => simp [encode, read, Nat.not_le_of_gt hc]
  | succ n =>
    have hskew : c - 1 ≤ n + 1 ∧ n ≤ (c - 1) + 1 := by omega
    have hle : (c - 1 ≤ n) ↔ c ≤ n + 1 := by omega
    simpa only [encode, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      show n + 1 - 2 = n - 1 from by omega, hle] using read_frame x hskew

/-- At the origin, the left value is literally `dead`, not a negative clock. -/
def step {Q : Type} (δ : Q → Q → Q → Q) (dead : Q) (origin : Bool)
    (packet : Option Q) (left center right : State Q) : State Q :=
  match center with
  | none => packet.map (fun q => (0, q, q))
  | some (k, current, _) =>
    match (if origin then some dead else read k left), read k right with
    | some l, some r => some (k + 1, δ l current r, current)
    | _, _ => center

lemma encode_succ {Q : Type} {c : ℕ} (hc : 0 < c) (x : ℕ → Q) :
    encode (c + 1) x = some (tag (c - 1) + 1, x c, x (c - 1)) := by
  have htag : tag c = tag (c - 1) + 1 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ c)] using tag_succ (c - 1)
  simp only [encode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel, htag, show c + 1 - 2 = c - 1 from by omega]

lemma step_encode_active {Q : Type} (δ : Q → Q → Q → Q) (dead : Q)
    (origin : Bool) (packet : Option Q) (x xl xr : ℕ → Q) {c l r : ℕ}
    (hc : 0 < c) (hl : c ≤ l + 1 ∧ l ≤ c + 1)
    (hr : c ≤ r + 1 ∧ r ≤ c + 1)
    (hx : ∀ k, x (k + 1) = δ (if origin then dead else xl k) (x k) (xr k)) :
    step δ dead origin packet (encode l xl) (encode c x) (encode r xr) =
      encode (if (origin = true ∨ c ≤ l) ∧ c ≤ r then c + 1 else c) x := by
  have hcenter : encode c x = some (tag (c - 1), x (c - 1), x (c - 2)) := by
    simp only [encode, Nat.ne_of_gt hc, ↓reduceIte]
  have hnext := hx (c - 1)
  rw [show c - 1 + 1 = c from by omega] at hnext
  rw [hcenter]
  simp only [step]
  rw [read_encode xr hc hr]
  cases origin with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, false_or] at hnext ⊢
    rw [read_encode xl hc hl]
    by_cases hcl : c ≤ l <;> by_cases hcr : c ≤ r
    · simp only [hcl, hcr, and_self, ↓reduceIte]
      rw [encode_succ hc, hnext]
    · simp only [hcl, hcr, and_false, ↓reduceIte, hcenter]
    · simp only [hcl, hcr, false_and, ↓reduceIte, hcenter]
    · simp only [hcl, hcr, false_and, ↓reduceIte, hcenter]
  | true =>
    simp only [↓reduceIte, true_or, true_and] at hnext ⊢
    by_cases hcr : c ≤ r
    · simp only [hcr, ↓reduceIte]
      rw [encode_succ hc, hnext]
    · simp only [hcr, ↓reduceIte, hcenter]

def synchronous {Q : Type} (δ : Q → Q → Q → Q) (dead : Q) (input : ℕ → Q) :
    ℕ → ℕ → Q
  | 0, p => input p
  | k + 1, p => δ (if p = 0 then dead else synchronous δ dead input k (p - 1))
      (synchronous δ dead input k p) (synchronous δ dead input k (p + 1))

def packet {Q : Type} (R : ℕ → ℕ) (input : ℕ → Q) (t p : ℕ) : Option Q :=
  if t = R p then some (input p) else none

/-- Externally driven half-line evolution. Releases and positions occur only
in this specification, never in the finite local state or transition. -/
def run {Q : Type} (δ : Q → Q → Q → Q) (dead : Q) (R : ℕ → ℕ) (input : ℕ → Q) :
    ℕ → ℕ → State Q
  | 0, p => (packet R input 0 p).map (fun q => (0, q, q))
  | t + 1, p => step δ dead (decide (p = 0)) (packet R input (t + 1) p)
      (run δ dead R input t (p - 1)) (run δ dead R input t p)
      (run δ dead R input t (p + 1))

lemma run_encode {Q : Type} (δ : Q → Q → Q → Q) (dead : Q)
    (R : ℕ → ℕ) (input : ℕ → Q) (t p : ℕ) :
    run δ dead R input t p =
      encode (height R t p) (fun k => synchronous δ dead input k p) := by
  induction t generalizing p with
  | zero =>
    by_cases hp : R p = 0
    · simp [run, packet, height, encode, synchronous, tag, hp]
    · simp [run, packet, height, encode, hp, Ne.symm hp]
  | succ t ih =>
    rw [run, ih, ih, ih]
    by_cases hz : height R t p = 0
    · by_cases hp : t + 1 = R p
      · simp [encode, hz, step, packet, hp, height, tick, synchronous, tag]
      · simp [encode, hz, step, packet, hp, height, tick]
    · have hc : 0 < height R t p := Nat.pos_of_ne_zero hz
      have hl : height R t p ≤ height R t (p - 1) + 1 ∧
          height R t (p - 1) ≤ height R t p + 1 := by
        by_cases hp : p = 0
        · subst p
          simp
        · have h := height_skew R t (p - 1)
          rw [show p - 1 + 1 = p from by omega] at h
          exact ⟨h.2, h.1⟩
      rw [step_encode_active δ dead (decide (p = 0)) _ _ _ _ hc hl
        (height_skew R t p) (by intro k; simp only [synchronous, decide_eq_true_eq])]
      simp only [height, tick, hz, ↓reduceIte, decide_eq_true_eq, ready]

lemma run_at_generation {Q : Type} (δ : Q → Q → Q → Q) (dead : Q)
    (R : ℕ → ℕ) (input : ℕ → Q) (t p k : ℕ) (h : height R t p = k + 1) :
    run δ dead R input t p =
      some (tag k, synchronous δ dead input k p, synchronous δ dead input (k - 1) p) := by
  rw [run_encode, h]
  simp only [encode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel, show k + 1 - 2 = k - 1 from by omega]

lemma run_at_arrival {Q : Type} (δ : Q → Q → Q → Q) (dead : Q)
    (R : ℕ → ℕ) (input : ℕ → Q) {H} (hs : ArrivalSpec R H) (p k : ℕ) :
    run δ dead R input (H p k) p =
      some (tag k, synchronous δ dead input k p, synchronous δ dead input (k - 1) p) := by
  exact run_at_generation δ dead R input (H p k) p k (height_at_arrival hs p k)

lemma dead_left_exterior {α β : Type} (C : CellAutomaton α β) (d : C.Q)
    (hd : C.dead d) (c : Config C.Q) (hc : ∀ p : ℤ, p < 0 → c p = d)
    (t : ℕ) (p : ℤ) (hp : p < 0) : C.nextt c t p = d := by
  induction t with
  | zero => exact hc p hp
  | succ t ih =>
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    exact hd _ _ _ ih

lemma synchronous_eq_nextt {α β : Type} (C : CellAutomaton α β) (d : C.Q)
    (hd : C.dead d) (c : Config C.Q) (hc : ∀ p : ℤ, p < 0 → c p = d)
    (k p : ℕ) :
    synchronous C.δ d (fun q : ℕ => c q) k p = C.nextt c k (p : ℤ) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    have hleft :
        (if p = 0 then d else synchronous C.δ d (fun q : ℕ => c q) k (p - 1)) =
          C.nextt c k ((p : ℤ) - 1) := by
      split
      · rename_i hp
        subst p
        exact (dead_left_exterior C d hd c hc k _ (by omega)).symm
      · rename_i hp
        rw [ih]
        congr 1
        omega
    calc
      synchronous C.δ d (fun q : ℕ => c q) (k + 1) p =
          C.δ (C.nextt c k ((p : ℤ) - 1)) (C.nextt c k p)
            (C.nextt c k ((p : ℤ) + 1)) := by
        rw [synchronous, hleft, ih, ih]
        simp
      _ = C.nextt c (k + 1) (p : ℤ) := by
        rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]

lemma run_at_arrival_eq_nextt {α β : Type} (C : CellAutomaton α β) (d : C.Q)
    (hd : C.dead d) (c : Config C.Q) (hc : ∀ p : ℤ, p < 0 → c p = d)
    (R : ℕ → ℕ) {H} (hs : ArrivalSpec R H) (p k : ℕ) :
    run C.δ d R (fun q : ℕ => c q) (H p k) p =
      some (tag k, C.nextt c k (p : ℤ), C.nextt c (k - 1) (p : ℤ)) := by
  rw [run_at_arrival C.δ d R _ hs,
    synchronous_eq_nextt C d hd c hc, synchronous_eq_nextt C d hd c hc]

example {Q : Type} [Alphabet Q] : Alphabet (State Q) := inferInstance

end CellularAutomatas.AsyncHalfLine
