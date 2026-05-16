/-
  SmallHandler: a CA that solves the FSSP for n = 2.

  For n = 2, Mazoyer's construction does not fire. This CA detects the
  n = 2 case (the soldier sees the general on its left and Border on its
  right) and fires both cells at t = 2 = 2*2 - 2.

  For n >= 3 the CA is permanently inert (no cell ever fires).

  Note: n = 1 requires firing at t = 0 (= 2*1 - 2), which means the
  initial state `inner true` must project to `true`. But the
  quiescent-set requirement forces `project (inner false) = false`, and
  for n >= 2 at t = 0 the general cell (also `inner true`) must NOT fire.
  This is a contradiction: no single CA can satisfy `SolvesFSSPOptimal`
  for both n = 1 and n = 2.
-/

import CellularAutomatas.proofs.fssp

namespace CellularAutomatas
namespace SmallHandler

/-! ### States -/

/-- 6 states: Border and Soldier are quiescent; General is the initial
    state for the leftmost cell; G1 and R1 are intermediate states for
    n = 2; Fire is the absorbing firing state. -/
inductive Q
  | Border   -- border cell (quiescent)
  | Soldier  -- initial soldier state (quiescent)
  | General  -- initial general state
  | G1       -- general after 1 step (n >= 2)
  | R1       -- soldier that saw general left + border right (n = 2 marker)
  | Fire     -- firing state
deriving DecidableEq, Repr, Inhabited, Fintype

instance : Alphabet Q := {}

open Q

/-! ### Transition rule -/

/-- The transition rule. Key transitions:
    * delta(B, G, S) = G1: general's first step for n >= 2.
    * delta(G, S, B) = R1: n = 2 rightmost soldier detects general + border.
    * delta(B, G1, R1) = Fire and delta(G1, R1, B) = Fire: n = 2 fires at t = 2.
    * Everything else maps to Soldier (permanently inert). -/
def delta : Q -> Q -> Q -> Q
  | _, Border, _ => Border
  | _, Fire, _   => Fire
  | Border, General, Soldier => G1
  | _, General, _            => Soldier
  | Border, G1, R1 => Fire
  | G1, R1, Border => Fire
  | General, Soldier, Border => R1
  | _, _, _ => Soldier

/-! ### The CA -/

def C : LCellAutomaton Bool where
  Q := Q
  δ := delta
  embed
    | none       => Border
    | some true  => General
    | some false => Soldier
  project
    | Fire => true
    | _    => false

-- Bridge C.δ and delta for tactics that don't unfold C.
private lemma C_delta (a b c : Q) : C.δ a b c = delta a b c := rfl

/-! ### Basic properties -/

lemma quiescent_set_border_soldier :
    C.quiescent_set { C.border, C.inner false } := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  show C.δ a b c = b
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

/-! ### Firing spec: fires exactly for n = 2 at t >= 2 -/

/-- For n = 2, at t = 2, both cells reach state Fire. -/
lemma n2_fires_at_2 (p : ℤ) (hp0 : 0 <= p) (hp2 : p < 2) :
    C.nextt (⦋⟬fssp_left_side 2⟭⦌) 2 p = Fire := by
  have : p = 0 ∨ p = 1 := by omega
  rcases this with rfl | rfl <;> native_decide

/-- For n = 2, no cell fires before t = 2. -/
lemma n2_not_fire_before (t : Nat) (ht : t < 2) (p : ℤ) (hp0 : 0 <= p) (hp2 : p < 2) :
    C.comp (word_to_config (fssp_left_side 2)) t p = false := by
  have hp : p = 0 ∨ p = 1 := by omega
  have ht : t = 0 ∨ t = 1 := by omega
  rcases hp with rfl | rfl <;> rcases ht with rfl | rfl <;> native_decide

/-- Fire is absorbing: delta(_, Fire, _) = Fire. -/
lemma delta_fire_center (a b : Q) : delta a Fire b = Fire := rfl

/-- Once a cell reaches Fire, it stays Fire. -/
lemma fire_persists (c : Config C.Q) (t s : Nat) (x : ℤ)
    (h : C.nextt c t x = Fire) :
    C.nextt c (t + s) x = Fire := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
    rw [show t + (s + 1) = (t + s) + 1 from by omega]
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    simp only [C_delta]
    show delta _ (C.nextt c (t + s) x) _ = Fire
    rw [ih]; rfl

/-- For n = 2, SmallHandler fires iff t >= 2. -/
theorem n2_iff (t : Nat) (p : ℤ) (hp0 : 0 <= p) (hp2 : p < 2) :
    C.comp (word_to_config (fssp_left_side 2)) t p = true <-> t >= 2 := by
  constructor
  . -- forward: comp = true -> t >= 2
    intro hfire
    by_contra hlt
    push_neg at hlt
    have := n2_not_fire_before t hlt p hp0 hp2
    rw [this] at hfire
    exact absurd hfire (by decide)
  . -- backward: t >= 2 -> comp = true
    intro hge
    show C.project (C.nextt (⦋⟬fssp_left_side 2⟭⦌) t p) = true
    have hF := n2_fires_at_2 p hp0 hp2
    have hFt : C.nextt (⦋⟬fssp_left_side 2⟭⦌) t p = Fire := by
      have := fire_persists (⦋⟬fssp_left_side 2⟭⦌) 2 (t - 2) p hF
      rw [show 2 + (t - 2) = t from by omega] at this
      exact this
    rw [hFt]; rfl

/-! ### n ≥ 3: SmallHandler never fires

For n ≥ 3, the CA is permanently inert.  After 2 time steps every cell
is in {Border, Soldier}, both quiescent.  Key insight: Fire needs
δ(Border, G1, R1) or δ(G1, R1, Border), but R1 only arises from
δ(General, Soldier, Border) (= position n−1 with n = 2).  For n ≥ 3
that transition never fires, so R1 never appears. -/

-- delta on {Border, Soldier}³ stays in {Border, Soldier}.
private lemma delta_bs_closed (a b c : Q)
    (ha : a = Border ∨ a = Soldier) (hb : b = Border ∨ b = Soldier)
    (hc : c = Border ∨ c = Soldier) :
    delta a b c = Border ∨ delta a b c = Soldier := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first | exact Or.inl rfl | exact Or.inr rfl

-- delta on {Border, G1, Soldier}³ lands in {Border, Soldier}.
private lemma delta_bgs_to_bs (a b c : Q)
    (ha : a = Border ∨ a = G1 ∨ a = Soldier)
    (hb : b = Border ∨ b = G1 ∨ b = Soldier)
    (hc : c = Border ∨ c = G1 ∨ c = Soldier) :
    delta a b c = Border ∨ delta a b c = Soldier := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl

-- Classify the initial embedded configuration.
private lemma init_border (n : ℕ) (_hn : 3 ≤ n) (q : ℤ) (hq : q < 0 ∨ q ≥ n) :
    (⦋⟬fssp_left_side n⟭⦌ : Config C.Q) q = Border := by
  simp only [CellAutomaton.embed_config, word_to_config]
  split
  · next h =>
    exfalso
    have := fssp_left_side_length n
    omega
  · rfl

private lemma init_general (n : ℕ) (hn : 3 ≤ n) :
    (⦋⟬fssp_left_side n⟭⦌ : Config C.Q) 0 = General := by
  unfold CellAutomaton.embed_config word_to_config
  split
  · next h =>
    unfold fssp_left_side
    split_ifs with hn0
    · exfalso; omega
    · rfl
  · next h =>
    exfalso; push_neg at h
    have := fssp_left_side_length n
    omega

private lemma init_soldier (n : ℕ) (hn : 3 ≤ n) (q : ℤ) (hq0 : 0 < q) (hqn : q < n) :
    (⦋⟬fssp_left_side n⟭⦌ : Config C.Q) q = Soldier := by
  unfold CellAutomaton.embed_config word_to_config
  split
  · next h =>
    -- Unfold fssp_left_side and eliminate the n = 0 branch.
    unfold fssp_left_side
    split_ifs with hn0
    · exfalso; omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_cons, List.length_nil]
      rw [List.getElem_replicate]
      rfl
  · next h =>
    exfalso; push_neg at h
    have := fssp_left_side_length n
    omega

-- Classify the initial config as {Border, General, Soldier}.
private lemma init_classify (n : ℕ) (hn : 3 ≤ n) (q : ℤ) :
    let c := (⦋⟬fssp_left_side n⟭⦌ : Config C.Q)
    c q = Border ∨ c q = General ∨ c q = Soldier := by
  rcases lt_or_ge q 0 with hq | hq
  · exact Or.inl (init_border n hn q (Or.inl hq))
  · rcases Decidable.eq_or_ne q 0 with rfl | hne
    · exact Or.inr (Or.inl (init_general n hn))
    · rcases lt_or_ge q ↑n with hqn | hqn
      · exact Or.inr (Or.inr (init_soldier n hn q (by omega) hqn))
      · exact Or.inl (init_border n hn q (Or.inr (by omega)))

-- At t = 1, every cell is in {Border, G1, Soldier} (no R1 for n ≥ 3).
private lemma t1_classify (n : ℕ) (hn : 3 ≤ n) (q : ℤ) :
    let c := (⦋⟬fssp_left_side n⟭⦌ : Config C.Q)
    C.nextt c 1 q = Border ∨ C.nextt c 1 q = G1 ∨ C.nextt c 1 q = Soldier := by
  simp only [CellAutomaton.nextt_succ, CellAutomaton.next_apply, CellAutomaton.nextt_zero, C_delta]
  -- Goal now uses delta (not C.δ) applied to the initial config values.
  rcases lt_or_ge q 0 with hq | hq
  · -- q < 0: center is Border → C.δ(_, Border, _) = Border
    rw [init_border n hn q (Or.inl hq)]; exact Or.inl rfl
  · rcases Decidable.eq_or_ne q 0 with rfl | hne
    · -- q = 0: delta(Border, General, Soldier) = G1
      rw [init_general n hn, init_border n hn (0 - 1) (Or.inl (by omega)),
          init_soldier n hn (0 + 1) (by omega) (by omega)]
      exact Or.inr (Or.inl rfl)
    · rcases lt_or_ge q ↑n with hqn | hqn
      · -- 0 < q < n: center is Soldier
        rw [init_soldier n hn q (by omega) hqn]
        rcases Decidable.eq_or_ne (q - 1) 0 with hq1 | hq1
        · -- q = 1: left neighbor is General
          have : q = 1 := by omega
          subst this
          rw [show (1 : ℤ) - 1 = 0 from by ring, init_general n hn,
              show (1 : ℤ) + 1 = 2 from by ring,
              init_soldier n hn 2 (by omega) (by omega)]
          exact Or.inr (Or.inr rfl)
        · -- q ≥ 2: left neighbor is Soldier
          rw [init_soldier n hn (q - 1) (by omega) (by omega)]
          rcases lt_or_ge (q + 1) ↑n with hq2 | hq2
          · rw [init_soldier n hn (q + 1) (by omega) hq2]; exact Or.inr (Or.inr rfl)
          · rw [init_border n hn (q + 1) (Or.inr (by omega))]; exact Or.inr (Or.inr rfl)
      · -- q ≥ n: center is Border
        rw [init_border n hn q (Or.inr (by omega))]; exact Or.inl rfl

-- For t ≥ 2, every cell is in {Border, Soldier}.
private lemma state_ge2 (n : ℕ) (hn : 3 ≤ n) (t : ℕ) (ht : t ≥ 2) (q : ℤ) :
    let c := (⦋⟬fssp_left_side n⟭⦌ : Config C.Q)
    C.nextt c t q = Border ∨ C.nextt c t q = Soldier := by
  intro c
  -- Need IH for all q, so revert before induction.
  revert q ht
  induction t with
  | zero => intro h; omega
  | succ t' ih =>
    intro ht q
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    simp only [C_delta]
    -- Goal now uses delta. delta_bgs_to_bs / delta_bs_closed match.
    rcases Nat.lt_or_ge t' 2 with ht' | ht'
    · -- t' = 1: use t1_classify + delta_bgs_to_bs
      have : t' = 1 := by omega
      subst this
      exact delta_bgs_to_bs _ _ _
        (t1_classify n hn (q - 1)) (t1_classify n hn q) (t1_classify n hn (q + 1))
    · -- t' ≥ 2: use IH + delta_bs_closed
      exact delta_bs_closed _ _ _
        (ih (by omega) (q - 1)) (ih (by omega) q) (ih (by omega) (q + 1))

/-- For n ≥ 3, no cell ever fires. -/
lemma n_ge3_never_fires (n : ℕ) (hn : 3 ≤ n) (t : ℕ) (p : ℤ)
    (_hp0 : 0 ≤ p) (_hpn : p < n) :
    C.comp ⟬fssp_left_side n⟭ t p = false := by
  -- comp unfolds to project ∘ nextt; project maps non-Fire to false.
  simp only [CellAutomaton.comp_apply]
  rcases Nat.lt_or_ge t 2 with ht | ht
  · -- t < 2: case-split into t = 0, t = 1
    rcases show t = 0 ∨ t = 1 from by omega with rfl | rfl
    · -- t = 0
      simp only [CellAutomaton.nextt_zero]
      rcases init_classify n hn p with h | h | h <;> (rw [h]; rfl)
    · -- t = 1
      rcases t1_classify n hn p with h | h | h <;> (rw [h]; rfl)
  · -- t ≥ 2
    rcases state_ge2 n hn t ht p with h | h <;> (rw [h]; rfl)

end SmallHandler
end CellularAutomatas
