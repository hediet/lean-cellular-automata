import CellularAutomatas.proofs.constructions.speedup_compressed
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.ready_packets

namespace CellularAutomatas.LocalHorizon.Fusion

open CellAutomaton
open MarkedPrefix.LT

namespace RetainedEvents

variable {α β : Type} [Alphabet β]

/-- Keep the first event at each site, including events in the initial state. -/
def retain (source : CellAutomaton α (Option β)) :
    CellAutomaton α (Option β) where
  Q := source.Q × Option β
  embed symbol := (source.embed symbol, source.project (source.embed symbol))
  δ left center right :=
    let updated := source.δ left.1 center.1 right.1
    (updated, center.2.or (source.project updated))
  project state := state.2

variable (source : CellAutomaton α (Option β)) (input : Config α)

/-- Retention does not interfere with the source computation, anywhere on the line. -/
theorem source_state (t : ℕ) (p : ℤ) :
    ((retain source).nextt ⦋input⦌ t p).1 = source.nextt ⦋input⦌ t p := by
  induction t generalizing p with
  | zero =>
    show (source.embed (input p), source.project (source.embed (input p))).1 = _
    rfl
  | succ t ih =>
    rw [nextt_succ, nextt_succ]
    show source.δ
      (((retain source).nextt ⦋input⦌ t (p - 1)).1)
      (((retain source).nextt ⦋input⦌ t p).1)
      (((retain source).nextt ⦋input⦌ t (p + 1)).1) = _
    rw [ih, ih, ih]
    rfl

@[simp]
theorem comp_zero (p : ℤ) :
    (retain source).comp ⦋input⦌ 0 p = source.comp ⦋input⦌ 0 p := rfl

theorem comp_succ (t : ℕ) (p : ℤ) :
    (retain source).comp ⦋input⦌ (t + 1) p =
      ((retain source).comp ⦋input⦌ t p).or (source.comp ⦋input⦌ (t + 1) p) := by
  simp only [comp_apply, nextt_succ]
  show (((retain source).nextt ⦋input⦌ t p).2).or
    (source.project (source.δ
      (((retain source).nextt ⦋input⦌ t (p - 1)).1)
      (((retain source).nextt ⦋input⦌ t p).1)
      (((retain source).nextt ⦋input⦌ t (p + 1)).1))) = _
  rw [source_state, source_state, source_state]
  rfl

theorem none_before (t : ℕ) (p : ℤ)
    (hsource : ∀ r ≤ t, source.comp ⦋input⦌ r p = none) :
    (retain source).comp ⦋input⦌ t p = none := by
  induction t with
  | zero =>
    show (retain source).comp ⦋input⦌ 0 p = none
    exact (comp_zero source input p).trans (hsource 0 (by omega))
  | succ t ih =>
    show (retain source).comp ⦋input⦌ (t + 1) p = none
    rw [comp_succ, ih (fun r hr => hsource r (by omega)), hsource (t + 1) le_rfl]
    rfl

/-- Once latched, an event survives arbitrary later source behavior. -/
theorem persists {r t : ℕ} {p : ℤ} {payload : β} (hrt : r ≤ t)
    (hevent : (retain source).comp ⦋input⦌ r p = some payload) :
    (retain source).comp ⦋input⦌ t p = some payload := by
  induction t with
  | zero =>
    show (retain source).comp ⦋input⦌ 0 p = some payload
    have : r = 0 := by omega
    simpa only [this] using hevent
  | succ t ih =>
    show (retain source).comp ⦋input⦌ (t + 1) p = some payload
    by_cases hrt' : r ≤ t
    · rw [comp_succ, ih hrt']
      rfl
    · have : r = t + 1 := by omega
      simpa only [this] using hevent

theorem first_event {r t : ℕ} {p : ℤ} {payload : β} (hrt : r ≤ t)
    (hevent : source.comp ⦋input⦌ r p = some payload)
    (hearlier : ∀ u < r, source.comp ⦋input⦌ u p = none) :
    (retain source).comp ⦋input⦌ t p = some payload := by
  apply persists source input hrt
  cases r with
  | zero =>
    show (retain source).comp ⦋input⦌ 0 p = some payload
    exact (comp_zero source input p).trans hevent
  | succ r =>
    show (retain source).comp ⦋input⦌ (r + 1) p = some payload
    rw [comp_succ, none_before source input r p (fun u hu => hearlier u (by omega)),
      hevent]
    rfl

/-- A site-local one-shot promise suffices; no promise is needed at other sites. -/
theorem one_shot {p : ℤ} (release : ℕ) (payload : β)
    (hsource : ∀ t, source.comp ⦋input⦌ t p =
      if t = release then some payload else none) (t : ℕ) :
    (retain source).comp ⦋input⦌ t p =
      if release ≤ t then some payload else none := by
  by_cases hready : release ≤ t
  · show (retain source).comp ⦋input⦌ t p = _
    rw [if_pos hready]
    apply first_event source input hready
    · show source.comp ⦋input⦌ release p = some payload
      simp [hsource]
    · intro u hu
      show source.comp ⦋input⦌ u p = none
      rw [hsource, if_neg (by omega)]
  · show (retain source).comp ⦋input⦌ t p = _
    rw [if_neg hready]
    apply none_before source input
    intro r hr
    show source.comp ⦋input⦌ r p = none
    rw [hsource, if_neg (by omega)]

theorem one_shot_isSome {p : ℤ} (release : ℕ) (payload : β)
    (hsource : ∀ t, source.comp ⦋input⦌ t p =
      if t = release then some payload else none) (t : ℕ) :
    ((retain source).comp ⦋input⦌ t p).isSome = true ↔ release ≤ t := by
  rw [one_shot source input release payload hsource]
  by_cases hready : release ≤ t <;> simp [hready]

variable [Alphabet α]

/-- Pack `k` retained sites and advance the source by `k` steps per generation. -/
def speedup (k : ℕ) [NeZero k] : SpeedupKx where
  k := k
  α := α
  β := Option β
  C_orig := retain source

def packed (k : ℕ) [NeZero k] :
    CellAutomaton (Fin k → α) (Fin k → Option β) :=
  (speedup source k).C

theorem packed_comp (k : ℕ) [NeZero k] (d : ℕ) (p : ℤ) (s : Fin k) :
    (packed source k).comp ⦋SpeedupKx.compress k input⦌ d p s =
      (retain source).comp ⦋input⦌ (k * d) (p * k + s) := by
  have hspec := (speedup source k).spec (c := input) d
  exact congrFun (congrFun hspec p) s

theorem packed_one_shot (k : ℕ) [NeZero k] (d : ℕ) (p : ℤ) (s : Fin k)
    (release : ℕ) (payload : β)
    (hsource : ∀ t, source.comp ⦋input⦌ t (p * k + s) =
      if t = release then some payload else none) :
    (packed source k).comp ⦋SpeedupKx.compress k input⦌ d p s =
      if release ≤ k * d then some payload else none := by
  calc
    (packed source k).comp ⦋SpeedupKx.compress k input⦌ d p s =
        (retain source).comp ⦋input⦌ (k * d) (p * k + s) :=
      packed_comp source input k d p s
    _ = if release ≤ k * d then some payload else none :=
      one_shot source input release payload hsource (k * d)

omit [Alphabet β] in
theorem readyBlock_eq_some {k : ℕ} {lanes : Fin k → Option β}
    {payload : Fin k → β} :
    readyBlock lanes = some payload ↔ ∀ s, lanes s = some (payload s) := by
  constructor
  · intro h s
    show lanes s = some (payload s)
    unfold readyBlock at h
    split at h
    · rename_i hall
      have hfun := Option.some.inj h
      have hlane := hall s
      cases hs : lanes s with
      | none => simp [hs] at hlane
      | some value =>
        have := congrFun hfun s
        simpa [hs] using congrArg some this
    · contradiction
  · intro h
    show readyBlock lanes = some payload
    simp [readyBlock, h]

omit [Alphabet β] in
theorem readyBlock_ready {k : ℕ} (lanes : Fin k → Option β) :
    (readyBlock lanes).isSome = true ↔ ∀ s, (lanes s).isSome = true := by
  simp only [readyBlock]
  split <;> simp_all

omit [Alphabet β] in
/-- Readiness of persistent lanes is exactly the conjunction of their release bounds. -/
theorem readyBlock_spec {k : ℕ} (release : Fin k → ℕ) (payload : Fin k → β)
    (t : ℕ) (lanes : Fin k → Option β)
    (hlanes : ∀ s, lanes s = if release s ≤ t then some (payload s) else none) :
    readyBlock lanes =
      if ∀ s, release s ≤ t then some payload else none := by
  by_cases hready : ∀ s, release s ≤ t
  · show readyBlock lanes = _
    rw [if_pos hready, readyBlock_eq_some]
    intro s
    show lanes s = some (payload s)
    rw [hlanes, if_pos (hready s)]
  · show readyBlock lanes = _
    rw [if_neg hready]
    unfold readyBlock
    split
    · rename_i hall
      exfalso
      apply hready
      intro s
      have hs := hall s
      rw [hlanes] at hs
      by_contra h
      simp [h] at hs
    · rfl

def packedJoined (k : ℕ) [NeZero k] :
    CellAutomaton (Fin k → α) (Option (Fin k → β)) :=
  (packed source k).map_project readyBlock

theorem packedJoined_comp (k : ℕ) [NeZero k] (d : ℕ) (p : ℤ) :
    (packedJoined source k).comp ⦋SpeedupKx.compress k input⦌ d p =
      readyBlock (fun s : Fin k =>
        (retain source).comp ⦋input⦌ (k * d) (p * k + s)) := by
  change readyBlock ((packed source k).comp ⦋SpeedupKx.compress k input⦌ d p) = _
  congr 1
  funext s
  exact packed_comp source input k d p s

theorem packedJoined_one_shot (k : ℕ) [NeZero k] (d : ℕ) (p : ℤ)
    (release : Fin k → ℕ) (payload : Fin k → β)
    (hsource : ∀ (s : Fin k) t, source.comp ⦋input⦌ t (p * k + s) =
      if t = release s then some (payload s) else none) :
    (packedJoined source k).comp ⦋SpeedupKx.compress k input⦌ d p =
      if ∀ s, release s ≤ k * d then some payload else none := by
  rw [packedJoined_comp]
  apply readyBlock_spec
  intro s
  exact one_shot source input (release s) (payload s) (hsource s) (k * d)

theorem packedJoined_ready (k : ℕ) [NeZero k] (d : ℕ) (p : ℤ)
    (release : Fin k → ℕ) (payload : Fin k → β)
    (hsource : ∀ (s : Fin k) t, source.comp ⦋input⦌ t (p * k + s) =
      if t = release s then some (payload s) else none) :
    ((packedJoined source k).comp ⦋SpeedupKx.compress k input⦌ d p).isSome = true ↔
      ∀ s, release s ≤ k * d := by
  rw [packedJoined_one_shot source input k d p release payload hsource]
  by_cases hready : ∀ s, release s ≤ k * d <;> simp [hready]

/-- A complete packed payload remains fixed, even without a one-shot promise. -/
theorem packedJoined_persists (k : ℕ) [NeZero k] {d e : ℕ} {p : ℤ}
    {payload : Fin k → β} (hde : d ≤ e)
    (hready : (packedJoined source k).comp ⦋SpeedupKx.compress k input⦌ d p =
      some payload) :
    (packedJoined source k).comp ⦋SpeedupKx.compress k input⦌ e p =
      some payload := by
  rw [packedJoined_comp, readyBlock_eq_some] at hready ⊢
  intro s
  show (retain source).comp ⦋input⦌ (k * e) (p * k + s) = some (payload s)
  exact persists source input (Nat.mul_le_mul_left k hde) (hready s)

end RetainedEvents

end CellularAutomatas.LocalHorizon.Fusion
