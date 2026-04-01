/-
  Config-based 5/3 Speedup with k=5

  Generalizes `CAgfSpeedup` from word-based to config-based input.
  Pipeline: RegularToLeftIndep → LeftIndepSpeedupConfig(k=5) → LeftIndepToRegular

  Net effect: 5/3 speedup — 5 original steps per 3 compressed steps.

  ## Extraction pattern (1+2+2 split) for C_orig position 0

  Each "cycle n" reads 3 compressed cells and extracts 5 original time steps:

  - spec_a: C @ (3n+1, 2n) comp 4 → C_orig(5n+1, 0) [single]
  - spec_b: C @ (3n+2, 2n+1) comp 3,2 → (C_orig(5n+2, 0), C_orig(5n+3, 0)) [pair.fst, single]
  - spec_c: C @ (3n+3, 2n+2) comp 1,0 → (C_orig(5n+4, 0), C_orig(5n+5, 0)) [pair.fst, single]

  ## Derivation

  Step 3: C @ (t', p') = step2 @ (2t', p'-t')           [LeftIndepToRegular.spec_nextt]
  Step 2 (diagonal): component j at step2 @ (T, P) for P<0, T ≥ -P:
    step1 @ ((T - 4P - j).toNat, 5P + j)                [LeftIndepSpeedupConfig.spec_diagonal]
  Step 1:
    even time 2s at pos q → single(C_orig(s, q+s))      [RegularToLeftIndep.spec_combined]
    odd time 2s+1 at pos q → pair(C_orig(s, q+s), C_orig(s, q+s+1))

  For cycle n, we need P = -(n+1). This means p' = t' - (n+1).

  At C @ (3n+1, 2n):
    T = 6n+2, P = -(n+1)
    j=4: step1 @ (10n+2, -5n-1), even s=5n+1, pos 0 → single(C_orig(5n+1, 0)) ✓

  At C @ (3n+2, 2n+1):
    T = 6n+4, P = -(n+1)
    j=3: step1 @ (10n+5, -5n-2), odd s=5n+2, pos 0 → pair.fst: C_orig(5n+2, 0) ✓
    j=2: step1 @ (10n+6, -5n-3), even s=5n+3, pos 0 → single(C_orig(5n+3, 0)) ✓

  At C @ (3n+3, 2n+2):
    T = 6n+6, P = -(n+1)
    j=1: step1 @ (10n+9, -5n-4), odd s=5n+4, pos 0 → pair.fst: C_orig(5n+4, 0) ✓
    j=0: step1 @ (10n+10, -5n-5), even s=5n+5, pos 0 → single(C_orig(5n+5, 0)) ✓
-/

import CellularAutomatas.defs
import CellularAutomatas.internal_defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.left_indep_from_regular
import CellularAutomatas.proofs.constructions.speedup_left_independent_config
import CellularAutomatas.proofs.constructions.left_indep_to_regular

namespace CellularAutomatas

open CellAutomaton

/-!
## Main structure
-/

structure CAgfSpeedupConfig where
  {Q : Type}
  {β : Type}
  [_inst_Q : Alphabet Q]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton Q β

attribute [instance] CAgfSpeedupConfig._inst_Q
attribute [instance] CAgfSpeedupConfig._inst_β

namespace CAgfSpeedupConfig

variable (e : CAgfSpeedupConfig)

/-!
## Pipeline construction

Step 1: Regular → Left-Independent (doubles time, state becomes single/pair/dead)
Step 2: Left-Independent Speedup with k=5 (compresses 5 cells into tuple)
Step 3: Left-Independent → Regular (halves time)

Net effect: 5/3 speedup (5 original steps per 3 compressed steps)
-/

private def step1 := RegularToLeftIndep.mk e.C_orig

private def step2 : LeftIndepSpeedupConfig := {
  Q := e.step1.C.Q
  δ := e.step1.C.δ
  k := 5
  hk := by decide
  h_left_indep := e.step1.C_left_independent
}

private def step3 := LeftIndepToRegular.mk e.step2.C' e.step2.δ'_left_indep

/-- The final compressed CA -/
def C := e.step3.C

/-!
## Configuration compression
-/

/-- Compress step1: wrap each Q state in RegularToLeftIndep.Q'.single -/
private def compress1 (c : Config e.C_orig.Q) : Config e.step1.C.Q :=
  fun i => RegularToLeftIndep.Q'.single (c i)

/-- Full compression through the pipeline -/
def compress (c : Config e.C_orig.Q) : Config e.C.Q :=
  e.step2.compress (e.compress1 c)

/-!
## Extraction functions

The final state type is `e.step2.Q'` which is one of:
- single(q)      where q : step1.Q' = single/pair/dead
- spatial(w)     where w : Fin 5 → step1.Q'
- diagonal(w)    where w : Fin 5 → step1.Q'

At the positions/times we care about (diagonal regime, i < 0), we have diagonal states.
Each component is a step1.Q' which is single or pair (not dead in valid evolution).

For k=5 with the 1+2+2 split:
- Component 4 gives single → C_orig at one time
- Components 3, 2 give pair.fst and single → C_orig at two times
- Components 1, 0 give pair.fst and single → C_orig at two times
-/

/-- Extract β from a step1.Q' that is a single -/
private def extract_single (q : e.step1.C.Q) : e.β :=
  match q with
  | RegularToLeftIndep.Q'.single s => e.C_orig.project s
  | RegularToLeftIndep.Q'.pair s _ => e.C_orig.project s  -- fallback
  | RegularToLeftIndep.Q'.dead => default

/-- Extract first β from a step1.Q' that is a pair -/
private def extract_pair_fst (q : e.step1.C.Q) : e.β :=
  match q with
  | RegularToLeftIndep.Q'.pair s _ => e.C_orig.project s
  | RegularToLeftIndep.Q'.single s => e.C_orig.project s  -- fallback
  | RegularToLeftIndep.Q'.dead => default

/-- Get the Fin 5 → step1.Q' tuple from a C.Q state -/
private def get_tuple (q : e.C.Q) : Fin 5 → e.step1.C.Q :=
  match q with
  | LeftIndepSpeedupConfig.Q'.diagonal w => w
  | LeftIndepSpeedupConfig.Q'.spatial w => w
  | LeftIndepSpeedupConfig.Q'.single s => fun _ => s

/-!
## Main extraction functions

At C @ (3n+1, 2n): step2 @ (6n+2, -(n+1)), diagonal regime
  Component 4 → step1 even → single → C_orig(5n+1, 0)

At C @ (3n+2, 2n+1): step2 @ (6n+4, -(n+1)), diagonal regime
  Component 3 → step1 odd → pair.fst → C_orig(5n+2, 0)
  Component 2 → step1 even → single → C_orig(5n+3, 0)

At C @ (3n+3, 2n+2): step2 @ (6n+6, -(n+1)), diagonal regime
  Component 1 → step1 odd → pair.fst → C_orig(5n+4, 0)
  Component 0 → step1 even → single → C_orig(5n+5, 0)
-/

/-- Extract single β from component 4 (even step1 time → single) -/
def extract_a (q : e.C.Q) : e.β :=
  e.extract_single (e.get_tuple q ⟨4, by decide⟩)

/-- Extract two β values from components 3 (pair.fst) and 2 (single) -/
def extract_b (q : e.C.Q) : e.β × e.β :=
  ( e.extract_pair_fst (e.get_tuple q ⟨3, by decide⟩),
    e.extract_single (e.get_tuple q ⟨2, by decide⟩) )

/-- Extract two β values from components 1 (pair.fst) and 0 (single) -/
def extract_c (q : e.C.Q) : e.β × e.β :=
  ( e.extract_pair_fst (e.get_tuple q ⟨1, by decide⟩),
    e.extract_single (e.get_tuple q ⟨0, by decide⟩) )

/-!
## Main theorems

The 5/3 speedup: every 3 compressed steps yield 5 original time steps at position 0.
Cycle n reads C @ (3n+1, 2n), (3n+2, 2n+1), (3n+3, 2n+2) and gives
C_orig at times 5n+1, 5n+2, 5n+3, 5n+4, 5n+5 at position 0.

Proof strategy: chain step3.spec_nextt → step2.spec_diagonal → step1.spec_combined,
then simplify arithmetic to match the stated positions.
-/

/-- step2.C_orig and step1.C have the same δ, so their nextt coincide -/
private lemma step2_C_orig_eq_step1_C :
    e.step2.C_orig.nextt = e.step1.C.nextt := by rfl

/-- step1.spec_combined: even time -/
private lemma compress1_spec_even (c : Config e.C_orig.Q) (s : ℕ) (q : ℤ) :
    e.step1.C.nextt (e.compress1 c) (2*s) q =
    RegularToLeftIndep.Q'.single (e.C_orig.nextt c s (q + s)) :=
  (e.step1.spec_combined c s q).1

/-- step1.spec_combined: odd time -/
private lemma compress1_spec_odd (c : Config e.C_orig.Q) (s : ℕ) (q : ℤ) :
    e.step1.C.nextt (e.compress1 c) (2*s+1) q =
    RegularToLeftIndep.Q'.pair (e.C_orig.nextt c s (q + s)) (e.C_orig.nextt c s (q + s + 1)) :=
  (e.step1.spec_combined c s q).2

/-- spec_a: component 4 at C @ (3n+1, 2n) gives C_orig(5n+1, 0) -/
theorem spec_a (c : Config e.C_orig.Q) (n : ℕ) :
    e.extract_a (e.C.nextt (e.compress c) (3*n+1) (2*n))
    = e.C_orig.project (e.C_orig.nextt c (5*n+1) 0) := by
  -- Chain: C → step3 → step2 → step1 → C_orig
  show e.extract_a (e.step3.C.nextt (e.compress c) (3 * n + 1) ↑(2 * n)) = _
  rw [e.step3.spec_nextt]
  show e.extract_a (e.step2.C'.nextt (e.step2.compress (e.compress1 c))
    (2 * (3 * n + 1)) (2 * ↑n - ↑(3 * n + 1))) = _
  rw [e.step2.spec_diagonal (e.compress1 c) _ (by omega) _ (by omega)]
  -- Unfold extraction
  unfold extract_a get_tuple extract_single
  -- Replace step2.C_orig.nextt with step1.C.nextt (same δ, defeq)
  simp only [show e.step2.C_orig.nextt = e.step1.C.nextt from rfl]
  -- Unfold step2 to make k=5 concrete
  unfold step2
  -- Force beta reduction
  dsimp only []
  -- Goal:
  -- (match step1.C.nextt (compress1 c) (↑(2*(3*n+1)) - ↑(5-1)*(2*↑n - ↑(3*n+1)) - ↑4).toNat
  --        (↑5 * (2*↑n - ↑(3*n+1)) + ↑4) with
  --   | Q'.single s => C_orig.project s | Q'.pair s _ => C_orig.project s | Q'.dead => default)
  -- = C_orig.project (C_orig.nextt c (5*n+1) 0)
  --
  -- Simplify the time arg to 2*(5*n+1) then apply compress1_spec_even
  -- Use norm_num to reduce numeric expressions
  norm_num
  -- Goal after norm_num:
  -- (match step1.C.nextt (compress1 c) (2*(3*↑n+1) - 4*(2*↑n-(3*↑n+1)) - 4).toNat
  --        (5*(2*↑n-(3*↑n+1))+4) with ...)
  -- = C_orig.project (C_orig.next (C_orig.nextt c (5*n)) 0)
  -- Simplify the time expression
  have h_time : (2 * (3 * (↑n : ℤ) + 1) - 4 * (2 * ↑n - (3 * ↑n + 1)) - 4).toNat
      = 2 * (5 * n + 1) := by omega
  rw [h_time, e.compress1_spec_even c (5 * n + 1)]
  -- Goal: match Q'.single(nextt c (5n+1) pos) with | single s => project s | ... = project(next(nextt c (5n)) 0)
  -- Reduce the match on Q'.single
  simp only []
  -- Goal should now be: project(nextt c (5n+1) pos) = project(next(nextt c (5n)) 0)
  -- Simplify position: 5*(2n-(3n+1))+4+(5n+1) = -5n-5+4+5n+1 = 0
  have h_pos : 5 * (2 * (↑n : ℤ) - (3 * ↑n + 1)) + 4 + ↑(5 * n + 1) = 0 := by omega
  rw [h_pos]
  -- Goal: project(nextt c (5n+1) 0) = project(next(nextt c (5n)) 0)
  -- nextt c (5n+1) = next(nextt c (5n))
  simp only [CellAutomaton.nextt_succ]

/-- spec_b: components 3,2 at C @ (3n+2, 2n+1) give C_orig at times 5n+2, 5n+3, pos 0 -/
theorem spec_b (c : Config e.C_orig.Q) (n : ℕ) :
    e.extract_b (e.C.nextt (e.compress c) (3*n+2) (2*n+1))
    = ( e.C_orig.project (e.C_orig.nextt c (5*n+2) 0),
        e.C_orig.project (e.C_orig.nextt c (5*n+3) 0) ) := by
  -- Chain: C → step3 → step2 → diagonal → step1 → C_orig
  show e.extract_b (e.step3.C.nextt (e.compress c) (3 * n + 2) ↑(2 * n + 1)) = _
  rw [e.step3.spec_nextt]
  show e.extract_b (e.step2.C'.nextt (e.step2.compress (e.compress1 c))
    (2 * (3 * n + 2)) (↑(2 * n + 1) - ↑(3 * n + 2))) = _
  rw [e.step2.spec_diagonal (e.compress1 c) _ (by omega) _ (by omega)]
  -- Unfold extraction for both components
  unfold extract_b get_tuple extract_pair_fst extract_single
  simp only [show e.step2.C_orig.nextt = e.step1.C.nextt from rfl]
  unfold step2
  dsimp only []
  norm_num
  -- Component 3 (odd time): time = (10n+5) = 2*(5n+2)+1
  -- Component 2 (even time): time = (10n+6) = 2*(5n+3)
  have h_time3 : (2 * (3 * (↑n : ℤ) + 2) - 4 * ((2 * ↑n + 1) - (3 * ↑n + 2)) - 3).toNat
      = 2 * (5 * n + 2) + 1 := by omega
  have h_time2 : (2 * (3 * (↑n : ℤ) + 2) - 4 * ((2 * ↑n + 1) - (3 * ↑n + 2)) - 2).toNat
      = 2 * (5 * n + 3) := by omega
  rw [h_time3, h_time2, e.compress1_spec_odd c (5 * n + 2), e.compress1_spec_even c (5 * n + 3)]
  -- After rewrite, matches on Q'.pair and Q'.single reduce
  simp only []
  -- Position equalities: both should simplify to 0
  -- After norm_num, RHS has nextt c (5*n+2) → next(next(nextt c (5*n))) etc.
  -- We need to show position expressions = 0 and unify nextt forms
  have h_pos3 : (5 : ℤ) * (2 * ↑n + 1 - (3 * ↑n + 2)) + 3 + ↑(5 * n + 2) = 0 := by omega
  have h_pos2 : (5 : ℤ) * (2 * ↑n + 1 - (3 * ↑n + 2)) + 2 + ↑(5 * n + 3) = 0 := by omega
  rw [h_pos3, h_pos2]
  simp only [CellAutomaton.nextt_succ]
  exact ⟨trivial, trivial⟩

/-- spec_c: components 1,0 at C @ (3n+3, 2n+2) give C_orig at times 5n+4, 5n+5, pos 0 -/
theorem spec_c (c : Config e.C_orig.Q) (n : ℕ) :
    e.extract_c (e.C.nextt (e.compress c) (3*n+3) (2*n+2))
    = ( e.C_orig.project (e.C_orig.nextt c (5*n+4) 0),
        e.C_orig.project (e.C_orig.nextt c (5*n+5) 0) ) := by
  -- Chain: C → step3 → step2 → diagonal → step1 → C_orig
  show e.extract_c (e.step3.C.nextt (e.compress c) (3 * n + 3) ↑(2 * n + 2)) = _
  rw [e.step3.spec_nextt]
  show e.extract_c (e.step2.C'.nextt (e.step2.compress (e.compress1 c))
    (2 * (3 * n + 3)) (↑(2 * n + 2) - ↑(3 * n + 3))) = _
  rw [e.step2.spec_diagonal (e.compress1 c) _ (by omega) _ (by omega)]
  -- Unfold extraction for both components
  unfold extract_c get_tuple extract_pair_fst extract_single
  simp only [show e.step2.C_orig.nextt = e.step1.C.nextt from rfl]
  unfold step2
  dsimp only []
  norm_num
  -- Component 1: time = (...).toNat - 1 = 2*(5n+4)+1 (odd)
  -- Component 0: time = (...).toNat = 2*(5n+5) (even)
  have h_base : (2 * (3 * (↑n : ℤ) + 3) - 4 * (2 * ↑n + 2 - (3 * ↑n + 3))).toNat
      = 2 * (5 * n + 5) := by omega
  have h_time1 : (2 * (3 * (↑n : ℤ) + 3) - 4 * (2 * ↑n + 2 - (3 * ↑n + 3))).toNat - 1
      = 2 * (5 * n + 4) + 1 := by omega
  rw [h_time1, h_base, e.compress1_spec_odd c (5 * n + 4), e.compress1_spec_even c (5 * n + 5)]
  simp only []
  -- Position equalities simplify to 0
  have h_pos1 : (5 : ℤ) * (2 * ↑n + 2 - (3 * ↑n + 3)) + 1 + ↑(5 * n + 4) = 0 := by omega
  have h_pos0 : (5 : ℤ) * (2 * ↑n + 2 - (3 * ↑n + 3)) + ↑(5 * n + 5) = 0 := by omega
  rw [h_pos1, h_pos0]
  simp only [CellAutomaton.nextt_succ]
  exact ⟨trivial, trivial⟩

/-- Initial state: at t=0, the compressed config at position 0 gives initial value -/
theorem initial_spec (c : Config e.C_orig.Q) :
    e.extract_single (match e.C.nextt (e.compress c) 0 0 with
       | LeftIndepSpeedupConfig.Q'.single s => s
       | LeftIndepSpeedupConfig.Q'.diagonal w => w ⟨0, by have := e.step2.hk; omega⟩
       | LeftIndepSpeedupConfig.Q'.spatial w => w ⟨0, by have := e.step2.hk; omega⟩)
    = e.C_orig.project (c 0) := by
  -- At t=0, nextt is identity, then compress c 0 = Q'.single(Q'.single(c 0))
  simp only [CellAutomaton.nextt_zero]
  -- Now goal: extract_single (match compress c 0 with ...) = C_orig.project (c 0)
  -- compress c 0 = step2.compress (compress1 c) 0 = Q'.single (compress1 c 0)
  -- compress1 c 0 = Q'.single (c 0)
  unfold compress compress1
  simp only [LeftIndepSpeedupConfig.compress, show (0 : ℤ) ≥ 0 from le_refl 0, ↓reduceIte]
  -- Now match on Q'.single reduces
  unfold extract_single
  rfl

/-!
## Combined extraction for full cycle

For convenience, combine extract_a, extract_b, extract_c to get all 5 values in one go.
-/

/-- Extract all 5 β values from cycle n (requires reading three positions) -/
def extract_cycle (c : Config e.C_orig.Q) (n : ℕ) : e.β × e.β × e.β × e.β × e.β :=
  let a := e.extract_a (e.C.nextt (e.compress c) (3*n+1) (2*n))
  let (b, c') := e.extract_b (e.C.nextt (e.compress c) (3*n+2) (2*n+1))
  let (d, f) := e.extract_c (e.C.nextt (e.compress c) (3*n+3) (2*n+2))
  (a, b, c', d, f)

/-- Full cycle spec: extract_cycle n gives C_orig times 5n+1 through 5n+5 at position 0 -/
theorem spec_cycle (c : Config e.C_orig.Q) (n : ℕ) :
    e.extract_cycle c n
    = ( e.C_orig.project (e.C_orig.nextt c (5*n+1) 0),
        e.C_orig.project (e.C_orig.nextt c (5*n+2) 0),
        e.C_orig.project (e.C_orig.nextt c (5*n+3) 0),
        e.C_orig.project (e.C_orig.nextt c (5*n+4) 0),
        e.C_orig.project (e.C_orig.nextt c (5*n+5) 0) ) := by
  show e.extract_cycle c n = _
  unfold extract_cycle
  rw [spec_a, spec_b, spec_c]

end CAgfSpeedupConfig

end CellularAutomatas
