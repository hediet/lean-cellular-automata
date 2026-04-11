import CellularAutomatas.defs
import CellularAutomatas.internal_defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.trace_kx
import CellularAutomatas.proofs.rt_eq_2n_iff_rt_eq_rt_rev.lx_rt_implies_rt

/-!
# Extract Middle Input CA Construction

Extracts the middle cell(s) of the input word:
- Odd-length words: outputs the single middle cell value
- Even-length words: outputs both middle cell values as a pair

## Design

### Stage 1: Half-speed signal (`extractMidValueCA`)

Each input value becomes a signal moving left at speed 1/2.
- State: `phase : Bool`, `value : Option α`
- Phase toggles each step; MOVE when phase=false, HOLD when phase=true
- MOVE: copy the right neighbor's value
- HOLD: keep current value

Position at cell 0, time t: `(t + 1) / 2`

### Stage 2: TraceKx wrapper (`extractMidCA`)

Uses `TraceKx` with k=1 to see the current and previous output of Stage 1.
At time n-1 (cell 0):
- Index 0 → time n-2: value from position `(n-1)/2`
- Index 1 → time n-1: value from position `n/2`

For even n: index 0 gives `w[n/2-1]`, index 1 gives `w[n/2]` → `.pair`
For odd n:  index 1 gives `w[n/2]` → `.single`
-/

namespace CellularAutomatas

open CellAutomaton

/-! ### Stage 1: Half-Speed Signal CA -/

structure HalfSpeedState (α : Type) where
  phase : Bool
  value : Option α
  deriving DecidableEq, Inhabited

instance {α : Type} [Fintype α] : Fintype (HalfSpeedState α) :=
  Fintype.ofEquiv (Bool × Option α)
    { toFun := fun (p, v) => ⟨p, v⟩
      invFun := fun s => (s.phase, s.value)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Half-speed signal transition:
    - phase=false → MOVE: take right neighbor's value
    - phase=true  → HOLD: keep current value -/
def halfSpeed_δ (α : Type)
    (_left center right : HalfSpeedState α) : HalfSpeedState α :=
  { phase := !center.phase,
    value := if center.phase then center.value else right.value }

/-- Stage 1 CA: outputs `(value, phase)` at each cell. -/
def extractMidValueCA (α : Type) [Alphabet α] : CellAutomaton α？ (α？ × Bool) where
  Q := HalfSpeedState α
  δ := halfSpeed_δ α
  embed := fun a =>
    match a with
    | some x => { phase := false, value := some x }
    | none   => { phase := false, value := none }
  project := fun s => (s.value, s.phase)

/-! ### Stage 1 Correctness -/

/-- Phase at any position at time t equals `decide (t % 2 = 1)`. -/
private lemma halfSpeed_phase {α : Type} [Alphabet α] (w : Word α) (t : ℕ) (p : ℤ) :
    ((extractMidValueCA α).nextt ⦋(word_to_config w)⦌ t p).phase = decide (t % 2 = 1) := by
  induction t with
  | zero =>
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, extractMidValueCA]
    cases (word_to_config w p) <;> simp
  | succ t ih =>
    rw [CellAutomaton.nextt_succ]
    show (!((extractMidValueCA α).nextt ⦋(word_to_config w)⦌ t p).phase) = _
    rw [ih]
    cases h : decide (t % 2 = 1) <;> simp_all <;> omega

/-- Value at cell p at time t comes from position `p + (t + 1) / 2` (generalized).
    We need this for all positions to make the induction work. -/
private lemma halfSpeed_value_general {α : Type} [Alphabet α] (w : Word α) (t : ℕ) (p : ℤ)
    (hp : 0 ≤ p) (horigin : p.toNat + (t + 1) / 2 < w.length) :
    ((extractMidValueCA α).nextt ⦋(word_to_config w)⦌ t p).value =
      some (w[p.toNat + (t + 1) / 2]'horigin) := by
  induction t generalizing p with
  | zero =>
    -- At t=0: embed maps w[p] to { phase := false, value := some w[p] }
    simp only [CellAutomaton.nextt_zero, CellAutomaton.embed_config, extractMidValueCA]
    have hp2 : p < w.length := by omega
    simp [word_to_config, hp, hp2]
  | succ t ih =>
    rw [CellAutomaton.nextt_succ]
    -- After one step: value depends on phase at time t
    show (if ((extractMidValueCA α).nextt ⦋(word_to_config w)⦌ t p).phase
          then ((extractMidValueCA α).nextt ⦋(word_to_config w)⦌ t p).value
          else ((extractMidValueCA α).nextt ⦋(word_to_config w)⦌ t (p + 1)).value) = _
    rw [halfSpeed_phase]
    by_cases ht : t % 2 = 1
    · -- HOLD phase (phase was true): keep current value
      simp only [ht, decide_true, ↓reduceIte]
      -- (t+1+1)/2 = (t+1)/2 when t is odd
      have h_idx : (t + 1 + 1) / 2 = (t + 1) / 2 := by omega
      have horigin' : p.toNat + (t + 1) / 2 < w.length := by linarith
      rw [ih p hp horigin']
      congr 1; congr 1; linarith
    · -- MOVE phase (phase was false): take right neighbor's value
      simp only [ht, decide_false, Bool.false_eq_true, ↓reduceIte]
      -- (t+1+1)/2 = (t+1)/2 + 1 when t is even, and we read from p+1
      have h_idx : (t + 1 + 1) / 2 = (t + 1) / 2 + 1 := by omega
      have hp1_nat : (p + 1).toNat = p.toNat + 1 := by omega
      have horigin' : (p + 1).toNat + (t + 1) / 2 < w.length := by linarith [hp1_nat, h_idx]
      rw [ih (p + 1) (by omega) horigin']
      congr 1; congr 1; linarith [hp1_nat, h_idx]

/-- Value at cell 0 at time t comes from position `(t + 1) / 2`. -/
private lemma halfSpeed_value {α : Type} [Alphabet α] (w : Word α) (t : ℕ)
    (ht : (t + 1) / 2 < w.length) :
    ((extractMidValueCA α).nextt ⦋(word_to_config w)⦌ t 0).value =
      some (w[(t + 1) / 2]'ht) := by
  have := halfSpeed_value_general w t 0 (le_refl 0) (by simpa using ht)
  simpa using this

/-- Combined spec for `extractMidValueCA` output at cell 0. -/
lemma extractMidValueCA_at_origin {α : Type} [Alphabet α] (w : Word α) (t : ℕ)
    (ht : (t + 1) / 2 < w.length) :
    (extractMidValueCA α).comp (word_to_config w) t 0 =
      (some (w[(t + 1) / 2]'ht), decide (t % 2 = 1)) := by
  simp only [CellAutomaton.comp_unfold, CellAutomaton.project_config_unfold]
  unfold extractMidValueCA
  simp only [Function.comp_apply]
  congr 1
  · exact halfSpeed_value w t ht
  · exact halfSpeed_phase w t 0

/-! ### Stage 2: TraceKx wrapper -/

def extractMidTrace (α : Type) [Alphabet α] : TraceKx where
  k := 1
  α := α？
  β := α？ × Bool
  C_orig := extractMidValueCA α

/-- Project TraceKx output to BetaUnionSq:
    - phase=true (even word): `.pair prev_val curr_val`
    - phase=false (odd word): `.single curr_val` -/
private def extractMidProject (α : Type) [Inhabited α] :
    (Fin 2 → (α？ × Bool)？) → BetaUnionSq α :=
  fun outputs =>
    match outputs 1 with
    | some (some val, phase) =>
      if phase then
        match outputs 0 with
        | some (some prev, _) => .pair prev val
        | _ => .pair default val
      else
        .single val
    | _ => .single default

def extractMidCA (α : Type) [Alphabet α] [Inhabited α] : CellAutomaton α？ (BetaUnionSq α) :=
  (extractMidTrace α).C.map_project (extractMidProject α)

/-! ### Main Spec -/

/-- For length-1 words, at time 0 the CA outputs `.single w[0]`. -/
theorem extractMidCA_spec_len1 {α : Type} [Alphabet α] [Inhabited α] (w : Word α) (hw : w.length = 1) :
    (extractMidCA α).comp w 0 0 = BetaUnionSq.single (w[0]'(by omega)) := by
  -- At time 0, comp = project ∘ embed applied to word_to_config w 0 = some w[0]
  unfold extractMidCA
  simp only [map_project_comp]
  -- Goal: extractMidProject α (TraceKx.C.comp w 0 0) = .single w[0]
  -- At time 0, TraceKx.C.comp w 0 0 = TraceKx.C.project (TraceKx.C.embed (some w[0]))
  -- TraceKx.C.embed (some w[0]) = fun _ => extractMidValueCA.embed (some w[0])
  --   = fun _ => { phase := false, value := some w[0] }
  -- TraceKx.C.project q = fun i => some (extractMidValueCA.project (q i))
  --   = fun i => some (some w[0], false)
  -- extractMidProject (fun i => some (some w[0], false)):
  --   outputs 1 = some (some w[0], false), phase = false → .single w[0]
  simp only [CellAutomaton.comp_apply, CellAutomaton.project_config_apply, Function.comp_apply,
    CellAutomaton.nextt_zero, CellAutomaton.embed_config]
  simp only [extractMidTrace, TraceKx.C, extractMidValueCA, word_to_config]
  have h0 : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < w.length := by omega
  simp only [h0.1, h0.2, and_self, ↓reduceDIte]
  simp only [extractMidProject]
  rfl

theorem extractMidCA_spec {α : Type} [Alphabet α] [Inhabited α] (w : Word α) (hw : w.length ≥ 2) :
    (extractMidCA α).comp w (w.length - 1) 0 =
      if w.length % 2 = 0 then
        BetaUnionSq.pair (w[w.length / 2 - 1]'(by omega)) (w[w.length / 2]'(by omega))
      else
        BetaUnionSq.single (w[w.length / 2]'(by omega)) := by
  set n := w.length with hn
  -- Step 1: extractMidCA = map_project f (trace.C), so comp = f ∘ trace.C.comp
  show extractMidProject α ((extractMidTrace α).C.comp w (n - 1) 0) = _
  -- Step 2: Apply TraceKx spec to get outputs from times n-2 and n-1
  have h_trace := (extractMidTrace α).spec_at (word_to_config w) (n - 2) 0
  have h_time : n - 2 + (extractMidTrace α).k = n - 1 := by show n - 2 + 1 = n - 1; omega
  rw [h_time] at h_trace
  rw [h_trace]
  -- Goal: extractMidProject α (fun t2 => some (C_orig.comp ⦋w⦌ (n-2+↑t2) 0)) = ...
  simp only [extractMidProject]
  -- Step 3: Evaluate the inner CA at both time steps
  have h_val1 : (extractMidTrace α).C_orig.comp (word_to_config w) (n - 2 + 1) 0 =
      (some (w[(n - 2 + 1 + 1) / 2]'(by omega)), decide ((n - 2 + 1) % 2 = 1)) :=
    extractMidValueCA_at_origin w (n - 2 + 1) (by omega)
  have h_val0 : (extractMidTrace α).C_orig.comp (word_to_config w) (n - 2) 0 =
      (some (w[(n - 2 + 1) / 2]'(by omega)), decide ((n - 2) % 2 = 1)) :=
    extractMidValueCA_at_origin w (n - 2) (by omega)
  simp only [Fin.val_one, Fin.val_zero, Nat.add_zero, h_val1, h_val0]
  -- Step 4: Case-split on parity and simplify
  by_cases hp : n % 2 = 0
  · -- Even: phase at n-1 is true → .pair
    have h1 : (n - 2 + 1) % 2 = 1 := by omega
    have h2 : ¬((n - 2) % 2 = 1) := by omega
    simp only [h1, decide_true]
    have hi1 : (n - 2 + 1) / 2 = n / 2 - 1 := by omega
    have hi2 : (n - 2 + 1 + 1) / 2 = n / 2 := by omega
    simp only [hi1, hi2, ← hn, hp, ↓reduceIte]
  · -- Odd: phase at n-1 is false → .single
    have h1 : ¬((n - 2 + 1) % 2 = 1) := by omega
    simp only [h1, decide_false]
    have hi : (n - 2 + 1 + 1) / 2 = n / 2 := by omega
    simp [hi, ← hn, hp]

end CellularAutomatas
