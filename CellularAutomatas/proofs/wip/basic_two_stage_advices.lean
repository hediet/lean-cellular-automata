/-
Basic Two-Stage Advice Constructions

This file explores simple two-stage advices:
1. shift_left: [a, b, c] → [some b, some c, none]
2. shift_right: [a, b, c] → [none, some a, some b]
3. annotate_with_first: each position gets (symbol, first_element)
4. annotate_with_last: each position gets (symbol, last_element)

All are two-stage advices (CArt + FST composition).

Proof strategy:
- shift_left: Pure CArt (ca_trace_id shifts left)
- shift_right: CArt (identity) + FST (delay by 1)
- annotate_first: CArt (identity × broadcast_first), FST = identity
- annotate_last: CArt (identity × broadcast_last), FST = identity
-/

import CellularAutomatas.defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.trace_id
import CellularAutomatas.proofs.constructions.basic_product_ca
import CellularAutomatas.proofs.finite_state_transducers
import CellularAutomatas.proofs.ca_rt_utils

namespace CellularAutomatas

open CellAutomaton
open FiniteStateTransducer

variable {α : Type} [Alphabet α]

/-! ## 1. Shift Left Advice -/

def Advice.shift_left : Advice α α？ where
  f := fun w => match w with
    | [] => []
    | _::w' => w'.map some ++ [none]
  len := by
    intro w
    cases w with
    | nil => rfl
    | cons a w' => simp

-- ca_trace_id α？ shifts left: trace_rt[i] = word_to_config w (i+1) = w[i+1]?
-- This gives some(w[i+1]) if i+1 < length, else none — exactly shift_left!
theorem shift_left_is_cart_advice : Advice.shift_left.is_cart_advice (α := α) := by
  use ca_trace_id α？
  apply advice_eq_iff
  funext w
  cases w with
  | nil => simp [CellAutomaton.trace_rt, Advice.shift_left]
  | cons a w' =>
    simp only [CArtTransducer.advice, CellAutomaton.trace_rt, ca_trace_id_trace_eq, Advice.shift_left]
    apply List.ext_getElem (by simp)
    intro i h_i h_len
    -- trace[i] = config_to_trace ⟬a::w'⟭ i = ⟬a::w'⟭ (i+1) = word_to_config (a::w') (i+1)
    -- shift_left[i] = (w'.map some ++ [none])[i]
    -- Both equal: some w'[i] when i < w'.length, none when i = w'.length
    sorry

theorem shift_left_is_two_stage : Advice.shift_left.is_two_stage_advice (α := α) :=
  Advice.is_cart_advice.is_two_stage shift_left_is_cart_advice


/-! ## 2. Shift Right Advice -/

def Advice.shift_right : Advice α α？ where
  f := fun w => match w with
    | [] => []
    | _::_ => [none] ++ (w.dropLast).map some
  len := by
    intro w
    cases w with
    | nil => rfl
    | cons a w' => simp

-- FST that shifts by outputting the previous input
-- State = previous input from the right (i.e., input at position i+1)
-- At position i, state = some(w[i+1]) after processing position i+1
-- Output at position i = state before processing position i = state after processing i+1..n-1
def fst_output_prev : FiniteStateTransducer α α？ := {
  Q := α？ × α？  -- (prev_prev, prev) to shift by 1
  δ := fun (_, prev) a => (prev, some a)
  q0 := (none, none)
  f := fun (prev_prev, _) => prev_prev
}

-- The key insight: FST scanr processes right-to-left
-- At position i, output = f(state after processing positions i+1, ..., n-1)
-- For shift_right, we want output[i] = w[i-1]?
-- With state = (prev_prev, prev) tracking two previous inputs:
-- After processing positions i+1, ..., n-1 right-to-left:
--   state = (w[i], w[i+1]) approximately... let me trace through

-- For input [a, b, c]:
-- Initial: (none, none)
-- Process c: state = (none, some c), output = none
-- Process b: state = (some c, some b), output = some c
-- Process a: state = (some b, some a), output = some b
-- Result: [some b, some c, none] -- still wrong! We want [none, some a, some b]

-- The issue is the FST scans right-to-left, so outputs are in order [left, ..., right]
-- but the information flows from right to left.

-- ALTERNATIVE: Use a CArt that shifts information left, then FST delays
-- CArt: at position i, time t, position 0 receives info about position t
-- If we use ca_trace_id, at step i+1, position 0 has w[i+1]?
-- This is shift_LEFT! So shift_right needs the opposite flow.

-- For shift_right, the construction is trickier:
-- Use CArt that outputs w[i] AND its state tracks history
-- FST outputs based on what was seen before

lemma shift_right_spec (w : Word α) (h_ne : w ≠ []) :
    [none] ++ (w.dropLast).map some
    = (List.range w.length).map (fun i => if i = 0 then none else w[i-1]?) := by
  sorry -- Technical index manipulation

-- For now, use sorry for the FST construction
def ts_shift_right : TwoStageAdvice α α？ := {
  β := α × α？  -- (current, shifted)
  C := ca_zip (ca_trace_id_word α) (ca_trace_id α？)  -- outputs (w[i], w[i+1]?)
  M := {  -- extracts w[i+1]? shifted left, then delays by 1
    Q := α？
    δ := fun _ (_, shifted) => shifted
    q0 := none
    f := id
  }
}

-- The above gives us shift_left, not shift_right. Let me try another approach.
-- Actually, for shift_right we need position i to output w[i-1], but the CArt
-- processes information that flows from right to left. So position 0 after t steps
-- only knows about positions 0..t, not position -1.

-- The correct approach: use CArt = identity, and FST that buffers the previous output
-- FST state after processing positions i+1..n-1 should contain w[i]
-- Then output at position i = w[i-1] = state before processing i = FST output at position i+1

-- This requires the FST to "delay" by one position to the left.
-- With fst_output_prev design:
-- State = (buffer of size 2 to track needed delay)
-- Output = item from 2 positions ago (in processing order = 1 position to the left in word)

-- For [a, b, c], FST processes c, b, a and outputs for positions 2, 1, 0:
-- We want outputs: [none, some a, some b] for positions [0, 1, 2]
-- FST output order: [output@2, output@1, output@0] from processing order
-- = [output when processing c, output when processing b, output when processing a]
-- Want: [some b, some a, none]

-- Processing c: output = some b (need b but haven't seen it yet!)
-- This shows FST alone can't do shift_right because it outputs BEFORE seeing earlier positions.

-- SOLUTION: shift_right IS two-stage but requires a different CArt construction.
-- The CArt must compute w[i-1]? at position i.
-- For this, we can use: CArt state at position i = sequence seen from the right
-- but truncated/encoded. This is doable with finite state.

-- Actually, the simplest proof: shift_right is the composition of shift_left with an inversion.
-- Or: define it directly as a two-stage advice with appropriate CA and FST.

theorem shift_right_is_two_stage : Advice.shift_right.is_two_stage_advice (α := α) := by
  -- The construction:
  -- CArt outputs (current, shifted_right) where shifted_right = previous position's value
  -- This is achieved by having CArt propagate values leftward
  -- FST then extracts the shifted component
  sorry


/-! ## 3. Annotate With First -/

def Advice.annotate_with_first : Advice α (α × α？) where
  f := fun w => w.map fun a => (a, w.head?)
  len := by intro w; simp

-- CA that broadcasts the first element to all positions
-- Rule: prefer left neighbor (which carries w[0] from position 0 outward)
def ca_broadcast_first : CellAutomaton α？ α？ := {
  Q := α？
  δ := fun left cur _right => left.or cur
  embed := id
  project := id
}

lemma ca_broadcast_first_trace_rt (w : Word α) :
    ca_broadcast_first.trace_rt w = List.replicate w.length w.head? := by
  cases w with
  | nil => simp [CellAutomaton.trace_rt]
  | cons a w' =>
    apply List.ext_getElem (by simp [CellAutomaton.trace_rt])
    intro i h_i _
    simp only [CellAutomaton.trace_rt] at h_i
    simp only [CellAutomaton.trace_rt, List.getElem_replicate, List.head?_cons,
               List.getElem_map, List.getElem_range]
    -- At step i+1, position 0 has w.head? because the CA propagates from left
    -- After t > 0 steps, position 0 has: δ(nextt(-1,t), nextt(0,t-1), nextt(1,t-1))
    -- Since position -1 is always none, and cur at step 1 is some a, we get some a
    unfold CellAutomaton.trace
    -- Need: nextt (embed_word (a::w')) (i+1) 0 = some a
    sorry

def ca_with_first : CArtTransducer α (α × α？) :=
  ca_zip (ca_trace_id_word α) ca_broadcast_first

def ts_annotate_first : TwoStageAdvice α (α × α？) := {
  β := α × α？
  C := ca_with_first
  M := M_id (α × α？)
}

theorem annotate_first_is_two_stage : Advice.annotate_with_first.is_two_stage_advice (α := α) := by
  use ts_annotate_first
  apply advice_eq_iff
  funext w
  simp only [TwoStageAdvice.advice, ts_annotate_first, Function.comp_apply, M_id_scanr_eq, id_eq,
             ca_with_first, ca_zip_trace_rt, ca_trace_id_scan_temporal]
  rw [ca_broadcast_first_trace_rt]
  simp only [Advice.annotate_with_first]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp


/-! ## 4. Annotate With Last -/

def Advice.annotate_with_last : Advice α (α × α？) where
  f := fun w => w.map fun a => (a, w.getLast?)
  len := by intro w; simp

-- CA that broadcasts the last element to all positions
-- Rule: prefer right neighbor (which carries w.getLast from rightmost position)
def ca_broadcast_last : CellAutomaton α？ α？ := {
  Q := α？
  δ := fun _left cur right => right.or cur
  embed := id
  project := id
}

lemma ca_broadcast_last_trace_rt (w : Word α) :
    ca_broadcast_last.trace_rt w = List.replicate w.length w.getLast? := by
  cases w with
  | nil => simp [CellAutomaton.trace_rt]
  | cons a w' =>
    apply List.ext_getElem (by simp [CellAutomaton.trace_rt])
    intro i h_i _
    simp only [CellAutomaton.trace_rt] at h_i
    simp only [CellAutomaton.trace_rt, List.getElem_replicate,
               List.getElem_map, List.getElem_range]
    unfold CellAutomaton.trace
    -- At step i+1, position 0 has received the last element from the right
    -- If i+1 >= w.length, then position 0 has seen the entire word
    sorry

def ca_with_last : CArtTransducer α (α × α？) :=
  ca_zip (ca_trace_id_word α) ca_broadcast_last

def ts_annotate_last : TwoStageAdvice α (α × α？) := {
  β := α × α？
  C := ca_with_last
  M := M_id (α × α？)
}

theorem annotate_last_is_two_stage : Advice.annotate_with_last.is_two_stage_advice (α := α) := by
  use ts_annotate_last
  apply advice_eq_iff
  funext w
  simp only [TwoStageAdvice.advice, ts_annotate_last, Function.comp_apply, M_id_scanr_eq, id_eq,
             ca_with_last, ca_zip_trace_rt, ca_trace_id_scan_temporal]
  rw [ca_broadcast_last_trace_rt]
  simp only [Advice.annotate_with_last]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

end CellularAutomatas
