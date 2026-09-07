import CellularAutomatas.proofs.constructions.border_dead
import CellularAutomatas.proofs.constructions.trace_kx

namespace CellularAutomatas.MarkedPrefix

open CellAutomaton

/-- Normalize a consumer using a one-cell folding radius. -/
abbrev normalizedConsumer {δ β : Type} [Alphabet δ]
    (C : CellAutomaton (Option δ) β) : DeadBorder where
  c := 1
  C_orig := C

/-- Boundary normalization preserves the consumer's final real-time trace on
every nonempty word. -/
theorem normalizedConsumer_trace_final
    {δ β : Type} [Alphabet δ] (C : CellAutomaton (Option δ) β)
    (v : Word δ) (hv : 0 < v.length) :
    (normalizedConsumer C).C.trace (word_to_config v) (v.length - 1) =
      C.trace (word_to_config v) (v.length - 1) := by
  apply (normalizedConsumer C).spec_comp_trace
  change v.length - 1 < 1 * v.length
  omega

/-- The normalized consumer's input border is an absorbing state. -/
theorem normalizedConsumer_border_dead
    {δ β : Type} [Alphabet δ] (C : CellAutomaton (Option δ) β) :
    (normalizedConsumer C).C.dead (normalizedConsumer C).C.border :=
  (normalizedConsumer C).spec_left_border_dead

/-- A dead state remains unchanged at its position under every iterate,
regardless of the surrounding configuration. -/
lemma nextt_eq_of_dead
    {α β : Type} (C : CellAutomaton α β) (q : C.Q)
    (hq : C.dead q) (c : Config C.Q) (t : ℕ) (p : ℤ)
    (hp : c p = q) :
    C.nextt c t p = q := by
  induction t with
  | zero =>
      simpa using hp
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.next]
      exact hq _ _ _ ih

/-- If an embedded original state is dead, its constant embedded history is
dead in `TraceKx`. -/
lemma traceKx_embed_dead (e : TraceKx) (x : e.α)
    (hx : e.C_orig.dead (e.C_orig.embed x)) :
    e.C.dead (e.C.embed x) := by
  unfold CellAutomaton.dead TraceKx.C
  intro left center right hcenter
  subst center
  funext i
  simp only [Fin.snoc]
  split
  · rfl
  · exact hx _ _ _ rfl

/-- If an embedded original state is dead, the constant input block embeds to
a dead state in `SpeedupKx`. -/
lemma speedupKx_embed_const_dead (e : SpeedupKx) (x : e.α)
    (hx : e.C_orig.dead (e.C_orig.embed x)) :
    e.C.dead (e.C.embed (fun _ => x)) := by
  unfold CellAutomaton.dead SpeedupKx.C
  intro left center right hcenter
  subst center
  funext i
  unfold SpeedupKx.to_local_config
  apply nextt_eq_of_dead e.C_orig (e.C_orig.embed x) hx
  unfold SpeedupKx.local_config
  have hk : 0 < e.k := NeZero.pos e.k
  have hiLeft : ¬(i : ℤ) ≤ -(e.k : ℤ) := by omega
  have hiNonneg : ¬(i : ℤ) < 0 := by omega
  have hiRight : (i : ℤ) < e.k := by exact_mod_cast i.isLt
  simp [hiLeft, hiNonneg, hiRight]

/-- Changing only an automaton's projection preserves its dead states. -/
lemma mapProject_dead
    {α β γ : Type} (C : CellAutomaton α β) (f : β → γ) (q : C.Q)
    (hq : C.dead q) :
    (C.map_project f).dead q := by
  exact hq

/-- `SpeedupAndTraceKx` transports an embedded dead state through both its
history layer and its compressed block layer. -/
lemma speedupAndTraceKx_embed_const_dead
    (e : SpeedupAndTraceKx) (x : e.α)
    (hx : e.C_orig.dead (e.C_orig.embed x)) :
    e.C.dead (e.C.embed (fun _ => x)) := by
  unfold SpeedupAndTraceKx.C
  apply mapProject_dead
  apply speedupKx_embed_const_dead
  apply traceKx_embed_dead
  exact hx

/-- The threefold speedup-and-trace wrapper around the normalized consumer. -/
abbrev normalizedSpeedupAndTrace3
    {δ β : Type} [Alphabet δ] [Alphabet β]
    (C : CellAutomaton (Option δ) β) : SpeedupAndTraceKx where
  k := 3
  α := Option δ
  β := β
  C_orig := (normalizedConsumer C).C

/-- The state obtained by embedding an all-border input packet. -/
def qDead
    {δ β : Type} [Alphabet δ] [Alphabet β]
    (C : CellAutomaton (Option δ) β) :
    (normalizedSpeedupAndTrace3 C).C.Q :=
  (normalizedSpeedupAndTrace3 C).C.embed (fun _ => none)

/-- The all-border packet is dead in the accelerated normalized consumer. -/
theorem qDead_dead
    {δ β : Type} [Alphabet δ] [Alphabet β]
    (C : CellAutomaton (Option δ) β) :
    (normalizedSpeedupAndTrace3 C).C.dead (qDead C) := by
  unfold qDead
  apply speedupAndTraceKx_embed_const_dead
  simpa only [CellAutomaton.border] using normalizedConsumer_border_dead C

/-- Every negative physical block starts at the all-border packet and remains
there at every generation. -/
theorem normalizedSpeedupAndTrace3_nextt_negative
    {δ β : Type} [Alphabet δ] [Alphabet β]
    (C : CellAutomaton (Option δ) β)
    (v : Word δ) (t : ℕ) (p : ℤ) (hp : p < 0) :
    (normalizedSpeedupAndTrace3 C).C.nextt
        ⦋SpeedupKx.compress 3 (word_to_config v)⦌ t p =
      qDead C := by
  apply nextt_eq_of_dead
    (normalizedSpeedupAndTrace3 C).C (qDead C) (qDead_dead C)
  change (normalizedSpeedupAndTrace3 C).C.embed
      ((SpeedupKx.compress 3 (word_to_config v)) p) =
    (normalizedSpeedupAndTrace3 C).C.embed (fun _ => none)
  apply congrArg
  funext i
  unfold SpeedupKx.compress word_to_config
  have hi : (i : ℤ) < 3 := by exact_mod_cast i.isLt
  have hnegative : p * 3 + (i : ℤ) < 0 := by omega
  simp [hnegative]

end CellularAutomatas.MarkedPrefix
