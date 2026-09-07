import CellularAutomatas.proofs.advice_theory.compose_trace_rt.decompress_triple

namespace CellularAutomatas

open CellAutomaton

/-- Sample a triple-valued computation on a fixed wall-clock phase. Payload
correctness can be proved only after catch-up; the pulse rhythm is unconditional. -/
structure PeriodicTripleReadout where
  {α β : Type}
  [alphabetα : Alphabet α]
  [alphabetβ : Alphabet β]
  source : CellAutomaton α (Fin 3 → β)
  offset : ℕ

attribute [instance] PeriodicTripleReadout.alphabetα
attribute [instance] PeriodicTripleReadout.alphabetβ

namespace PeriodicTripleReadout

variable (e : PeriodicTripleReadout)

def C : CellAutomaton e.α (Option (Fin 3 → e.β)) where
  Q := e.source.Q × Fin 3
  δ := fun left center right =>
    (e.source.δ left.1 center.1 right.1, center.2 + 1)
  embed := fun a => (e.source.embed a, 0)
  project := fun state =>
    if state.2.val = e.offset % 3 then some (e.source.project state.1) else none

theorem state_spec (c : Config e.α) (t : ℕ) (p : ℤ) :
    e.C.nextt ⦋c⦌ t p =
      (e.source.nextt ⦋c⦌ t p, ⟨t % 3, Nat.mod_lt _ (by decide)⟩) := by
  induction t generalizing p with
  | zero =>
    show e.C.embed (c p) = (e.source.embed (c p), (0 : Fin 3))
    rfl
  | succ t ih =>
    show e.C.nextt ⦋c⦌ (t + 1) p =
      (e.source.nextt ⦋c⦌ (t + 1) p,
        ⟨(t + 1) % 3, Nat.mod_lt _ (by decide)⟩)
    simp only [CellAutomaton.nextt_succ, CellAutomaton.next]
    rw [ih (p - 1), ih p, ih (p + 1)]
    simp only [C]
    apply Prod.ext
    · show e.source.δ _ _ _ = e.source.δ _ _ _
      rfl
    · apply Fin.ext
      show (t % 3 + 1) % 3 = (t + 1) % 3
      omega

theorem comp_spec (c : Config e.α) (t : ℕ) (p : ℤ) :
    e.C.comp ⦋c⦌ t p =
      if t % 3 = e.offset % 3 then some (e.source.comp ⦋c⦌ t p) else none := by
  show e.C.project (e.C.nextt ⦋c⦌ t p) = _
  rw [e.state_spec]
  simp [C, CellAutomaton.comp_unfold, CellAutomaton.project_config]

theorem trace_at_sample (c : Config e.α) (j : ℕ) :
    e.C.trace c (3 * j + e.offset) =
      some (e.source.trace c (3 * j + e.offset)) := by
  show e.C.comp ⦋c⦌ (3 * j + e.offset) 0 = _
  rw [e.comp_spec]
  have hphase : (3 * j + e.offset) % 3 = e.offset % 3 := by omega
  rw [if_pos hphase]
  rfl

def decompressor : DecompressTriple where
  C_orig := e.C

theorem rhythm (c : Config e.α) : e.decompressor.h_cond c e.offset := by
  intro t
  change ((e.C.trace c (t + e.offset)).isSome == (t % 3 == 0))
  unfold CellAutomaton.trace
  rw [e.comp_spec]
  by_cases h : t % 3 = 0
  · show (if (t + e.offset) % 3 = e.offset % 3 then
        some (e.source.comp ⦋c⦌ (t + e.offset) 0) else none).isSome ==
      (t % 3 == 0)
    have hphase : (t + e.offset) % 3 = e.offset % 3 := by omega
    simp [hphase, h]
  · show (if (t + e.offset) % 3 = e.offset % 3 then
        some (e.source.comp ⦋c⦌ (t + e.offset) 0) else none).isSome ==
      (t % 3 == 0)
    have hphase : (t + e.offset) % 3 ≠ e.offset % 3 := by omega
    simp [hphase, h]

theorem unpack_spec (c : Config e.α) (hoffset : 0 < e.offset)
    (j : ℕ) (r : Fin 3) :
    e.decompressor.C.trace c (3 * j + r + e.offset) =
      e.source.trace c (3 * j + e.offset) r := by
  rw [e.decompressor.spec2 c (e.rhythm c) hoffset j r]
  change (e.C.trace c (3 * j + e.offset)).get _ r = _
  have hsample := e.trace_at_sample c j
  have hvalid : (e.C.trace c (3 * j + e.offset)).isSome = true := by
    rw [hsample]
    rfl
  exact congrFun (Option.some.inj ((Option.some_get hvalid).trans hsample)) r

/-- The accelerated trace wrapper exposes original times `3*a+r` in its
generation `a+1`. Sampling and unpacking add only `offset+3` physical ticks. -/
theorem decode_packet (c : Config e.α) (hoffset : 0 < e.offset)
    (a : ℕ) (r : Fin 3) (packet : Fin 3 → e.β)
    (hpacket : e.source.trace c (3 * (a + 1) + e.offset) = packet) :
    e.decompressor.C.trace c (3 * a + r + e.offset + 3) = packet r := by
  calc
    e.decompressor.C.trace c (3 * a + r + e.offset + 3)
        = e.decompressor.C.trace c (3 * (a + 1) + r + e.offset) := by
          congr 1
          omega
    _ = e.source.trace c (3 * (a + 1) + e.offset) r :=
      e.unpack_spec c hoffset (a + 1) r
    _ = packet r := congrFun hpacket r

end PeriodicTripleReadout

end CellularAutomatas
