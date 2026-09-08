import CellularAutomatas.proofs.advice_theory.marked_prefix.consumer_normalization

namespace CellularAutomatas.MarkedPrefix.LT

variable {α β : Type} [Alphabet α] [Alphabet β]

abbrev packedProducer (q : ℕ) [NeZero q] (C : CellAutomaton (Option α) β) :
    SpeedupKx where
  k := q
  α := Option α
  β := β
  C_orig := C

omit [Alphabet α] in
/-- Exact packing leaves no partial block at the right producer boundary. -/
theorem compress_word_exterior (q : ℕ) [NeZero q] (w : Word α) (M : ℕ)
    (hlength : w.length = q * M) (p : ℤ)
    (hp : p < 0 ∨ (M : ℤ) ≤ p) :
    SpeedupKx.compress q (word_to_config w) p = fun _ => none := by
  funext i
  change word_to_config w (p * q + (i : ℤ)) = none
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hi : (0 : ℤ) ≤ i ∧ (i : ℤ) < q := by
    constructor
    · exact_mod_cast (Nat.zero_le i.val)
    · exact_mod_cast i.isLt
  have hsize : (w.length : ℤ) = (q : ℤ) * M := by exact_mod_cast hlength
  have hout : ¬(0 ≤ p * q + (i : ℤ) ∧
      p * q + (i : ℤ) < (w.length : ℤ)) := by
    rcases hp with hleft | hright
    · have hleft' : p ≤ -1 := by omega
      have hmul := mul_le_mul_of_nonneg_right hleft' hq.le
      omega
    · have hmul := mul_le_mul_of_nonneg_right hright hq.le
      rw [mul_comm (M : ℤ) (q : ℤ), ← hsize] at hmul
      omega
  simp [word_to_config, hout]

/-- Both exterior half-lines stay at the literal packed dead state. This is
what allows the producer to omit both exterior clock dependencies. -/
theorem packedProducer_nextt_exterior (q : ℕ) [NeZero q]
    (C : CellAutomaton (Option α) β) (hdead : C.dead C.border)
    (w : Word α) (M : ℕ) (hlength : w.length = q * M)
    (t : ℕ) (p : ℤ) (hp : p < 0 ∨ (M : ℤ) ≤ p) :
    (packedProducer q C).C.nextt
        ⦋SpeedupKx.compress q (word_to_config w)⦌ t p =
      (packedProducer q C).C.embed (fun _ => none) := by
  apply nextt_eq_of_dead
  · exact speedupKx_embed_const_dead (packedProducer q C) none hdead
  · change
      (packedProducer q C).C.embed
          (SpeedupKx.compress q (word_to_config w) p) =
        (packedProducer q C).C.embed (fun _ => none)
    rw [compress_word_exterior q w M hlength p hp]

end CellularAutomatas.MarkedPrefix.LT
