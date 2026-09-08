import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.stable_transform
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.packed_exterior
import CellularAutomatas.proofs.advice_theory.marked_prefix.lt.ready_packets

namespace CellularAutomatas.MarkedPrefix.LT.PackedTransform

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

abbrev speedup (q : ℕ) [NeZero q] {F : Advice α Γ} (hF : F.IsLtAdvice) :
    SpeedupKx :=
  packedProducer q (StableTransform.C hF)

/-- An actual accelerated LT producer whose output includes local completion.
The asynchronous wrapper will run this CA, not an assumed row transformer. -/
def C (q : ℕ) [NeZero q] {F : Advice α Γ} (hF : F.IsLtAdvice) :
    CellAutomaton (Fin q → Option α) (Option (Fin q → Γ)) :=
  (speedup q hF).C.map_project readyBlock

def block (q : ℕ) (F : Advice α Γ) (blank : Γ) (w : Word α) (p : ℤ) :
    Fin q → Γ :=
  fun i => (word_to_config (F w) (p * q + (i : ℤ))).getD blank

theorem spec (q : ℕ) [NeZero q] {F : Advice α Γ} (hF : F.IsLtAdvice)
    (blank : Γ) (w : Word α) (M : ℕ) (hM : 0 < M)
    (hlength : w.length = q * M) (k p : ℕ) (hp : p < M) :
    (C q hF).comp ⦋SpeedupKx.compress q (word_to_config w)⦌ k p =
      if hF.c * M ≤ k then some (block q F blank w p) else none := by
  have hq := NeZero.pos q
  have hw : 0 < w.length := by
    rw [hlength]
    exact Nat.mul_pos hq hM
  have hdeadline : hF.c * w.length ≤ q * k ↔ hF.c * M ≤ k := by
    rw [hlength, show hF.c * (q * M) = q * (hF.c * M) by ring]
    exact Nat.mul_le_mul_left_iff hq
  simp only [C, comp_of_map_project]
  rw [(speedup q hF).spec]
  have hslots :
      SpeedupKx.compress q ((StableTransform.C hF).comp w (q * k)) p =
        fun i => if hF.c * M ≤ k
          then some (block q F blank w p i) else none := by
    funext i
    have hindex : p * q + i.val < w.length := by
      rw [hlength, Nat.mul_comm q M]
      have hi := i.isLt
      have hmul := Nat.mul_le_mul_right q (show p + 1 ≤ M by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega
    have hpos : (p : ℤ) * q + (i : ℤ) ∈ w.range := by
      show 0 ≤ (p : ℤ) * q + (i : ℤ) ∧
        (p : ℤ) * q + (i : ℤ) < w.length
      constructor
      · positivity
      · exact_mod_cast hindex
    have hvalue :
        StableTransform.outputAt F w ((p : ℤ) * q + (i : ℤ)) hpos =
          block q F blank w p i := by
      have hbounds : 0 ≤ (p : ℤ) * q + (i : ℤ) ∧
          (p : ℤ) * q + (i : ℤ) < w.length := hpos
      simp only [block, word_to_config, advice_len, dif_pos hbounds,
        Option.getD_some, StableTransform.outputAt]
    change (StableTransform.C hF).comp w (q * k)
      ((p : ℤ) * q + (i : ℤ)) = _
    rw [StableTransform.spec hF w hw (q * k) _ hpos, hvalue]
    simp only [hdeadline]
  rw [hslots]
  by_cases hready : hF.c * M ≤ k
  · simp [hready]
  · simp [hready]

theorem dead (q : ℕ) [NeZero q] {F : Advice α Γ} (hF : F.IsLtAdvice) :
    (C q hF).dead ((C q hF).embed (fun _ => none)) := by
  apply mapProject_dead
  exact speedupKx_embed_const_dead (speedup q hF) none
    (StableTransform.border_dead hF)

theorem project_dead (q : ℕ) [NeZero q] {F : Advice α Γ} (hF : F.IsLtAdvice) :
    (C q hF).project ((C q hF).embed (fun _ => none)) = none := by
  change readyBlock (fun _ : Fin q =>
    (StableTransform.C hF).project (StableTransform.C hF).border) = none
  rw [StableTransform.border_project]
  exact readyBlock_none

theorem nextt_exterior (q : ℕ) [NeZero q] {F : Advice α Γ}
    (hF : F.IsLtAdvice) (w : Word α) (M : ℕ)
    (hlength : w.length = q * M) (k : ℕ) (p : ℤ)
    (hp : p < 0 ∨ (M : ℤ) ≤ p) :
    (C q hF).nextt ⦋SpeedupKx.compress q (word_to_config w)⦌ k p =
      (C q hF).embed (fun _ => none) := by
  exact packedProducer_nextt_exterior q (StableTransform.C hF)
    (StableTransform.border_dead hF) w M hlength k p hp

end CellularAutomatas.MarkedPrefix.LT.PackedTransform
