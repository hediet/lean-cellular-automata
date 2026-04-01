import CellularAutomatas.defs
import CellularAutomatas.proofs.basic

namespace CellularAutomatas

open CellAutomaton

/--
Mirror config: places `(w[i], true)` at position i ∈ [0, |w|),
`(w[i], false)` at position i - |w| for i ∈ [0, |w|),
and `(none, false)` elsewhere.

The true-tagged region occupies positions [0, n), the false-tagged region
occupies positions [-n, 0), both containing the same word w.
-/
def mirror_config {α : Type} (w : Word α) : Config (α？ × Bool) :=
  fun p =>
    if h : 0 ≤ p ∧ p < w.length then
      (some w[p.toNat], true)
    else if h2 : -w.length ≤ p ∧ p < 0 then
      (some w[(w.length + p).toNat], false)
    else
      (none, false)

/--
Given a CA C over the tagged alphabet (α？ × Bool), constructs a CA that runs
on plain α？ and simulates C running on mirror_config.

At each position i, the state tracks:
- fwd: what C computes at mirror_config position i (true-tagged region)
- bwd: what C computes at mirror_config position i - n (false-tagged region)

The simulation is exact when C treats cross-tagged neighbors as border
(e.g., CAs constructed via mirrorCA).
-/
def CellAutomaton.mirrorConfigCA (C : CellAutomaton (α？ × Bool) β) : CellAutomaton α？ (β × β) :=
  {
    Q := C.Q × C.Q
    δ := fun (l_fwd, l_bwd) (c_fwd, c_bwd) (r_fwd, r_bwd) =>
      (C.δ l_fwd c_fwd r_fwd, C.δ l_bwd c_bwd r_bwd)
    embed := fun a => (C.embed (a, true), C.embed (a, false))
    project := fun (q_fwd, q_bwd) => (C.project q_fwd, C.project q_bwd)
  }

namespace CellAutomaton.mirrorConfigCA

  variable {α β : Type} [Alphabet α] (C : CellAutomaton (α？ × Bool) β)

  -- Helper: mirror_config at position i in the true region
  omit [Alphabet α] in
  @[simp]
  lemma mirror_config_true_region (w : Word α) (i : ℤ) (hi : 0 ≤ i) (hi2 : i < w.length) :
      mirror_config w i = (some w[i.toNat], true) := by
    unfold mirror_config
    have h : 0 ≤ i ∧ i < w.length := ⟨hi, hi2⟩
    simp only [dif_pos h]

  -- Helper: mirror_config at position i - n in the false region
  omit [Alphabet α] in
  @[simp]
  lemma mirror_config_false_region (w : Word α) (i : ℤ) (hi : 0 ≤ i) (hi2 : i < w.length) :
      mirror_config w (i - w.length) = (some w[i.toNat], false) := by
    unfold mirror_config
    have h1 : ¬(0 ≤ i - ↑w.length ∧ i - ↑w.length < ↑w.length) := by omega
    have h2 : -↑w.length ≤ i - ↑w.length ∧ i - ↑w.length < 0 := by omega
    simp only [dif_neg h1, dif_pos h2]
    have idx_eq : (↑w.length + (i - ↑w.length)).toNat = i.toNat := by omega
    simp only [idx_eq]

  -- Helper: mirror_config outside both regions
  omit [Alphabet α] in
  @[simp]
  lemma mirror_config_outside (w : Word α) (i : ℤ)
      (h1 : ¬(0 ≤ i ∧ i < w.length)) (h2 : ¬(-↑w.length ≤ i ∧ i < 0)) :
      mirror_config w i = (none, false) := by
    unfold mirror_config
    simp only [dif_neg h1, dif_neg h2]

  -- Helper: embed_config outside word range
  omit [Alphabet α] in
  lemma embed_config_outside (w : Word α) (i : ℤ) (h : ¬(0 ≤ i ∧ i < w.length)) :
      C.mirrorConfigCA.embed_config (word_to_config w) i
        = (C.embed (none, true), C.embed (none, false)) := by
    simp only [embed_config, mirrorConfigCA, word_to_config]
    simp only [dif_neg h]

  /--
  **State-level correspondence (interior)**: For strictly interior positions,
  the mirrorConfigCA state equals the pair of C states at the two mirror positions.
  -/
  theorem nextt_eq_interior (w : Word α) (t : ℕ) (i : ℤ)
      (ht : t < i) (ht2 : t < w.length - 1 - i) :
      C.mirrorConfigCA.nextt ⦋w⦌ t i
        = (C.nextt ⦋mirror_config w⦌ t i, C.nextt ⦋mirror_config w⦌ t (i - w.length)) := by
    have hi : 0 ≤ i := by omega
    have hi2 : i < w.length := by omega
    induction t generalizing i with
    | zero =>
      -- Base case: initial embedding
      simp only [nextt_zero, embed_config, mirrorConfigCA, word_to_config]
      have h_range : 0 ≤ i ∧ i < w.length := ⟨hi, hi2⟩
      simp only [dif_pos h_range]
      simp only [mirror_config_true_region w i hi hi2, mirror_config_false_region w i hi hi2]

    | succ t ih =>
      -- Set up bounds for neighbors
      have hi_m1 : 0 ≤ i - 1 := by omega
      have hi2_m1 : i - 1 < w.length := by omega
      have ht_m1 : t < i - 1 := by omega
      have ht2_m1 : t < w.length - 1 - (i - 1) := by omega

      have hi_p1 : 0 ≤ i + 1 := by omega
      have hi2_p1 : i + 1 < w.length := by omega
      have ht_p1 : t < i + 1 := by omega
      have ht2_p1 : t < w.length - 1 - (i + 1) := by omega

      have ht_i : t < i := by omega
      have ht2_i : t < w.length - 1 - i := by omega

      calc C.mirrorConfigCA.nextt ⦋w⦌ (t + 1) i
          = C.mirrorConfigCA.next (C.mirrorConfigCA.nextt ⦋w⦌ t) i := by rw [nextt_succ]
        _ = (C.δ (C.mirrorConfigCA.nextt ⦋w⦌ t (i - 1)).1
               (C.mirrorConfigCA.nextt ⦋w⦌ t i).1
               (C.mirrorConfigCA.nextt ⦋w⦌ t (i + 1)).1,
             C.δ (C.mirrorConfigCA.nextt ⦋w⦌ t (i - 1)).2
               (C.mirrorConfigCA.nextt ⦋w⦌ t i).2
               (C.mirrorConfigCA.nextt ⦋w⦌ t (i + 1)).2) := by simp only [next, mirrorConfigCA]
        _ = (C.δ (C.nextt ⦋mirror_config w⦌ t (i - 1))
               (C.nextt ⦋mirror_config w⦌ t i)
               (C.nextt ⦋mirror_config w⦌ t (i + 1)),
             C.δ (C.nextt ⦋mirror_config w⦌ t (i - 1 - w.length))
               (C.nextt ⦋mirror_config w⦌ t (i - w.length))
               (C.nextt ⦋mirror_config w⦌ t (i + 1 - w.length))) := by
          rw [ih (i - 1) ht_m1 ht2_m1 hi_m1 hi2_m1,
              ih i ht_i ht2_i hi hi2,
              ih (i + 1) ht_p1 ht2_p1 hi_p1 hi2_p1]
        _ = (C.next (C.nextt ⦋mirror_config w⦌ t) i,
             C.next (C.nextt ⦋mirror_config w⦌ t) (i - w.length)) := by
          simp only [next]; ring_nf
        _ = (C.nextt ⦋mirror_config w⦌ (t + 1) i,
             C.nextt ⦋mirror_config w⦌ (t + 1) (i - w.length)) := by
          simp only [← nextt_succ]

  /--
  **Mirror spec (interior)**: For positions strictly inside the word where
  neighbors stay in range throughout the computation, mirrorConfigCA simulates
  C on mirror_config.
  -/
  theorem spec_interior (w : Word α) (t : ℕ) (i : ℤ)
      (ht : t < i) (ht2 : t < w.length - 1 - i) :
      C.mirrorConfigCA.comp ⦋w⦌ t i
        = (C.comp ⦋mirror_config w⦌ t i, C.comp ⦋mirror_config w⦌ t (i - w.length)) := by
    unfold comp project_config
    simp only [Function.comp_apply]
    rw [nextt_eq_interior C w t i ht ht2]
    simp only [mirrorConfigCA]

end CellAutomaton.mirrorConfigCA

end CellularAutomatas
