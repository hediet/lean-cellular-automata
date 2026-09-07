import CellularAutomatas.proofs.advice_theory.marked_prefix.lifted_packets
import CellularAutomatas.proofs.advice_theory.marked_prefix.marked_initialization
import CellularAutomatas.proofs.advice_theory.marked_prefix.raw_pack_three
import CellularAutomatas.proofs.advice_theory.marked_prefix.reversal_packets

namespace CellularAutomatas.MarkedPrefix.ReversalInitialization

open CellAutomaton

variable {σ α : Type} [Alphabet σ] [Alphabet α]

/-- The actual controller alphabet retains the ordinary input symbol and the
single `middle_exp` marker. -/
def controllerWord (w : Word σ) : Word (σ × Bool) :=
  (Advice.middle_exp σ).annotate w

/-- Raw three-cell packets preserve the complete `σ` input and ignore only
the controller marker. -/
def rawPackets (σ : Type) [Alphabet σ] :
    CellAutomaton (Option (σ × Bool)) (Option (Fin 3 → Option σ)) :=
  (RawPackThree.C σ).map_embed (Option.map Prod.fst)

/-- Reversed-prefix packets project the ordinary input through `π`, while
retaining the controller marker used by `ReversalPackets.P`. -/
def advicePackets (π : σ → α) :
    CellAutomaton (Option (σ × Bool)) (Option (Fin 3 → Option α)) :=
  (ReversalPackets.P α).map_embed
    (Option.map fun pair => (π pair.1, pair.2))

/-- The concrete joined initialization source. -/
def P (π : σ → α) :
    CellAutomaton (Option (σ × Bool))
      (Option (Fin 3 → Option (σ × Option α))) :=
  MarkedInitialization.C (rawPackets σ) (advicePackets π)

private theorem mapEmbed_comp_word
    {ι κ γ : Type} (C : CellAutomaton (Option κ) γ)
    (f : ι → κ) (w : Word ι) (t : ℕ) (p : ℤ) :
    (C.map_embed (Option.map f)).comp w t p =
      C.comp (w.map f) t p := by
  change C.project
      ((C.map_embed (Option.map f)).nextt ⦋w⦌ t p) =
    C.project (C.nextt ⦋w.map f⦌ t p)
  exact congrArg C.project (map_embed_nextt_word C f w t p)

omit [Alphabet σ] in
private theorem controllerWord_eq_markedWord
    (w : Word σ) (hn : 2 ≤ w.length) :
    controllerWord w =
      ReversalPackets.markedWord w (dyadicSelector w.length - 1) := by
  exact middle_exp_annotate_eq_mapIdx w hn

omit [Alphabet σ] in
private theorem controllerWord_map_fst
    (w : Word σ) (hn : 2 ≤ w.length) :
    (controllerWord w).map Prod.fst = w := by
  rw [controllerWord_eq_markedWord w hn]
  exact ReversalPackets.markedWord_map_fst w _

omit [Alphabet α] in
private theorem controllerWord_map_projection
    (π : σ → α) (w : Word σ) (hn : 2 ≤ w.length) :
    (controllerWord w).map (fun pair => (π pair.1, pair.2)) =
      ReversalPackets.markedWord (w.map π)
        (dyadicSelector w.length - 1) := by
  change ((Advice.middle_exp σ).annotate w).map
      (fun pair => (π pair.1, pair.2)) = _
  rw [← middle_exp_lift_eq π]
  rw [annotate_lift_map]
  rw [middle_exp_annotate_eq_mapIdx (w.map π) (by simpa using hn)]
  simp only [List.length_map]
  rfl

/-! ## The two concrete source contracts -/

/-- The raw source fires exactly on the right diagonal with startup constant
three, carrying the full unprojected `σ` input packet. -/
theorem rawPackets_spec (w : Word σ) (hn : 2 ≤ w.length)
    (t : ℕ) (p : ℤ) :
    (rawPackets σ).comp (controllerWord w) t p =
      if 0 ≤ p ∧ t = 3 + 2 * p.natAbs then
        some (SpeedupKx.compress 3 (word_to_config w) p)
      else
        none := by
  calc
    (rawPackets σ).comp (controllerWord w) t p =
        (RawPackThree.C σ).comp ((controllerWord w).map Prod.fst) t p :=
      mapEmbed_comp_word (RawPackThree.C σ) Prod.fst (controllerWord w) t p
    _ = (RawPackThree.C σ).comp w t p := by
      rw [controllerWord_map_fst w hn]
    _ = if 0 ≤ p ∧ t = 3 + 2 * p.natAbs then
          some (SpeedupKx.compress 3 (word_to_config w) p)
        else none := by
      rw [RawPackThree.comp_spec w
        (List.ne_nil_of_length_pos (by omega)) t p]
      split_ifs with hp
      · congr 2
        funext r
        unfold SpeedupKx.compress
        congr 1
        ring
      · rfl

/-- The advice source fires exactly on the marker ray.  Its payload is already
in the `adviceBlock` form consumed by `MarkedInitialization`. -/
theorem advicePackets_spec (π : σ → α) (w : Word σ)
    (hn : 2 ≤ w.length) (t p : ℕ) :
    (advicePackets π).comp (controllerWord w) t (p : ℤ) =
      if t =
          3 + Int.natAbs
            ((p : ℤ) - ((dyadicSelector w.length - 1 : ℕ) : ℤ)) then
        some (adviceBlock ((dyadicPrefixReversal α).lift π) none w (p : ℤ))
      else
        none := by
  unfold advicePackets
  rw [mapEmbed_comp_word, controllerWord_map_projection π w hn]
  have hb :
      dyadicSelector w.length - 1 < (w.map π).length := by
    simpa only [List.length_map] using dyadicSelector_pred_lt hn
  rw [ReversalPackets.comp_spec (w.map π)
    (dyadicSelector w.length - 1) hb t p]
  congr 1
  have hpos : 0 < dyadicSelector w.length := dyadicSelector_pos hn
  have hsucc :
      (dyadicSelector w.length - 1) + 1 = dyadicSelector w.length := by
    omega
  rw [hsucc]
  simpa only [dyadicPrefixReversal] using
    congrArg some
      (prefixReversal_adviceBlock_lift
        dyadicSelector π w (p : ℤ)).symm

/-! ## Joined initialization -/

/-- Exact initialized packet stream for the lifted dyadic prefix-reversal
advice.  The statement covers every integer position; negative positions are
silent, while every nonnegative position fires once at the release envelope. -/
theorem comp_spec (π : σ → α) (w : Word σ) (hn : 2 ≤ w.length)
    (t : ℕ) (p : ℤ) :
    (P π).comp (controllerWord w) t p =
      if 0 ≤ p ∧
          t = MarkedPrefixClock.release 3
            (dyadicSelector w.length - 1) p.natAbs then
        some (SpeedupKx.compress 3
          (word_to_config
            (((dyadicPrefixReversal α).lift π).annotate w)) p)
      else
        none := by
  have hraw :
      ∀ (s : ℕ) (q : ℤ),
        (rawPackets σ).comp
            (⦋word_to_config (controllerWord w)⦌) s q =
          if 0 ≤ q ∧ s = 3 + 2 * q.natAbs then
            some (SpeedupKx.compress 3 (word_to_config w) q)
          else none := by
    intro s q
    change (rawPackets σ).comp (controllerWord w) s q = _
    exact rawPackets_spec w hn s q
  have hadvice :
      ∀ (s q : ℕ),
        (advicePackets π).comp
            (⦋word_to_config (controllerWord w)⦌) s (q : ℤ) =
          if s =
              3 + Int.natAbs
                ((q : ℤ) -
                  ((dyadicSelector w.length - 1 : ℕ) : ℤ)) then
            some (adviceBlock
              ((dyadicPrefixReversal α).lift π) none w (q : ℤ))
          else none := by
    intro s q
    change (advicePackets π).comp (controllerWord w) s (q : ℤ) = _
    exact advicePackets_spec π w hn s q
  simpa only [P] using
    MarkedInitialization.comp_spec
      (rawPackets σ) (advicePackets π)
      (word_to_config (controllerWord w))
      w ((dyadicPrefixReversal α).lift π) none
      3 (dyadicSelector w.length - 1)
      hraw hadvice t p

end CellularAutomatas.MarkedPrefix.ReversalInitialization
