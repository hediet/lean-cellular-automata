import CellularAutomatas.proofs.advice_theory.marked_prefix.packet_join
import CellularAutomatas.proofs.advice_theory.sync_time_constructible
import CellularAutomatas.proofs.constructions.basic_ca_id
import CellularAutomatas.proofs.constructions.basic_compose_k_steps
import CellularAutomatas.proofs.constructions.border_dead

namespace CellularAutomatas.MarkedPrefix.LT.StableTransform

open CellAutomaton

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]

/-- A synchronous timer for the exact time `coefficient * n`. -/
def timer : (coefficient : ℕ) →
    SyncTimeConstructibleInner (fun n => coefficient * n)
  | 0 => by
      simpa using Const 0
  | coefficient + 1 => by
      simpa [Nat.succ_mul] using
        (Sum (timer coefficient) IdSync.toInner).toInner

/-- Delay the original LT witness by its linear coefficient. -/
def delayed {F : Advice α Γ} (hF : F.IsLtAdvice) :
    CellAutomaton α？ Γ :=
  (CellAutomaton.idCA (Option α)).composeKSteps hF.witness.C hF.c

/-- The exact `c * n` timer, remapped to the witness input alphabet. -/
def timerTrack {F : Advice α Γ} (hF : F.IsLtAdvice) :
    CellAutomaton α？ Bool :=
  (timer hF.c).timer.map_embed (Option.map (fun _ : α => ()))

private theorem timerTrack_comp {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (t : ℕ) (p : ℤ) :
    (timerTrack hF).comp w t p =
      (timer hF.c).timer.comp (unitWord w.length) t p := by
  rw [CellAutomaton.comp_apply, CellAutomaton.comp_apply]
  change
    (timer hF.c).timer.project
        (((timer hF.c).timer.map_embed
          (Option.map (fun _ : α => ()))).nextt ⦋w⦌ t p) =
      (timer hF.c).timer.project
        ((timer hF.c).timer.nextt ⦋unitWord w.length⦌ t p)
  rw [map_embed_nextt_word]
  have hmap : w.map (fun _ : α => ()) = unitWord w.length := by
    apply List.ext_getElem
    · simp [unitWord]
    · intro i hi₁ hi₂
      simp [unitWord]
  rw [hmap]

/-- The delayed witness is exposed exactly when the `c * n` timer fires. -/
def source {F : Advice α Γ} (hF : F.IsLtAdvice) :
    CellAutomaton α？ (Option Γ) :=
  (delayed hF ⨂ timerTrack hF).map_project fun output =>
    if output.2 then some output.1 else none

/-- The advice symbol at an integer position known to be inside the word. -/
def outputAt (F : Advice α Γ) (w : Word α) (p : ℤ)
    (hp : p ∈ w.range) : Γ :=
  (F w)[p.toNat]'(by
    rw [advice_len]
    have hpos : 0 ≤ p ∧ p < (w.length : ℤ) := by
      simpa only [Word.range, Set.mem_setOf_eq] using hp
    omega)

private theorem witness_at_deadline {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (p : ℤ) (hp : p ∈ w.range) :
    hF.witness.C.comp w (hF.c * (w.length - 1)) p =
      outputAt F w p hp := by
  have hpos : 0 ≤ p ∧ p < (w.length : ℤ) := by
    simpa only [Word.range, Set.mem_setOf_eq] using hp
  have hpnat : p.toNat < w.length := by omega
  have houtput : (F w)[p.toNat]? = some (outputAt F w p hp) :=
    List.getElem?_eq_getElem (by simpa [advice_len] using hpnat)
  rw [hF.witness.spec w, List.getElem?_map,
    List.getElem?_range hpnat] at houtput
  have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hpos.1
  simpa only [Option.map_some, Option.some.injEq, hcast] using houtput

private theorem delayed_at_deadline {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (hw : 0 < w.length) (p : ℤ) (hp : p ∈ w.range) :
    (delayed hF).comp w (hF.c * w.length) p =
      outputAt F w p hp := by
  have hdelay : hF.c * w.length - hF.c =
      hF.c * (w.length - 1) := by
    calc
      hF.c * w.length - hF.c =
          hF.c * w.length - hF.c * 1 := by simp
      _ = hF.c * (w.length - 1) := by
        rw [Nat.mul_sub_left_distrib]
  have hstart : hF.c ≤ hF.c * w.length := by
    have := Nat.mul_le_mul_left hF.c hw
    simpa using this
  rw [delayed, CellAutomaton.composeKSteps_comp,
    CellAutomaton.idCA.comp_spec, if_pos hstart, hdelay]
  exact witness_at_deadline hF w p hp

private theorem source_before {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (t : ℕ) (p : ℤ) (hp : p ∈ w.range)
    (ht : t < hF.c * w.length) :
    (source hF).comp w t p = none := by
  have hpos : 0 ≤ p ∧ p < (w.length : ℤ) := by
    simpa only [Word.range, Set.mem_setOf_eq] using hp
  have htimer := (timer hF.c).no_fire_before
    w.length p t hpos.1 hpos.2 ht
  change (timer hF.c).timer.comp (unitWord w.length) t p = false at htimer
  simp only [source, comp_of_map_project, ca_zip_comp]
  rw [timerTrack_comp, htimer]
  rfl

private theorem source_at_deadline {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (hw : 0 < w.length) (p : ℤ) (hp : p ∈ w.range) :
    (source hF).comp w (hF.c * w.length) p =
      some (outputAt F w p hp) := by
  have hpos : 0 ≤ p ∧ p < (w.length : ℤ) := by
    simpa only [Word.range, Set.mem_setOf_eq] using hp
  have htimer := (timer hF.c).fires_at
    w.length p hpos.1 hpos.2
  change (timer hF.c).timer.comp
    (unitWord w.length) (hF.c * w.length) p = true at htimer
  simp only [source, comp_of_map_project, ca_zip_comp]
  rw [timerTrack_comp, htimer, if_pos rfl,
    delayed_at_deadline hF w hw p hp]

/-- Enough folded workspace to preserve every source cell through `c * n`. -/
def folded {F : Advice α Γ} (hF : F.IsLtAdvice) : DeadBorder where
  c := hF.c + 1
  C_orig := source hF

private theorem folded_before {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (t : ℕ) (p : ℤ) (hp : p ∈ w.range)
    (ht : t < hF.c * w.length) :
    (folded hF).C.comp w t p = none := by
  rw [(folded hF).spec_comp_row w t
    (by
      calc
        t + w.length ≤ hF.c * w.length + w.length :=
          Nat.add_le_add_right (Nat.le_of_lt ht) _
        _ = (hF.c + 1) * w.length := by simp [Nat.add_mul])
    p hp]
  exact source_before hF w t p hp ht

private theorem folded_at_deadline {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (hw : 0 < w.length) (p : ℤ) (hp : p ∈ w.range) :
    (folded hF).C.comp w (hF.c * w.length) p =
      some (outputAt F w p hp) := by
  rw [(folded hF).spec_comp_row w (hF.c * w.length)
    (by
      change hF.c * w.length + w.length ≤
        (hF.c + 1) * w.length
      rw [Nat.add_mul, one_mul]) p hp]
  exact source_at_deadline hF w hw p hp

private theorem source_project_border_none {F : Advice α Γ}
    (hF : F.IsLtAdvice) :
    (source hF).project (source hF).border = none := by
  have houter : ¬(0 ≤ (0 : ℤ) ∧ (0 : ℤ) < (0 : ℕ)) := by omega
  have htimer := (timer hF.c).no_outer_fire 0 0 0 houter
  have htrack : (timerTrack hF).comp ([] : Word α) 0 0 = false := by
    rw [timerTrack_comp]
    exact htimer
  change (source hF).comp ([] : Word α) 0 0 = none
  simp only [source, comp_of_map_project, ca_zip_comp]
  rw [htrack]
  rfl

private theorem folded_project_border_none {F : Advice α Γ}
    (hF : F.IsLtAdvice) :
    (folded hF).C.project (folded hF).C.border = none := by
  change (source hF).project (source hF).border = none
  exact source_project_border_none hF

private theorem folded_outside {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (t : ℕ) (p : ℤ) (hp : p ∉ w.range) :
    (folded hF).C.comp w t p = none := by
  rw [CellAutomaton.comp_apply,
    dead_border_prop (folded hF).C (folded hF).spec_left_border_dead
      w t p hp]
  exact folded_project_border_none hF

/-- A local first-output latch. Its controller keeps running, while
`PacketJoin.retain` makes the first observed payload permanent. -/
def latch {ι β : Type} [Alphabet β]
    (source : CellAutomaton ι (Option β)) :
    CellAutomaton ι (Option β) where
  Q := source.Q × Option β
  δ := fun left center right =>
    let next := source.δ left.1 center.1 right.1
    (next, PacketJoin.retain center.2 (source.project next))
  embed := fun input =>
    let controller := source.embed input
    (controller, source.project controller)
  project := Prod.snd

private theorem latch_controller {ι β : Type} [Alphabet β]
    (source : CellAutomaton ι (Option β)) (input : Config ι)
    (t : ℕ) (p : ℤ) :
    ((latch source).nextt ⦋input⦌ t p).1 =
      source.nextt ⦋input⦌ t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ,
        CellAutomaton.next_apply, CellAutomaton.next_apply]
      change source.δ _ _ _ = source.δ _ _ _
      rw [ih, ih, ih]

private theorem latch_succ {ι β : Type} [Alphabet β]
    (source : CellAutomaton ι (Option β)) (input : Config ι)
    (t : ℕ) (p : ℤ) :
    ((latch source).nextt ⦋input⦌ (t + 1) p).2 =
      PacketJoin.retain
        ((latch source).nextt ⦋input⦌ t p).2
        (source.comp ⦋input⦌ (t + 1) p) := by
  rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
  change
    PacketJoin.retain ((latch source).nextt ⦋input⦌ t p).2
      (source.project (source.δ
        ((latch source).nextt ⦋input⦌ t (p - 1)).1
        ((latch source).nextt ⦋input⦌ t p).1
        ((latch source).nextt ⦋input⦌ t (p + 1)).1)) =
      PacketJoin.retain ((latch source).nextt ⦋input⦌ t p).2
        (source.comp ⦋input⦌ (t + 1) p)
  congr 1
  rw [CellAutomaton.comp_apply, CellAutomaton.nextt_succ,
    CellAutomaton.next_apply, latch_controller, latch_controller,
    latch_controller]

private theorem latch_spec {ι β : Type} [Alphabet β]
    (source : CellAutomaton ι (Option β)) (input : Config ι)
    (p : ℤ) (deadline : ℕ) (value : β)
    (hbefore : ∀ t, t < deadline → source.comp ⦋input⦌ t p = none)
    (hat : source.comp ⦋input⦌ deadline p = some value)
    (t : ℕ) :
    (latch source).comp ⦋input⦌ t p =
      if deadline ≤ t then some value else none := by
  rw [CellAutomaton.comp_apply]
  change ((latch source).nextt ⦋input⦌ t p).2 =
    if deadline ≤ t then some value else none
  induction t with
  | zero =>
      change source.comp ⦋input⦌ 0 p =
        if deadline ≤ 0 then some value else none
      by_cases hzero : deadline = 0
      · simpa [hzero] using hat
      · simp [hzero, hbefore 0 (Nat.pos_of_ne_zero hzero)]
  | succ t ih =>
      rw [latch_succ, ih]
      by_cases hseen : deadline ≤ t
      · rw [if_pos hseen,
          if_pos (le_trans hseen (Nat.le_succ t))]
        rfl
      · by_cases hnow : t + 1 = deadline
        · rw [hnow, hat]
          simp [hseen, PacketJoin.retain]
        · have hfuture : t + 1 < deadline := by omega
          rw [hbefore (t + 1) hfuture]
          rw [if_neg hseen, if_neg (by omega : ¬deadline ≤ t + 1)]
          rfl

private theorem latch_none {ι β : Type} [Alphabet β]
    (source : CellAutomaton ι (Option β)) (input : Config ι)
    (p : ℤ) (hsource : ∀ t, source.comp ⦋input⦌ t p = none)
    (t : ℕ) :
    (latch source).comp ⦋input⦌ t p = none := by
  rw [CellAutomaton.comp_apply]
  change ((latch source).nextt ⦋input⦌ t p).2 = none
  induction t with
  | zero =>
      change source.comp ⦋input⦌ 0 p = none
      exact hsource 0
  | succ t ih =>
      rw [latch_succ, ih, hsource]
      rfl

private theorem latch_dead {ι β : Type} [Alphabet β]
    (source : CellAutomaton (Option ι) (Option β))
    (hdead : source.dead source.border)
    (hproject : source.project source.border = none) :
    (latch source).dead (latch source).border := by
  have hborder : (latch source).border = (source.border, none) := by
    change (source.border, source.project source.border) =
      (source.border, none)
    rw [hproject]
  unfold CellAutomaton.dead
  intro left center right hcenter
  rw [hborder] at hcenter ⊢
  subst center
  change
    (source.δ left.1 source.border right.1,
      PacketJoin.retain none
        (source.project (source.δ left.1 source.border right.1))) =
      (source.border, none)
  rw [hdead left.1 source.border right.1 rfl, hproject]
  rfl

/-- Stable finite-strip normalization of an LT advice witness. -/
def C {F : Advice α Γ} (hF : F.IsLtAdvice) :
    CellAutomaton α？ (Option Γ) :=
  latch (folded hF).C

/-- Every interior cell is silent before `c * |w|` and permanently exposes
its advice symbol from that exact time onward. -/
theorem spec {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (hw : 0 < w.length) (t : ℕ)
    (p : ℤ) (hp : p ∈ w.range) :
    (C hF).comp w t p =
      if hF.c * w.length ≤ t
      then some (outputAt F w p hp)
      else none := by
  apply latch_spec (folded hF).C (word_to_config w) p
    (hF.c * w.length) (outputAt F w p hp)
  · intro s hs
    exact folded_before hF w s p hp hs
  · exact folded_at_deadline hF w hw p hp

/-- Exterior positions remain permanently absent. -/
theorem outside {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (t : ℕ) (p : ℤ) (hp : p ∉ w.range) :
    (C hF).comp w t p = none := by
  apply latch_none (folded hF).C (word_to_config w) p
  intro s
  exact folded_outside hF w s p hp

/-- The stable CA's border projects to absence. -/
theorem border_project {F : Advice α Γ} (hF : F.IsLtAdvice) :
    (C hF).project (C hF).border = none := by
  change (folded hF).C.project (folded hF).C.border = none
  exact folded_project_border_none hF

/-- The normalized finite-strip CA has an unconditionally dead border. -/
theorem border_dead {F : Advice α Γ} (hF : F.IsLtAdvice) :
    (C hF).dead (C hF).border := by
  exact latch_dead (folded hF).C (folded hF).spec_left_border_dead
    (folded_project_border_none hF)

/-- The stable normalization uses the original coefficient, including when it
is zero; no additive startup constant is introduced. -/
theorem stable_c {F : Advice α Γ} (hF : F.IsLtAdvice)
    (w : Word α) (hw : 0 < w.length) (t : ℕ)
    (p : ℤ) (hp : p ∈ w.range) :
    (C hF).comp w t p =
      if hF.c * w.length ≤ t
      then some (outputAt F w p hp)
      else none :=
  spec hF w hw t p hp

end CellularAutomatas.MarkedPrefix.LT.StableTransform
