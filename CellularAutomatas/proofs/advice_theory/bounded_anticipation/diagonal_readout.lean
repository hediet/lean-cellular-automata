import CellularAutomatas.proofs.advice_theory.bounded_anticipation.defs
import CellularAutomatas.proofs.advice_theory.local_horizon.machine
import CellularAutomatas.proofs.advice_theory.compose_trace_rt.compose_cart

namespace CellularAutomatas.BoundedAnticipation

open CellAutomaton

namespace EventRouting

variable {α β : Type} [Alphabet β]

/-- A one-tick event pipeline moves the observed event one cell left while
leaving the source computation running unchanged. -/
def moveLeft (source : CellAutomaton α (Option β)) :
    CellAutomaton α (Option β) where
  Q := source.Q × Option β
  δ left center right :=
    (source.δ left.1 center.1 right.1, source.project right.1)
  embed symbol := (source.embed symbol, none)
  project := Prod.snd

theorem moveLeft_state (source : CellAutomaton α (Option β))
    (input : Config α) (t : ℕ) (p : ℤ) :
    ((moveLeft source).nextt ⦋input⦌ t p).1 = source.nextt ⦋input⦌ t p := by
  induction t generalizing p with
  | zero =>
      show source.embed (input p) = source.embed (input p)
      rfl
  | succ t ih =>
      rw [CellAutomaton.nextt_succ, CellAutomaton.nextt_succ,
        CellAutomaton.next_apply, CellAutomaton.next_apply]
      show source.δ
        (((moveLeft source).nextt ⦋input⦌ t (p - 1)).1)
        (((moveLeft source).nextt ⦋input⦌ t p).1)
        (((moveLeft source).nextt ⦋input⦌ t (p + 1)).1) =
        source.δ (source.nextt ⦋input⦌ t (p - 1))
          (source.nextt ⦋input⦌ t p) (source.nextt ⦋input⦌ t (p + 1))
      rw [ih, ih, ih]

theorem moveLeft_zero (source : CellAutomaton α (Option β))
    (input : Config α) (p : ℤ) :
    (moveLeft source).comp input 0 p = none := rfl

theorem moveLeft_succ (source : CellAutomaton α (Option β))
    (input : Config α) (t : ℕ) (p : ℤ) :
    (moveLeft source).comp input (t + 1) p = source.comp input t (p + 1) := by
  change ((moveLeft source).nextt ⦋input⦌ (t + 1) p).2 =
    source.project (source.nextt ⦋input⦌ t (p + 1))
  rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
  show source.project (((moveLeft source).nextt ⦋input⦌ t (p + 1)).1) =
    source.project (source.nextt ⦋input⦌ t (p + 1))
  rw [moveLeft_state]

def routeLeft (source : CellAutomaton α (Option β)) : ℕ → CellAutomaton α (Option β)
  | 0 => source
  | distance + 1 => moveLeft (routeLeft source distance)

theorem routeLeft_spec (source : CellAutomaton α (Option β)) (distance : ℕ)
    (input : Config α) (t : ℕ) (p : ℤ) :
    (routeLeft source distance).comp input t p =
      if distance ≤ t then source.comp input (t - distance) (p + distance) else none := by
  induction distance generalizing t p with
  | zero =>
      show source.comp input t p =
        if 0 ≤ t then source.comp input (t - 0) (p + (0 : ℕ)) else none
      simp
  | succ distance ih =>
      cases t with
      | zero =>
          show (moveLeft (routeLeft source distance)).comp input 0 p = _
          rw [moveLeft_zero]
          simp
      | succ t =>
          show (moveLeft (routeLeft source distance)).comp input (t + 1) p = _
          rw [moveLeft_succ, ih]
          have hposition : p + 1 + (distance : ℤ) = p + ((distance + 1 : ℕ) : ℤ) := by
            push_cast
            ring
          rw [hposition]
          simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right]

end EventRouting

namespace DiagonalReadout

variable {α Γ : Type} [Alphabet α] [Alphabet Γ]
variable {advice : Advice α Γ} {distance : ℕ}

/-- Do not truncate the delayed trace at the original input length: its
last useful outputs occur after that time. -/
abbrev compressed (trace : advice.DelayedTrace (3 * distance)) : CompressToΛ where
  C_orig := trace.C.map_project some

def source (trace : advice.DelayedTrace (3 * distance)) :
    CellAutomaton (Option α) (Option (Fin 3 → Option Γ)) :=
  EventRouting.routeLeft (compressed trace).C distance

theorem compressed_payload (trace : advice.DelayedTrace (3 * distance))
    (word : Word α) (p : ℕ) :
    (compressed trace).decode_cfg word (↑(p + distance) : ℤ) =
      fun r : Fin 3 => some (trace.C.trace word (3 * distance + (3 * p + r.val))) := by
  funext r
  simp only [CompressToΛ.decode_cfg, Int.natCast_nonneg, if_true, triple_at,
    Int.natAbs_mul, Int.natAbs_natCast, show (3 : ℤ).natAbs = 3 from rfl,
    compressed, trace_of_map_project, Function.comp_apply]
  congr 2
  omega

theorem source_spec (trace : advice.DelayedTrace (3 * distance))
    (word : Word α) (hne : word ≠ []) (t p : ℕ) :
    (source trace).comp word t p =
      if t = 3 + 3 * distance + 2 * p then
        some (fun r : Fin 3 =>
          some (trace.C.trace word (3 * distance + (3 * p + r.val))))
      else none := by
  rw [source, EventRouting.routeLeft_spec]
  by_cases htime : distance ≤ t
  · show (if distance ≤ t then
        (compressed trace).C.comp word (t - distance) ((p : ℤ) + distance)
        else none) = _
    rw [if_pos htime]
    have hposition : (p : ℤ) + distance = ↑(p + distance) := by omega
    rw [hposition, (compressed trace).spec word hne]
    simp only [Int.natAbs_natCast]
    have hfiring : t - distance = 3 + 2 * (p + distance) ↔
        t = 3 + 3 * distance + 2 * p := by omega
    simp only [hfiring, compressed_payload]
  · show (if distance ≤ t then
        (compressed trace).C.comp word (t - distance) ((p : ℤ) + distance)
        else none) = _
    rw [if_neg htime, if_neg (by omega)]

def machine (trace : advice.DelayedTrace (3 * distance)) :
    PacketReadoutMachine α Γ where
  width := 3
  width_ge_two := by decide
  clock := (source trace).map_project Option.isSome
  data := (source trace).map_project fun event r =>
    ((event.getD (fun _ => none)) r).getD default

def contract (trace : advice.DelayedTrace (3 * distance)) :
    (machine trace).RTContractOn (fun _ => True) where
  startup := 3 + 3 * distance
  startup_ge_width := by show 3 ≤ 3 + 3 * distance; omega
  time := fun _ p => 3 + 3 * distance + 2 * p
  fires := by
    intro word _ hne t p
    show ((source trace).map_project Option.isSome).comp word t p = _
    rw [comp_of_map_project, source_spec trace word hne]
    split <;> simp_all
  deadline := by
    intro word _ _ p hp
    change p < LocalHorizon.packetCount 3 word.length at hp
    show 3 + 3 * distance + 2 * p ≤
      3 + 3 * distance + (3 - 1) * LocalHorizon.packetCount 3 word.length
    omega

theorem readout_eq (trace : advice.DelayedTrace (3 * distance)) (word : Word α) :
    (contract trace).readout word = advice word := by
  apply List.ext_getElem (by simp)
  intro i hi _
  have hiword : i < word.length := by simpa using hi
  have hne : word ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [(contract trace).readout_getElem word i hiword]
  change ((source trace).map_project
      (fun event r => ((event.getD (fun _ => none)) r).getD default)).comp word
      (3 + 3 * distance + 2 * (i / 3)) (↑(i / 3) : ℤ)
      ⟨i % 3, Nat.mod_lt _ (by decide)⟩ = _
  rw [comp_of_map_project, source_spec trace word hne]
  simp only [if_true, Option.getD_some]
  have hindex : 3 * (i / 3) + i % 3 = i := by omega
  rw [hindex]
  exact trace.spec word i hiword

end DiagonalReadout

end CellularAutomatas.BoundedAnticipation

namespace CellularAutomatas

theorem Advice.DelayedTrace.isGlobalPacketReadout {α Γ : Type}
    [Alphabet α] [Alphabet Γ] {advice : Advice α Γ} {distance : ℕ}
    (trace : advice.DelayedTrace (3 * distance)) :
    advice.IsGlobalPacketReadout :=
  ⟨BoundedAnticipation.DiagonalReadout.machine trace,
    BoundedAnticipation.DiagonalReadout.contract trace,
    fun word _ => BoundedAnticipation.DiagonalReadout.readout_eq trace word⟩

end CellularAutomatas
