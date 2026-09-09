import CellularAutomatas.proofs.advice_theory.local_horizon.fusion.composition

namespace CellularAutomatas.LocalHorizon.Fusion

/-- Unequal widths concatenate in word order. The partial final packet keeps
its genuine padding instead of inventing a final output symbol. -/
example :
    flatten (q₁ := 2) (q₂ := 3)
      (SpeedupKx.compress 2
        (SpeedupKx.compress 3 (word_to_config [true, false, true, false, true])) 0) =
      fun i : Fin 6 => [some true, some false, some true, some false, some true, none][i] := by
  decide

example :
    flatten (q₁ := 3) (q₂ := 2)
      (SpeedupKx.compress 3 (SpeedupKx.compress 2 (word_to_config ([] : Word Bool))) 0) =
      fun _ => none := by
  decide

/-- One late lane prevents the packet from firing early. -/
example : ¬lanesReady (q := 2) (fun i => if i.val = 0 then 0 else 4) 2 := by
  decide

example : lanesReady (q := 2) (fun i => if i.val = 0 then 0 else 4) 3 := by
  decide

/-- The intermediate contract need not be global, provided the first
readout establishes precisely its promise. -/
example {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (A : Advice α β) (B : Advice β γ) (domain : Word α → Prop)
    (middle : Word β → Prop)
    (hA : A.IsPacketReadoutOn domain) (hB : B.IsPacketReadoutOn middle)
    (hcompatible : ∀ w, domain w → middle (A w)) :
    (A.compose B).IsPacketReadoutOn domain :=
  hA.compose hB hcompatible

example {α β γ : Type} [Alphabet α] [Alphabet β] [Alphabet γ]
    (A : Advice α β) (B : Advice β γ)
    (hA : A.IsGlobalPacketReadout) (hB : B.IsGlobalPacketReadout) :
    (A.compose B).IsGlobalPacketReadout :=
  hA.compose hB

end CellularAutomatas.LocalHorizon.Fusion
