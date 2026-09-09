import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.basic_product_ca

namespace CellularAutomatas

/-- A proof-level firing time witnessed by one fixed finite, radius-one CA.
`valid` restricts the contract, not the total transition function. In particular,
no origin-dependent pulse is required on the empty homogeneous input. -/
structure RealizableHorizon (α : Type) (valid : Word α → Prop) where
  time : Word α → ℕ → ℕ
  clock : CellAutomaton (Option α) Bool
  fires : ∀ w, valid w → w ≠ [] → ∀ t p : ℕ,
    clock.comp w t p = decide (t = time w p)

namespace LocalHorizon

/-- Number of occupied physical packets; the empty word has no packets. -/
def packetCount (q n : ℕ) : ℕ :=
  if n = 0 then 0 else (n - 1) / q + 1

@[simp]
theorem packetCount_of_pos (q n : ℕ) (hn : 0 < n) :
    packetCount q n = (n - 1) / q + 1 := by
  simp only [packetCount, Nat.ne_of_gt hn, if_false]

/-- Positions refer to physical packets, not to logical output symbols.
This bound is a proof obligation, not a global clock provided to the machine. -/
def RTAdmissibleHorizon {α : Type} {valid : Word α → Prop}
    (q κ : ℕ) (horizon : RealizableHorizon α valid) : Prop :=
  2 ≤ q ∧ q ≤ κ ∧
    ∀ w, valid w → w ≠ [] → ∀ p, p < packetCount q w.length →
      horizon.time w p ≤ κ + (q - 1) * packetCount q w.length

/-- Sample packet slot `i % q` at physical position `i / q`. The length
bound truncates the final packet and handles empty advice without a clock. -/
def readout {α Γ : Type} {valid : Word α → Prop}
    (q : ℕ) [NeZero q] (horizon : RealizableHorizon α valid)
    (data : CellAutomaton (Option α) (Fin q → Γ)) : Advice α Γ where
  f w := List.ofFn fun i : Fin w.length =>
    data.comp w (horizon.time w (i.val / q)) (↑(i.val / q) : ℤ)
      ⟨i.val % q, Nat.mod_lt _ (NeZero.pos q)⟩
  len _ := List.length_ofFn

@[simp]
theorem readout_getElem {α Γ : Type} {valid : Word α → Prop}
    (q : ℕ) [NeZero q] (horizon : RealizableHorizon α valid)
    (data : CellAutomaton (Option α) (Fin q → Γ))
    (w : Word α) (i : ℕ) (hi : i < w.length) :
    (readout q horizon data w)[i]'(by simpa using hi) =
      data.comp w (horizon.time w (i / q)) (↑(i / q) : ℤ)
        ⟨i % q, Nat.mod_lt _ (NeZero.pos q)⟩ := by
  exact List.getElem_ofFn _

/-- Sampling is a genuine local event: the product observes its own pulse,
without querying the mathematical time function. -/
def events {α Γ : Type} [Alphabet α] [Alphabet Γ] {valid : Word α → Prop}
    (q : ℕ) [NeZero q] (horizon : RealizableHorizon α valid)
    (data : CellAutomaton (Option α) (Fin q → Γ)) :
    CellAutomaton (Option α) (Option (Fin q → Γ)) :=
  (horizon.clock ⨂ data).map_project fun (pulse, packet) =>
    if pulse then some packet else none

theorem events_spec {α Γ : Type} [Alphabet α] [Alphabet Γ] {valid : Word α → Prop}
    (q : ℕ) [NeZero q] (horizon : RealizableHorizon α valid)
    (data : CellAutomaton (Option α) (Fin q → Γ))
    (w : Word α) (hw : valid w) (hne : w ≠ []) (t p : ℕ) :
    (events q horizon data).comp w t p =
      if t = horizon.time w p then
        some (data.comp w (horizon.time w p) p) else none := by
  simp only [events, comp_of_map_project, ca_zip_comp,
    horizon.fires w hw hne]
  by_cases ht : t = horizon.time w p
  · show (if decide (t = horizon.time w p) = true then
        some (data.comp w t p) else none) = _
    simp [ht]
  · show (if decide (t = horizon.time w p) = true then
        some (data.comp w t p) else none) = _
    simp [ht]

end LocalHorizon
end CellularAutomatas
