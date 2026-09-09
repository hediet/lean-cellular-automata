import CellularAutomatas.proofs.advice_theory.local_horizon.closure

namespace CellularAutomatas

open CellAutomaton

/-- A finite packet-readout implementation. The clock and data run in parallel;
neither a validity predicate nor a mathematical firing schedule is runtime input. -/
structure PacketReadoutMachine (α Γ : Type) where
  width : ℕ
  width_ge_two : 2 ≤ width
  clock : CellAutomaton (Option α) Bool
  data : CellAutomaton (Option α) (Fin width → Γ)

namespace PacketReadoutMachine

variable {α Γ : Type}

instance (machine : PacketReadoutMachine α Γ) : NeZero machine.width :=
  ⟨by have := machine.width_ge_two; omega⟩

/-- The domain is mandatory. A contract on prepared inputs is not a contract
on all words. Exterior positions must fire, but have no deadline. -/
structure RTContractOn (machine : PacketReadoutMachine α Γ)
    (domain : Word α → Prop) where
  startup : ℕ
  startup_ge_width : machine.width ≤ startup
  time : Word α → ℕ → ℕ
  fires : ∀ w, domain w → w ≠ [] → ∀ t p : ℕ,
    machine.clock.comp w t p = decide (t = time w p)
  deadline : ∀ w, domain w → w ≠ [] → ∀ p,
    p < LocalHorizon.packetCount machine.width w.length →
      time w p ≤ startup +
        (machine.width - 1) * LocalHorizon.packetCount machine.width w.length

/-- The actual local output event, independent of any correctness contract. -/
def events [Alphabet α] [Alphabet Γ] (machine : PacketReadoutMachine α Γ) :
    CellAutomaton (Option α) (Option (Fin machine.width → Γ)) :=
  (machine.clock ⨂ machine.data).map_project fun (pulse, packet) =>
    if pulse then some packet else none

namespace RTContractOn

variable {machine : PacketReadoutMachine α Γ} {domain : Word α → Prop}

/-- Compatibility with the original clock-only interface. -/
def horizon (contract : machine.RTContractOn domain) : RealizableHorizon α domain where
  time := contract.time
  clock := machine.clock
  fires := contract.fires

theorem admissible (contract : machine.RTContractOn domain) :
    LocalHorizon.RTAdmissibleHorizon machine.width contract.startup contract.horizon :=
  ⟨machine.width_ge_two, contract.startup_ge_width, contract.deadline⟩

/-- The schedule denotes the sampled word; only its values on `domain` are
specified by the machine. Empty words produce empty output without a pulse. -/
def readout (contract : machine.RTContractOn domain) : Advice α Γ :=
  LocalHorizon.readout machine.width contract.horizon machine.data

theorem readout_getElem (contract : machine.RTContractOn domain)
    (w : Word α) (i : ℕ) (hi : i < w.length) :
    (contract.readout w)[i]'(by simpa using hi) =
      machine.data.comp w (contract.time w (i / machine.width))
        (↑(i / machine.width) : ℤ)
        ⟨i % machine.width, Nat.mod_lt _ (NeZero.pos machine.width)⟩ :=
  LocalHorizon.readout_getElem machine.width contract.horizon machine.data w i hi

theorem events_spec [Alphabet α] [Alphabet Γ]
    (contract : machine.RTContractOn domain)
    (w : Word α) (hw : domain w) (hne : w ≠ []) (t p : ℕ) :
    machine.events.comp w t p =
      if t = contract.time w p then
        some (machine.data.comp w (contract.time w p) p) else none :=
  LocalHorizon.events_spec machine.width contract.horizon machine.data w hw hne t p

/-- A promise can be strengthened, never silently discarded. -/
def restrict (contract : machine.RTContractOn domain)
    (smaller : Word α → Prop) (hsub : ∀ w, smaller w → domain w) :
    machine.RTContractOn smaller where
  startup := contract.startup
  startup_ge_width := contract.startup_ge_width
  time := contract.time
  fires w hw := contract.fires w (hsub w hw)
  deadline w hw := contract.deadline w (hsub w hw)

theorem restrict_readout (contract : machine.RTContractOn domain)
    (smaller : Word α → Prop) (hsub : ∀ w, smaller w → domain w) :
    (contract.restrict smaller hsub).readout = contract.readout := rfl

/-- The one-shot machine, not the chosen proof witness, determines the time
where two contracts both apply. -/
theorem time_eq {otherDomain : Word α → Prop}
    (contract : machine.RTContractOn domain)
    (other : machine.RTContractOn otherDomain)
    (w : Word α) (hw : domain w) (hother : otherDomain w) (hne : w ≠ []) (p : ℕ) :
    contract.time w p = other.time w p := by
  have hpulse := contract.fires w hw hne (contract.time w p) p
  rw [other.fires w hother hne] at hpulse
  simpa only [decide_true, decide_eq_true_eq] using hpulse

theorem readout_eq_on {otherDomain : Word α → Prop}
    (contract : machine.RTContractOn domain)
    (other : machine.RTContractOn otherDomain)
    (w : Word α) (hw : domain w) (hother : otherDomain w) :
    contract.readout w = other.readout w := by
  apply List.ext_getElem (by simp)
  intro i hi _
  have hiw : i < w.length := by simpa using hi
  have hne := List.ne_nil_of_length_pos (by omega : 0 < w.length)
  rw [contract.readout_getElem w i hiw, other.readout_getElem w i hiw,
    contract.time_eq other w hw hother hne]

/-- Only an all-input contract gives unconditional strong RT closure. -/
noncomputable def rt_closed [Alphabet α] [Alphabet Γ]
    (contract : machine.RTContractOn (fun _ => True)) :
    contract.readout.rt_closed :=
  LocalHorizon.rt_closed machine.width contract.startup
    contract.horizon machine.data contract.admissible

end RTContractOn

/-- Adapt an existing horizon without changing either finite automaton. -/
def ofHorizon {domain : Word α → Prop} (q : ℕ)
    (horizon : RealizableHorizon α domain)
    (data : CellAutomaton (Option α) (Fin q → Γ)) (hq : 2 ≤ q) :
    PacketReadoutMachine α Γ where
  width := q
  width_ge_two := hq
  clock := horizon.clock
  data := data

def contractOfHorizon {domain : Word α → Prop} (q κ : ℕ)
    (horizon : RealizableHorizon α domain)
    (data : CellAutomaton (Option α) (Fin q → Γ))
    (hadmissible : LocalHorizon.RTAdmissibleHorizon q κ horizon) :
    (ofHorizon q horizon data hadmissible.1).RTContractOn domain where
  startup := κ
  startup_ge_width := hadmissible.2.1
  time := horizon.time
  fires := horizon.fires
  deadline := hadmissible.2.2

def ofProducer [Alphabet Γ] {q κ : ℕ} {domain : Word α → Prop}
    {output : Advice α Γ} (producer : LocalHorizon.PacketProducer q κ domain output) :
    PacketReadoutMachine α Γ :=
  ofHorizon q producer.horizon producer.data producer.width_ge_two

def contractOfProducer [Alphabet Γ] {q κ : ℕ} {domain : Word α → Prop}
    {output : Advice α Γ} (producer : LocalHorizon.PacketProducer q κ domain output)
    (hstartup : q ≤ κ) :
    (ofProducer producer).RTContractOn domain :=
  contractOfHorizon q κ producer.horizon producer.data (producer.admissible hstartup)

theorem producer_readout_eq [Alphabet Γ] {q κ : ℕ} {domain : Word α → Prop}
    {output : Advice α Γ} (producer : LocalHorizon.PacketProducer q κ domain output)
    (hstartup : q ≤ κ) (w : Word α) (hw : domain w) :
    (contractOfProducer producer hstartup).readout w = output w := by
  letI : NeZero q := ⟨by have := producer.width_ge_two; omega⟩
  exact producer.readout_eq w hw

end PacketReadoutMachine

/-- A single machine realizes the advice on the explicitly specified domain.
No behavior of the advice outside that domain is asserted. -/
def Advice.IsPacketReadoutOn {α Γ : Type} (advice : Advice α Γ)
    (domain : Word α → Prop) : Prop :=
  ∃ machine : PacketReadoutMachine α Γ,
    ∃ contract : machine.RTContractOn domain,
      ∀ w, domain w → contract.readout w = advice w

/-- The all-input subclass, named separately to avoid confusing it with a
machine whose contract holds only after preparation. -/
def Advice.IsGlobalPacketReadout {α Γ : Type} (advice : Advice α Γ) : Prop :=
  advice.IsPacketReadoutOn (fun _ => True)

theorem Advice.IsGlobalPacketReadout.rt_closed {α Γ : Type}
    [Alphabet α] [Alphabet Γ] {advice : Advice α Γ}
    (hreadout : advice.IsGlobalPacketReadout) :
    Nonempty advice.rt_closed := by
  obtain ⟨machine, contract, hspec⟩ := hreadout
  have heq : contract.readout = advice := by
    apply advice_eq_iff
    funext w
    exact hspec w trivial
  rw [← heq]
  exact ⟨contract.rt_closed⟩

end CellularAutomatas
