import CellularAutomatas.defs
import CellularAutomatas.internal_defs
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.speedup_left_independent
import CellularAutomatas.proofs.constructions.border_quiescent
import CellularAutomatas.proofs.constructions.left_indep_to_regular
import CellularAutomatas.proofs.constructions.left_indep_from_regular
namespace CellularAutomatas

open CellAutomaton


def cast α (x: α := by rfl) := x


structure CAgfSpeedup where
  {α : Type}
  {β : Type}
  [_inst_α : Alphabet α]
  [_inst_β : Alphabet β]
  C_orig : CellAutomaton α？ β  -- Takes optional alphabet for finite words

attribute [instance] CAgfSpeedup._inst_α
attribute [instance] CAgfSpeedup._inst_β

namespace CAgfSpeedup

variable (e : CAgfSpeedup)

private def step1 := RegularToLeftIndep.mk e.C_orig

private def step2 := LeftIndepSpeedup.mk e.step1.C 3 (by decide) e.step1.C_left_independent

private def step3 := LeftIndepToRegular.mk e.step2.C e.step2.C_left_indep

def C := e.step3.C

def g1 (q: Fin 3 → e.step2.β): e.β := match q 2 with
  | BetaUnionSq.single s => s
  | BetaUnionSq.pair _ _ => default

lemma g1_spec (w: Word e.α) (h: w.length > 0) (p: ℕ):
    e.g1 (e.C.comp w (2 * p + 1) (p)) = e.C_orig.comp w (3 * p + 1) 0 := by
  rw [C]
  rw [e.step3.spec]

  have : e.step3.C_orig = e.step2.C := by rfl
  rw [this]

  unfold g1
  rw [e.step2.spec (hi := by ring_nf; grind) (hw := h) (hi2 := by grind)]

  rw [cast $ e.step2.C_orig = e.step1.C]

  simp only [cast $ e.step2.k = 3]

  erw [e.step1.spec]
  simp [cast $ e.step2.k = 3]
  ring_nf

  have : (2 + (p: ℤ) * 6).toNat % 2 = 0 := by grind
  simp only [this, ↓reduceIte]

  rw [cast $ e.step1.C_orig = e.C_orig]
  congr
  grind
  grind



def g2 (q: Fin 3 → e.step2.β): e.β × e.β :=
  (
    match q 1 with
    | BetaUnionSq.single _ => default
    | BetaUnionSq.pair s _ => s,
    match q 0 with
    | BetaUnionSq.single s => s
    | BetaUnionSq.pair _ _ => default
  )


lemma g2_spec (w: Word e.α) (h: w.length > 0) (p: ℕ) :
    e.g2 (e.C.comp w (2 * p + 2) (p + 1)) = (e.C_orig.comp w (3 * p + 2) 0, e.C_orig.comp w (3 * p + 3) 0) := by
  rw [C]
  rw [e.step3.spec]

  have : e.step3.C_orig = e.step2.C := by rfl
  rw [this]

  unfold g2
  rw [e.step2.spec (hi := by ring_nf; grind) (hw := h) (hi2 := by grind)]
  rw [e.step2.spec (hi := by ring_nf; grind) (hw := h) (hi2 := by grind)]


  rw [cast $ e.step2.C_orig = e.step1.C]

  simp only [cast $ e.step2.k = 3]

  erw [e.step1.spec]
  erw [e.step1.spec]
  simp [cast $ e.step2.k = 3]
  ring_nf

  have : ((6 + (p: ℤ) * 6).toNat - 1) % 2 = 1 := by grind
  simp only [this, one_ne_zero, ↓reduceIte]

  have : ((6 + (p: ℤ) * 6).toNat) % 2 = 0 := by grind
  simp only [this, ↓reduceIte]

  rw [cast $ e.step1.C_orig = e.C_orig]

  constructor

  congr
  grind
  grind

  congr
  grind
  grind

-- At time 0, the speedup gives the initial state.
-- After the projectQ' change, g2 on the initial projected output gives trace(0).
lemma g2_initial_spec (w: Word e.α) (h: w.length > 0):
    (e.g2 (e.C.comp w 0 0)).2 = e.C_orig.comp w 0 0 := by
  -- First establish that C.comp w 0 0 = fun _ => BetaUnionSq.single(C_orig.comp w 0 0)
  have key : e.C.comp w 0 0 = fun _ => BetaUnionSq.single (e.C_orig.comp w 0 0) := by
    rw [C]
    rw [e.step3.spec]
    have : e.step3.C_orig = e.step2.C := by rfl
    rw [this]
    simp only [mul_zero, zero_sub, CellAutomaton.comp, CellAutomaton.project_config,
      CellAutomaton.nextt_zero, Function.comp_apply]
    have h0 : (-↑(0:ℕ) : ℤ) = 0 := by norm_num
    rw [h0]
    funext j
    simp only [CellAutomaton.embed_config, word_to_config]
    have hw0 : (0 : ℤ) ≥ 0 ∧ (0 : ℤ) < ↑w.length := ⟨le_refl 0, by omega⟩
    simp only [hw0, dite_true, and_self]
    -- Goal: step2.C.project(step2.C.embed(some w[0])) j = BetaUnionSq.single(C_orig.project(C_orig.embed(some w[0])))
    rfl
  -- Now rewrite using key and simplify g2
  unfold g2
  rw [key]

end CAgfSpeedup

end CellularAutomatas
