import CellularAutomatas.proofs.constructions.basic_flip
import CellularAutomatas.proofs.basic

/-!
# ℒ_rev(CA_rt) = ℒ(CAr_rt)

Reversals of left-reading real-time CA languages equal right-reading real-time CA languages.

## Key identity

`shift (1-n) ⟬w⟭.flip = ⟬w.reverse⟭`

Combined with:
- `C.flip.comp c t p = C.comp c.flip t (-p)`
- `C.comp (shift d c) t p = C.comp c t (p + d)` (via nextt_shift)

We get:
```
C.flip.comp ⦋⟬w⟭⦌ (n-1) (n-1)
= C.comp ⦋⟬w⟭⦌.flip (n-1) (1-n)
= C.comp ⦋⟬w⟭.flip⦌ (n-1) (1-n)
= C.comp ⦋shift (1-n) ⟬w⟭.flip⦌ (n-1) 0
= C.comp ⦋⟬w.reverse⟭⦌ (n-1) 0
= C.accepts w.reverse
```
-/

namespace CellularAutomatas

open CellAutomaton

variable {α : Type} [Alphabet α]

/-! ## Key config identity -/

omit [Alphabet α] in
/-- shift (1-n) ⟬w⟭.flip = ⟬w.reverse⟭

Proof:
- LHS at p: ⟬w⟭.flip(p + 1 - n) = ⟬w⟭(n - 1 - p)
- RHS at p: ⟬w.reverse⟭(p) = w.reverse[p] = w[n-1-p]
Both equal `some w[n-1-p]` for 0 ≤ p < n, and `none` outside. -/
lemma word_to_config_flip_shift (w : Word α) :
    (fun p => (word_to_config w).flip (p + (1 - ↑w.length))) = word_to_config w.reverse := by
  funext p
  simp only [Config.flip_apply, word_to_config, List.length_reverse]
  have h_idx : -(p + (1 - ↑w.length)) = ↑w.length - 1 - p := by ring
  rw [h_idx]
  split_ifs with h1 h2 h2
  · -- Both in range
    have h_idx2 : (↑w.length - 1 - p).toNat = w.length - 1 - p.toNat := by omega
    simp only [h_idx2, List.getElem_reverse]
  · omega
  · omega
  · rfl

/-! ## The flip construction -/

/-- Convert a left-reading CA_rt to a right-reading CAr_rt via flip. -/
def CA_rt.toRight (C : CA_rt α) : CAr_rt α where
  toCellAutomaton := C.toCellAutomaton.flip

/-- Convert a right-reading CAr_rt to a left-reading CA_rt via flip. -/
def CAr_rt.toLeft (C : CAr_rt α) : CA_rt α where
  toCellAutomaton := C.toCellAutomaton.flip

/-! ## Acceptance equivalence -/

omit [Alphabet α] in
/-- The toRight CA accepts w iff the original CA accepts w.reverse. -/
theorem CA_rt.toRight_accepts_iff (C : CA_rt α) (w : Word α) :
    C.toRight.accepts w = C.accepts w.reverse := by
  simp only [tCellAutomaton.accepts, CA_rt.toRight, AcceptanceSchema.rt_right,
             AcceptanceSchema.rt_center, List.length_reverse]
  -- LHS: C.flip.comp ⦋⟬w⟭⦌ (|w| - 1) (|w| - 1)
  -- RHS: C.comp ⦋⟬w.reverse⟭⦌ (|w| - 1) 0
  rw [CellAutomaton.flip_comp, CellAutomaton.flip_embed_config']
  -- LHS: C.comp ⦋⟬w⟭.flip⦌ (|w| - 1) (-(|w| - 1))
  simp only [comp, Function.comp_apply, project_config]
  congr 1
  conv_lhs => rw [show -(↑w.length - 1 : ℤ) = 0 + (1 - ↑w.length) from by ring]
  rw [nextt_shift]
  congr 1
  funext q
  simp only [embed_config]
  exact congrArg C.toCellAutomaton.embed (congrFun (word_to_config_flip_shift w) q)

/-- The toLeft CA accepts w iff the original CA accepts w.reverse. -/
theorem CAr_rt.toLeft_accepts_iff (C : CAr_rt α) (w : Word α) :
    C.toLeft.accepts w = C.accepts w.reverse := by
  -- Strategy: C.toLeft is a CA_rt, apply toRight_accepts_iff to it.
  have key := CA_rt.toRight_accepts_iff C.toLeft w.reverse
  simp only [List.reverse_reverse] at key
  -- key: C.toLeft.toRight.accepts w.reverse = C.toLeft.accepts w
  -- Show C.toLeft.toRight.accepts = C.accepts (flip.flip = id)
  have h_accepts_eq : C.toLeft.toRight.accepts w.reverse = C.accepts w.reverse := by
    show C.toLeft.toRight.accepts w.reverse = C.accepts w.reverse
    simp only [tCellAutomaton.accepts, CA_rt.toRight, CAr_rt.toLeft,
               AcceptanceSchema.rt_right, AcceptanceSchema.rt_center,
               CellAutomaton.flip, List.length_reverse]
  rw [h_accepts_eq] at key
  exact key.symm

/-! ## Main theorem -/

/-- ℒ_rev(CA_rt) = ℒ(CAr_rt): Reversals of left-reading RT = right-reading RT. -/
theorem ca_rt_rev_eq_car_rt : ℒ_rev (CA_rt α) = ℒ (CAr_rt α) := by
  ext L
  simp only [ℒ_rev, LanguageClass.rev, Set.mem_image, ℒ]
  constructor
  · -- (⊆) ℒ_rev(CA_rt) ⊆ ℒ(CAr_rt)
    rintro ⟨L', ⟨C, rfl⟩, rfl⟩
    refine ⟨C.toRight, ?_⟩
    ext w
    simp only [Language.rev, DefinesLanguage.L, tCellAutomaton.L, Set.mem_setOf_eq]
    constructor <;> intro h
    · simp_rw [CA_rt.toRight_accepts_iff]; exact h
    · simp_rw [CA_rt.toRight_accepts_iff] at h; exact h
  · -- (⊇) ℒ(CAr_rt) ⊆ ℒ_rev(CA_rt)
    rintro ⟨C, rfl⟩
    refine ⟨Language.rev C.L, ⟨C.toLeft, ?_⟩, Language.rev_rev C.L⟩
    ext w
    simp only [Language.rev, DefinesLanguage.L, tCellAutomaton.L, Set.mem_setOf_eq]
    constructor <;> intro h
    · simp_rw [CAr_rt.toLeft_accepts_iff]; exact h
    · simp_rw [CAr_rt.toLeft_accepts_iff] at h; exact h

end CellularAutomatas
