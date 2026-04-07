import CellularAutomatas.lt_closed
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

/-! ## CAr_rt definition -/

/-- Right-reading CA class: reads at position n-1.
    Note: this differs from `CAr` (which reads at n = right border).
    CAr_rt reads the *last cell* of the word. -/
def CAr_rt (α : Type) [Alphabet α] :=
  { C ∈ tCellAutomata α | C.p = fun (n : ℕ) => ((n : ℤ) - 1) } |> t_rt α

/-! ## Key config identity -/

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

/-- Convert a left-reading CA to a right-reading CA. -/
def tCellAutomaton.toRight (C : tCellAutomaton α) : tCellAutomaton α where
  toCellAutomaton := C.toCellAutomaton.flip
  t := C.t
  p := fun n => ((n : ℤ) - 1)

/-- Convert a right-reading CA to a left-reading CA. -/
def tCellAutomaton.toLeft (C : tCellAutomaton α) : tCellAutomaton α where
  toCellAutomaton := C.toCellAutomaton.flip
  t := C.t
  p := fun _ => 0

/-! ## Membership preservation -/

theorem tCellAutomaton.toRight_in_CAr_rt (C : tCellAutomaton α) (hC : C ∈ CA_rt α) :
    C.toRight ∈ CAr_rt α := by
  simp only [CAr_rt, CA_rt, t_rt, CA, tCellAutomata, Set.mem_setOf_eq,
             Set.mem_univ, true_and, tCellAutomaton.toRight] at hC ⊢
  obtain ⟨h_p, h_t⟩ := hC
  exact h_t

theorem tCellAutomaton.toLeft_in_CA_rt (C : tCellAutomaton α) (hC : C ∈ CAr_rt α) :
    C.toLeft ∈ CA_rt α := by
  simp only [CA_rt, CAr_rt, t_rt, CA, tCellAutomata, Set.mem_setOf_eq,
             Set.mem_univ, true_and, tCellAutomaton.toLeft] at hC ⊢
  obtain ⟨h_p, h_t⟩ := hC
  exact h_t

/-! ## Acceptance equivalence -/

/-- The toRight CA accepts w iff the original CA accepts w.reverse. -/
theorem tCellAutomaton.toRight_accepts_iff (C : tCellAutomaton α) (hC : C ∈ CA_rt α) (w : Word α) :
    C.toRight.accepts w = C.accepts w.reverse := by
  -- Extract C.p = 0
  have h_p : C.p = fun _ => (0 : ℤ) := by
    simp only [CA_rt, t_rt, CA, tCellAutomata, Set.mem_setOf_eq, Set.mem_univ, true_and] at hC
    exact hC.1
  simp only [tCellAutomaton.accepts, tCellAutomaton.toRight]
  rw [h_p, List.length_reverse]
  -- LHS: C.flip.comp ⦋⟬w⟭⦌ (C.t |w|) (|w| - 1)
  -- RHS: C.comp ⦋⟬w.reverse⟭⦌ (C.t |w|) 0
  rw [CellAutomaton.flip_comp, CellAutomaton.flip_embed_config']
  -- LHS: C.comp ⦋⟬w⟭.flip⦌ (C.t |w|) (-(|w| - 1))
  simp only [comp, Function.comp_apply, project_config]
  congr 1
  conv_lhs => rw [show -(↑w.length - 1 : ℤ) = 0 + (1 - ↑w.length) from by ring]
  rw [nextt_shift]
  congr 1
  funext q
  simp only [embed_config]
  exact congrArg C.toCellAutomaton.embed (congrFun (word_to_config_flip_shift w) q)

/-- The toLeft CA accepts w iff the original CA accepts w.reverse. -/
theorem tCellAutomaton.toLeft_accepts_iff (C : tCellAutomaton α) (hC : C ∈ CAr_rt α) (w : Word α) :
    C.toLeft.accepts w = C.accepts w.reverse := by
  -- Strategy: C.toLeft ∈ CA_rt, so we can apply toRight_accepts_iff to C.toLeft.
  -- C.toLeft.toRight has the same underlying CA as C (flip.flip = id) and same t and p.
  -- So C.toLeft.toRight.accepts = C.accepts.
  have h_D_in_CA_rt : C.toLeft ∈ CA_rt α := tCellAutomaton.toLeft_in_CA_rt C hC
  -- Apply toRight_accepts_iff to D = C.toLeft:
  -- D.toRight.accepts w = D.accepts w.reverse
  -- i.e. C.toLeft.toRight.accepts w = C.toLeft.accepts w.reverse
  have key := tCellAutomaton.toRight_accepts_iff C.toLeft h_D_in_CA_rt w.reverse
  -- key: C.toLeft.toRight.accepts w.reverse = C.toLeft.accepts w.reverse.reverse
  simp only [List.reverse_reverse] at key
  -- key: C.toLeft.toRight.accepts w.reverse = C.toLeft.accepts w
  have h_p : C.p = fun (n : ℕ) => ((n : ℤ) - 1) := by
    simp only [CAr_rt, t_rt, tCellAutomata, Set.mem_setOf_eq, Set.mem_univ, true_and] at hC
    exact hC.1
  have h_accepts_eq : C.toLeft.toRight.accepts w.reverse = C.accepts w.reverse := by
    simp only [tCellAutomaton.accepts, tCellAutomaton.toRight, tCellAutomaton.toLeft,
               CellAutomaton.flip, h_p]
  rw [h_accepts_eq] at key
  -- key: C.accepts w.reverse = C.toLeft.accepts w
  exact key.symm

/-! ## Main theorem -/

/-- ℒ_rev(CA_rt) = ℒ(CAr_rt): Reversals of left-reading RT = right-reading RT. -/
theorem ca_rt_rev_eq_car_rt : ℒ_rev (CA_rt α) = ℒ (CAr_rt α) := by
  ext L
  simp only [ℒ_rev, LanguageClass.rev, Set.mem_image, ℒ, Set.mem_setOf_eq]
  constructor
  · -- (⊆) ℒ_rev(CA_rt) ⊆ ℒ(CAr_rt)
    intro ⟨L', ⟨C, hC, hL'⟩, hL_eq⟩
    subst hL' hL_eq
    use C.toRight
    refine ⟨tCellAutomaton.toRight_in_CAr_rt C hC, ?_⟩
    show Language.rev C.L = C.toRight.L
    ext w
    simp only [Language.rev, tCellAutomaton.L, Set.mem_setOf_eq]
    show w.reverse ∈ {w | C.accepts w} ↔ w ∈ {w | C.toRight.accepts w}
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> rw [tCellAutomaton.toRight_accepts_iff C hC w] at * <;> exact h
  · -- (⊇) ℒ(CAr_rt) ⊆ ℒ_rev(CA_rt)
    intro ⟨C, hC, hL⟩
    subst hL
    use Language.rev C.L
    refine ⟨⟨C.toLeft, tCellAutomaton.toLeft_in_CA_rt C hC, ?_⟩, Language.rev_rev C.L⟩
    ext w
    simp only [Language.rev, tCellAutomaton.L, Set.mem_setOf_eq, DefinesLanguage.L]
    show w.reverse ∈ {w | C.accepts w} ↔ w ∈ {w | C.toLeft.accepts w}
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> rw [tCellAutomaton.toLeft_accepts_iff C hC w] at * <;> exact h

end CellularAutomatas
