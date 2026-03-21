import CellularAutomatas.proofs.ca_rt_utils
import CellularAutomatas.proofs.two_stage_is_rt_closed

namespace CellularAutomatas

variable {α : Type} [Alphabet α]
variable {Γ₁ : Type} [Alphabet Γ₁]
variable {Γ₂ : Type} [Alphabet Γ₂]

open CellAutomaton

-- Helper: zip with map Prod.swap swaps the lists
private lemma zip_map_swap {α β: Type} (w1: Word α) (w2: Word β) (_h: w1.length = w2.length):
    (w1 ⨂ w2).map Prod.swap = w2 ⨂ w1 := by
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp

-- Helper: mapping a projection over a reassociated zip
-- For u : Word(Γ₁ × α), v : Word Γ₂:
-- ((u ⨂ v).map (fun ((g1, a), g2) => (a, g2))) = u.map snd ⨂ v
private lemma zip_map_proj {Γ₁ α Γ₂: Type} (u: Word (Γ₁ × α)) (v: Word Γ₂) (_h: u.length = v.length):
    (u ⨂ v).map (fun (p : (Γ₁ × α) × Γ₂) => (p.1.2, p.2)) = (u.map Prod.snd) ⨂ v := by
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp

-- Helper: map swap then fst = snd
@[simp]
private lemma map_swap_fst {α β: Type} (w: Word (α × β)):
    (w.map Prod.swap).map Prod.fst = w.map Prod.snd := by
  simp [List.map_map, Function.comp]

-- Helper: map swap then snd = fst
@[simp]
private lemma map_swap_snd {α β: Type} (w: Word (α × β)):
    (w.map Prod.swap).map Prod.snd = w.map Prod.fst := by
  simp [List.map_map, Function.comp]


/-!
## Composition Closure of RT-Closed Advices

Weak + Strong = Weak:
  Given f₁ : Advice α Γ₁ (weak_rt_closed)
  and   f₂ : Advice Γ₁ Γ₂ (rt_closed, i.e. strong),
  the composition f₁.compose f₂ : Advice α Γ₂ is weak_rt_closed.

Strong + Strong = Strong:
  Given f₁ : Advice α Γ₁ (rt_closed)
  and   f₂ : Advice Γ₁ Γ₂ (rt_closed),
  the composition f₁.compose f₂ is rt_closed.
-/


theorem Advice.weak_rt_closed_compose_rt_closed
    (f₁: Advice α Γ₁) (f₂: Advice Γ₁ Γ₂)
    (h₁: f₁.weak_rt_closed) (h₂: f₂.rt_closed):
    (f₁.compose f₂).weak_rt_closed := by
  rw [advice_weak_rt_closed_iff]
  intro C

  -- Step 1: Build D ∈ CA_rt((Γ₁ × α) × Γ₂) from C by remapping input
  -- D accepts w iff C accepts w with components projected: ((γ₁,a),γ₂) ↦ (a,γ₂)
  let proj : (Γ₁ × α) × Γ₂ → α × Γ₂ := fun ((_, a), g2) => (a, g2)
  let D_tca := C.val.map_embed proj
  have hD_mem : D_tca ∈ CA_rt ((Γ₁ × α) × Γ₂) := by
    simp only [D_tca, c_map_embed_in_ca_rt_iff_c_in_ca_rt]; exact C.prop
  let D : CA_rt ((Γ₁ × α) × Γ₂) := ⟨D_tca, hD_mem⟩

  -- Step 2: Use f₂.rt_closed with Σ = α to get (f₂.lift α).weak_rt_closed
  have h_f2_α : (f₂.lift α).weak_rt_closed := h₂ α
  rw [advice_weak_rt_closed_iff] at h_f2_α
  have step2 := h_f2_α D
  rw [ℒ_CA_rt_iff] at step2
  obtain ⟨D₁, hD₁_mem, hD₁_L⟩ := step2

  -- Step 3: Swap to get D₂ ∈ CA_rt(α × Γ₁) from D₁ ∈ CA_rt(Γ₁ × α)
  let D₂_tca := D₁.map_embed Prod.swap
  have hD₂_mem : D₂_tca ∈ CA_rt (α × Γ₁) := by
    simp only [D₂_tca, c_map_embed_in_ca_rt_iff_c_in_ca_rt]; exact hD₁_mem
  let D₂ : CA_rt (α × Γ₁) := ⟨D₂_tca, hD₂_mem⟩

  -- Step 4: Use f₁.weak_rt_closed
  rw [advice_weak_rt_closed_iff] at h₁
  have step4 := h₁ D₂

  -- Step 5: Show the sets are equal
  convert step4 using 1
  ext w
  simp only [Set.mem_setOf_eq]

  -- Show: w ⨂ (f₁.compose f₂) w ∈ C.val.L ↔ w ⨂ f₁ w ∈ D₂.val.L
  show w ⨂ (f₁.compose f₂).f w ∈ C.val.L ↔ w ⨂ f₁.f w ∈ D₂.val.L

  -- Unfold D₂ → D₁ → D → C
  show w ⨂ f₂.f (f₁.f w) ∈ C.val.L ↔ w ⨂ f₁.f w ∈ D₂_tca.L
  rw [map_embed_L, hD₁_L, Set.mem_setOf_eq]
  show w ⨂ f₂.f (f₁.f w) ∈ C.val.L ↔
    ((w ⨂ f₁.f w).map Prod.swap ⨂ (f₂.lift α).f ((w ⨂ f₁.f w).map Prod.swap)) ∈ D_tca.L
  rw [map_embed_L]

  -- Both sides are membership in C.val.L, so show the words are equal
  suffices word_eq :
      List.map proj (List.map Prod.swap (w ⨂ f₁.f w) ⨂ (f₂.lift α).f (List.map Prod.swap (w ⨂ f₁.f w)))
      = w ⨂ f₂.f (f₁.f w) by
    constructor
    · intro h; rwa [word_eq]
    · intro h; rwa [← word_eq]
  apply List.ext_getElem
  · simp
  intro i h1 h2
  simp only [List.getElem_zip, List.getElem_map, Advice.lift, Prod.swap, proj]
  refine Prod.ext ?_ ?_
  · simp
  · simp only
    congr 1
    congr 1
    simp [List.map_fst_zip]


-- Lift preserves composition: (f₁.compose f₂).lift S = (f₁.lift S).compose f₂
omit [Alphabet α] [Alphabet Γ₁] [Alphabet Γ₂] in
private lemma Advice.compose_lift_eq (f₁: Advice α Γ₁) (f₂: Advice Γ₁ Γ₂) (S: Type) [Alphabet S]:
    (f₁.compose f₂).lift S = (f₁.lift S).compose f₂ := by
  apply advice_eq_iff
  rfl


theorem Advice.rt_closed_compose_rt_closed
    (f₁: Advice α Γ₁) (f₂: Advice Γ₁ Γ₂)
    (h₁: f₁.rt_closed) (h₂: f₂.rt_closed):
    (f₁.compose f₂).rt_closed := by
  intro S _inst
  rw [Advice.compose_lift_eq]
  exact Advice.weak_rt_closed_compose_rt_closed (f₁.lift S) f₂ (h₁ S) h₂


end CellularAutomatas
