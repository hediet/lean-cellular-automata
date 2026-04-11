import CellularAutomatas.defs
import Mathlib.Data.List.Basic

namespace CellularAutomatas

open CellAutomaton

@[simp]
lemma comp_of_map_project {α β γ: Type} {C: CellAutomaton α β} (f: β → γ) (c: Config α):
      (C.map_project f).comp c t i = f (C.comp c t i) := by
  simp only [comp_apply, map_project_nextt]; rfl

@[simp]
lemma trace_of_map_project {α β γ: Type} {C: CellAutomaton α？ β} (f: β → γ) (w: Word α):
      (C.map_project f).trace w = f ∘ (C.trace w) := by
  funext i
  simp only [trace_eq_comp, comp_apply, map_project_nextt, Function.comp_apply]; rfl

@[simp]
lemma trace_rt_of_map_project {α β γ: Type} {C: CellAutomaton α？ β} (f: β → γ) (w: Word α):
      (C.map_project f).trace_rt w = (C.trace_rt w).map f := by
  unfold trace_rt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

def ProdCA {α P γ: Type} [Alphabet P] (f: P → CellAutomaton α γ): CellAutomaton α (P → γ) := {
  Q := ∀ b: P, (f b).Q
  δ := fun qL qC qR a => (f a).δ (qL a) (qC a) (qR a)
  embed := fun a b => (f b).embed a
  project := fun q => (fun b => (f b).project (q b))
}

namespace ProdCA

  variable {α P γ: Type} [Alphabet P]
  variable {f: P → CellAutomaton α γ}

  @[simp, grind =]
  lemma comp [Alphabet γ] {f: P → CellAutomaton α γ}
      (w: Config α) (t: ℕ) (i: ℤ):
      (ProdCA f).comp w t i = fun b => (f b).comp w t i := by
    simp only [CellAutomaton.comp_apply]

    have nextt_proj (c: Config (ProdCA f).Q) (t: ℕ) (i: ℤ) (b: P):
        (ProdCA f).nextt c t i b = (f b).nextt (fun j => c j b) t i := by
      have h_delta : ∀ (X Y Z : (ProdCA f).Q),
          (ProdCA f).δ X Y Z b = (f b).δ (X b) (Y b) (Z b) := fun _ _ _ => rfl
      induction t generalizing i c with
      | zero => simp only [nextt_zero]
      | succ t ih =>
        simp only [nextt_succ, next_apply, h_delta, ih]

    funext b; exact congrArg ((f b).project) (nextt_proj _ t i b)


  def zipMany {γ: P -> Type v} [∀ b, Inhabited (γ b)] (f: (b: P) → Word (γ b)) : Word ((b: P) -> (γ b)) :=
    let n := (f default).length
    (List.range n).map fun i => fun b => (f b).getD i default

  lemma zipMany_get? {γ: P -> Type v} [∀ b, Inhabited (γ b)] (f: (b: P) → Word (γ b)) (i: ℕ):
      (ProdCA.zipMany f)[i]? = if i < (f default).length then some (fun b => (f b).getD i default) else none := by
    simp [zipMany]
    grind

  @[simp]
  lemma zipMany_get {γ: P -> Type v} [∀ b, Inhabited (γ b)] (w_b: (b: P) → Word (γ b)) (i: ℕ) (h: i < (ProdCA.zipMany w_b).length):
      (ProdCA.zipMany w_b)[i] = fun b => (w_b b).getD i default := by
    simp [zipMany]


  @[simp]
  lemma trace_rt [Alphabet γ] (f: P → CellAutomaton (Option α) γ) (w: Word α):
      (ProdCA f).trace_rt w = zipMany (fun b => (f b).trace_rt w) := by
    apply List.ext_getElem
    · unfold CellAutomaton.trace_rt; simp [zipMany]
    intro i h1 h2
    unfold CellAutomaton.trace_rt at h1 ⊢
    simp only [List.getElem_map, List.getElem_range] at *
    have h_i_lt : i < w.length := by simpa using h1
    ext b
    simp only [trace_eq_comp, ProdCA.comp]
    simp only [zipMany_get]
    simp only [CellAutomaton.trace_rt, show (List.map ((f b).trace ⟬w⟭) (List.range w.length)).getD i default
        = (f b).trace ⟬w⟭ i from by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; simp]
    simp only [trace_eq_comp]

end ProdCA


def ca_zip {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
  (C1: CellAutomaton α β1) (C2: CellAutomaton α β2) :
    CellAutomaton α (β1 × β2) :=
  (ProdCA
    (fun
      | (0: Fin 2) => C1.map_project (fun v => (v, default))
      | (1: Fin 2) => C2.map_project (fun v => (default, v))
    )
  ).map_project (fun v => ((v 0).fst, (v 1).snd))


infixr:90 " ⨂ "  => ca_zip

@[simp]
lemma ca_zip_comp {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
    {C1: CellAutomaton α β1} {C2: CellAutomaton α β2} {c: Config α} {t: ℕ} {i: ℤ}:
    (C1 ⨂ C2).comp c t i = ((C1.comp c t i), (C2.comp c t i)) := by
  simp only [ca_zip, comp_of_map_project, ProdCA.comp]


@[simp]
lemma ca_zip_trac {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
    {C1: CellAutomaton α β1} {C2: CellAutomaton α β2} {c: Config α} {t: ℕ}:
    (C1 ⨂ C2).trace c t = ((C1.trace c t), (C2.trace c t)) := by
  simp only [trace_eq_comp, ca_zip_comp]


@[simp]
lemma ca_zip_trace_rt {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
    {C1: CellAutomaton α？ β1} {C2: CellAutomaton α？ β2} {w: Word α}:
    (C1 ⨂ C2).trace_rt w = (C1.trace_rt w) ⨂ (C2.trace_rt w) := by
  simp [ca_zip]
  apply List.ext_getElem?
  intro i
  simp [ProdCA.zipMany_get?]
  by_cases h: i < List.length w
  · simp [h, List.zip]
  · simp [h, List.zip]

end CellularAutomatas
