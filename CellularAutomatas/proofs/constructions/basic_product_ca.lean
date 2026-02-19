import CellularAutomatas.defs
import Mathlib.Data.List.Basic

namespace CellularAutomatas

open CellAutomaton

@[simp]
lemma comp_of_map_project {α β γ: Type} {C: CellAutomaton α β} (f: β → γ) (c: Config α):
      (C.map_project f).comp c t i = f (C.comp c t i) := by
  rfl

@[simp]
lemma trace_of_map_project {α β γ: Type} {C: CellAutomaton α？ β} (f: β → γ) (w: Word α):
      (C.map_project f).trace w = f ∘ (C.trace w) := by
  funext i
  unfold trace comp project_config
  simp
  unfold map_project
  rfl

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
    unfold CellAutomaton.comp CellAutomaton.project_config
    unfold CellAutomaton.nextt

    have nextt_proj (c: Config (ProdCA f).Q) (t: ℕ) (i: ℤ) (b: P):
        (ProdCA f).next^[t] c i b = (f b).next^[t] (fun j => c j b) i := by
      induction t generalizing i c with
      | zero => rfl
      | succ t ih =>
        rw [Function.iterate_succ]
        rw [Function.iterate_succ]
        dsimp
        rw [ih]
        dsimp [CellAutomaton.next, ProdCA]
        rfl

    funext b
    simp
    conv in (ProdCA f).project =>
      simp [ProdCA]
    rw [nextt_proj]
    congr


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
    unfold CellAutomaton.trace_rt CellAutomaton.trace
    simp [zipMany]
    unfold embed_word
    intro t ht
    funext b
    grind

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
  simp [ca_zip]


@[simp]
lemma ca_zip_trac {α β1 β2} [Alphabet α] [Alphabet β1] [Alphabet β2]
    {C1: CellAutomaton α β1} {C2: CellAutomaton α β2} {c: Config α} {t: ℕ}:
    (C1 ⨂ C2).trace c t = ((C1.trace c t), (C2.trace c t)) := by
  unfold trace
  simp


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
