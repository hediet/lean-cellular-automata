import CellularAutomatas.defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith
import CellularAutomatas.proofs.basic

namespace CellularAutomatas




namespace FiniteStateTransducer
  section

    variable {α β : Type} {M: FiniteStateTransducer α β}

    lemma scanr_foldr_state (p: Word α) (q: M.Q) (tail: List β):
        (p.foldr M.scanr_step (q, tail)).fst = M.scanr_reduce_q q p := by
      induction p generalizing q tail with
      | nil => simp [scanr_reduce_q]
      | cons a p' ih =>
        simp [scanr_step, scanr_reduce_q]
        rw [ih]

    lemma scanr_foldr_cons (p: Word α) (q: M.Q) (tail: List β):
        (p.foldr M.scanr_step (q, tail)).snd = (M.scanr_q q p) ++ tail := by
      induction p generalizing q tail with
      | nil =>
        simp [scanr_q]
      | cons a p' ih =>
        simp [scanr_q, scanr_step]
        rw [scanr_foldr_state]
        rw [scanr_foldr_state (tail := [])]
        rw [ih]
        simp [scanr_q]

    lemma scanr_q_append (p s: Word α) (q: M.Q):
        M.scanr_q q (p ++ s) = M.scanr_q (M.scanr_reduce_q q s) p ++ M.scanr_q q s := by
      unfold scanr_q
      rw [List.foldr_append]
      let res_s := s.foldr M.scanr_step (q, [])
      have h_fst : res_s.fst = M.scanr_reduce_q q s := by
        dsimp [res_s]
        rw [scanr_foldr_state]
      have h_snd : res_s.snd = M.scanr_q q s := rfl
      rw [scanr_foldr_cons]
      rw [h_fst]
      rfl

    lemma scanr_append_take (p s: Word α):
        (M.scanr (p ++ s)).take p.length = M.scanr_q (M.scanr_reduce s) p := by
      unfold scanr
      rw [scanr_q_append]
      apply List.take_left'
      simp




    @[simp]
    lemma scanr_reduce_q_empty (q: M.Q): M.scanr_reduce_q q [] = q := by simp [FiniteStateTransducer.scanr_reduce_q]

    @[simp]
    lemma scanr_reduce_empty: M.scanr_reduce [] = M.q0 := by simp [FiniteStateTransducer.scanr_reduce]

    lemma scanr_reduce_cons (ws: Word α): M.scanr_reduce (w::ws) = M.δ (M.scanr_reduce ws) w := by rfl



    @[simp]
    lemma range_of_scanr_q {M: FiniteStateTransducer α β} {q0: M.Q} {w: Word α}: (M.scanr_q q0 w).range = w.range := by
      simp [Word.range, FiniteStateTransducer.scanr_q_len]

    @[simp]
    lemma range_of_scanr {M: FiniteStateTransducer α β} {w: Word α}: (M.scanr w).range = w.range := by
      simp [FiniteStateTransducer.scanr, range_of_scanr_q]



  /-
    lemma scanr {M: FiniteStateTransducer α β} (w: Word α) (p: Fin w.length) (q: M.Q):
        (M.scanr_q q w).get ⟨ p, by simp ⟩ = M.f (M.scanr_reduce_q q (w.drop p)) := sorry
  -/


    lemma scanr_cons (a: α) (w: Word α):
      M.scanr (a::w) = M.f (M.δ (M.scanr_reduce w) a) :: M.scanr w := by
      simp [scanr, scanr_q, scanr_step]
      rw [scanr_foldr_state]
      rfl

    lemma scanr_get'_eq2 (w: Word α) (i: Fin w.length):
      (M.scanr w)[i]'(by simp) = M.f (M.scanr_reduce w⟦i..*⟧) := by
      induction w with
      | nil =>
        exact i.elim0
      | cons a w ih =>
        simp_rw [scanr_cons]
        match i with
        | ⟨0, _⟩ =>
          rfl
        | ⟨n+1, h⟩ =>
          simp
          exact ih ⟨n, Nat.lt_of_succ_lt_succ h⟩

    lemma scanr_get'_eq1 (w: Word α) (i: Fin w.length):
      (M.scanr w)[i]'(by simp) = M.f (M.δ (M.scanr_reduce w⟦i+1..*⟧) w[i]) := by
      induction w with
      | nil =>
        exact i.elim0
      | cons a w ih =>
        simp_rw [scanr_cons]
        match i with
        | ⟨0, _⟩ =>
          rfl
        | ⟨n+1, h⟩ =>
          simp
          exact ih ⟨n, Nat.lt_of_succ_lt_succ h⟩

    lemma scanr_get'_eq (w: Word α) (i: ℤ) (h: i ∈ w.range):
      (M.scanr w).get' i (by simp [h]) = M.f (M.δ (M.scanr_reduce w⟦(i+1).toNat..*⟧) (w.get' i h)) := by
      rw [Word.get']
      have h_pos : 0 ≤ i := by simp [Word.range] at h; exact h.1
      have h_lt : i < w.length := by simp [Word.range] at h; exact h.2
      have h_nat_lt : i.toNat < w.length := by
        rwa [Int.toNat_lt h_pos]
      let idx : Fin w.length := ⟨i.toNat, h_nat_lt⟩
      have := @scanr_get'_eq1 α β M w idx
      convert this
      { grind }




    lemma scanr_reduce_drop (w: Word α) (i: Fin w.length):
      M.scanr_reduce w⟦i..*⟧ = M.δ (M.scanr_reduce w⟦i+1..*⟧) w[i] := by
      rw [List.drop_eq_getElem_cons (h := i.isLt)]
      rw [scanr_reduce_cons]
      grind


    lemma scanr_reduce'? (w: Word α) (i: ℤ):
      M.scanr_reduce (w.drop i.toNat) = M.δ? (M.scanr_reduce w⟦(i+1).toNat..*⟧) (w.get'? i) := by
      if h: i ∈ w.range then
        have h_orig := h
        rw [Word.range] at h
        simp only [Set.mem_setOf_eq] at h
        have h_pos : 0 ≤ i := h.1
        have h_lt : i < w.length := h.2
        have h_nat_lt : i.toNat < w.length := by
          rwa [Int.toNat_lt h_pos]
        rw [Word.get'?]
        rw [dif_pos h_orig]
        rw [List.drop_eq_getElem_cons (h := h_nat_lt)]
        rw [scanr_reduce_cons]
        congr
        . rw [Int.toNat_add h_pos (by decide)]; simp
      else
        rw [Word.get'?]
        rw [dif_neg h]
        rw [Word.range] at h
        simp only [Set.mem_setOf_eq] at h
        if h_neg : i < 0 then
          have h1 : i.toNat = 0 := Int.toNat_of_nonpos (le_of_lt h_neg)
          have h2 : (i+1).toNat = 0 := Int.toNat_of_nonpos (by omega)
          simp [h1, h2, FiniteStateTransducer.δ?]
        else
          have h1 : i.toNat ≥ w.length := by omega
          have h2 : (i+1).toNat ≥ w.length := by omega
          simp [List.drop_eq_nil_of_le h1]
          simp [List.drop_eq_nil_of_le h2]
          simp [FiniteStateTransducer.δ?]


    @[simp]
    lemma scanr_neq_empty {α} {M: FiniteStateTransducer α β} (w: Word α) (h: w ≠ []): (M.scanr w) ≠ [] := by
      simp_all [List.ne_nil_iff_length_pos]

    lemma getLast?_of_scanr {M: FiniteStateTransducer α β} (w: Word α) (h: w ≠ []):
        (M.scanr w).getLast (by simp [h]) = M.f (M.δ? M.q0 (w.getLast h)) := by
      induction w with
      | nil => contradiction
      | cons a w ih =>
        by_cases h' : w = []
        · subst h'
          simp [scanr, scanr_q, scanr_step, FiniteStateTransducer.δ?]
        · have hw : w ≠ [] := h'
          simp only [scanr_cons]
          erw [List.getLast_cons]
          rotate_left
          · simp [scanr_neq_empty _ hw]
          rw [ih hw]
          erw [List.getLast_cons]

  end


  section M_id

    def M_id (α) [Alphabet α]: FiniteStateTransducer α α := {
      Q := α
      δ := fun _ a => a
      q0 := default
      f := id
    }

    @[simp]
    lemma M_id_scanr_eq [Alphabet α]: (M_id α).scanr = id := by
      funext w
      simp [FiniteStateTransducer.scanr, FiniteStateTransducer.scanr_q]
      induction w with
      | nil => rfl
      | cons a w ih =>
        simp [FiniteStateTransducer.scanr_step]
        rw [ih]
        cases w <;> simp [M_id]

    @[simp]
    lemma M_id_advice_eq {α} [Alphabet α]: (M_id α).advice.f = id := by
      simp [FiniteStateTransducer.advice]
      rfl

  end M_id


  section M_projQ

    def M_projQ (M: FiniteStateTransducer α β): FiniteStateTransducer α M.Q := {
      Q := M.Q
      δ := M.δ
      q0 := M.q0
      f := id
    }


    lemma M_projQ_scanr (i: ℕ) (h: i < w.length): ((M_projQ M).scanr w)[i]'(by simp_all) = M.scanr_reduce w⟦i..*⟧ := by
      convert scanr_get'_eq2 (M := M_projQ M) w ⟨i, h⟩
      simp [M_projQ]
      generalize w⟦i..*⟧ = w'
      induction w' with
      | nil => simp
      | cons a w' ih =>
        simp [scanr_reduce_cons]
        rw [ih]

    @[simp]
    lemma M_projQ_scanr2: (M_projQ M).scanr w = w.mapIdx fun i _ => M.scanr_reduce w⟦i..*⟧ := by
      apply List.ext_get
      · simp
      intro i h1 h2
      simp
      rw [←M_projQ_scanr i]
      simp_all

  end M_projQ



  section M_prod


    def M_prod [Alphabet α1] [Alphabet α2] (M1: FiniteStateTransducer α1 β1) (M2: FiniteStateTransducer α2 β2):
        FiniteStateTransducer (α1 × α2) (β1 × β2) :=
      {
        Q := M1.Q × M2.Q
        δ := fun (m_q, c_q) (a1, a2) => (M1.δ m_q a1, M2.δ c_q a2)
        q0 := (M1.q0, M2.q0)
        f := fun (m_q, c_q) => (M1.f m_q, M2.f c_q)
      }

    private lemma m_prod_scanr_reduce_q [Alphabet α1] [Alphabet α2] {M1: FiniteStateTransducer α1 β1} {M2: FiniteStateTransducer α2 β2}
        (q1: M1.Q) (q2: M2.Q) (w: Word (α1 × α2)):
        (M_prod M1 M2).scanr_reduce_q (q1, q2) w = (M1.scanr_reduce_q q1 w.fst, M2.scanr_reduce_q q2 w.snd) := by
      induction w with
      | nil => simp [scanr_reduce_q]
      | cons a w ih =>
        rw [scanr_reduce_q]
        rw [ih]
        simp [M_prod, scanr_reduce_q]


    @[simp]
    lemma M_prod_spec [Alphabet α1] [Alphabet α2] {M1: FiniteStateTransducer α1 β1} {M2: FiniteStateTransducer α2 β2}:
        (M_prod M1 M2).scanr = fun w => List.zip (M1.scanr w.fst) (M2.scanr w.snd) := by
      funext M2X
      induction M2X with
      | nil => simp [scanr, scanr_q]
      | cons a w ih =>
        simp only [scanr_cons]
        rw [ih]
        simp only [scanr_reduce]
        rw [show (M_prod M1 M2).q0 = (M1.q0, M2.q0) from rfl]
        simp [m_prod_scanr_reduce_q]
        simp [scanr_cons]
        simp [M_prod]
        simp [scanr_reduce]

    infixr:90 " ⨂ "  => M_prod

  end M_prod


  def comp (M2: FiniteStateTransducer β γ) (M1: FiniteStateTransducer α β): FiniteStateTransducer α γ := {
    Q := M1.Q × M2.Q
    δ := fun (q1, q2) a => (M1.δ q1 a, M2.δ q2 (M1.f (M1.δ q1 a)))
    q0 := (M1.q0, M2.q0)
    f := fun (_q1, q2) => M2.f q2
  }

  infixr:90 " ⊚ "  => comp

  lemma comp_scanr_reduce_q
      {M2: FiniteStateTransducer β γ} {M1: FiniteStateTransducer α β}
      (q1: M1.Q) (q2: M2.Q) (w: Word α):
      (M2 ⊚ M1).scanr_reduce_q (q1, q2) w = (M1.scanr_reduce_q q1 w, M2.scanr_reduce_q q2 (M1.scanr_q q1 w)) := by
    induction w with
    | nil => simp [scanr_reduce_q, scanr_q]
    | cons a w ih =>
      simp only [scanr_reduce_q]
      rw [ih]
      simp only [comp]
      have h_scanr_q : M1.scanr_q q1 (a::w) = M1.f (M1.δ (M1.scanr_reduce_q q1 w) a) :: M1.scanr_q q1 w := by
            simp [scanr_q, scanr_step]
            rw [scanr_foldr_state]
      rw [h_scanr_q]
      simp [scanr_reduce_q]

  lemma comp_scanr_q
      {M2: FiniteStateTransducer β γ} {M1: FiniteStateTransducer α β}
      (q1: M1.Q) (q2: M2.Q) (w: Word α):
      (M2 ⊚ M1).scanr_q (q1, q2) w = M2.scanr_q q2 (M1.scanr_q q1 w) := by
    induction w with
    | nil => simp [scanr_q]
    | cons a w ih =>
      have h_scanr_q_M1 : M1.scanr_q q1 (a::w) = M1.f (M1.δ (M1.scanr_reduce_q q1 w) a) :: M1.scanr_q q1 w := by
            simp [scanr_q, scanr_step]
            rw [scanr_foldr_state]
      rw [h_scanr_q_M1]

      have h_scanr_q_M2 : M2.scanr_q q2 (M1.f (M1.δ (M1.scanr_reduce_q q1 w) a) :: M1.scanr_q q1 w) =
            M2.f (M2.δ (M2.scanr_reduce_q q2 (M1.scanr_q q1 w)) (M1.f (M1.δ (M1.scanr_reduce_q q1 w) a))) :: M2.scanr_q q2 (M1.scanr_q q1 w) := by
            simp [scanr_q, scanr_step]
            rw [scanr_foldr_state]
      rw [h_scanr_q_M2]

      have h_scanr_q_comp : (M2 ⊚ M1).scanr_q (q1, q2) (a::w) =
            (M2 ⊚ M1).f ((M2 ⊚ M1).δ ((M2 ⊚ M1).scanr_reduce_q (q1, q2) w) a) :: (M2 ⊚ M1).scanr_q (q1, q2) w := by
            simp [scanr_q, scanr_step]
            rw [scanr_foldr_state]
      rw [h_scanr_q_comp]

      rw [ih]
      rw [comp_scanr_reduce_q]
      simp [comp]

  @[simp]
  theorem compose_spec2
    (M2: FiniteStateTransducer β γ) (M1: FiniteStateTransducer α β):
      (M2 ⊚ M1).scanr = M2.scanr ∘ M1.scanr := by
    funext w
    simp [scanr]
    apply comp_scanr_q


  theorem compose_spec [Alphabet α] [Alphabet β] [Alphabet γ]
    (M1: FiniteStateTransducer β γ) (M2: FiniteStateTransducer α β):
      (M1 ⊚ M2).advice.f = M1.advice.f ∘ M2.advice.f := by
    funext w
    simp [compose_spec2, FiniteStateTransducer.advice]





  section M_map

    def M_map [Alphabet α] (f: α → β): FiniteStateTransducer α β := {
      Q := α
      δ := fun _ a => a
      q0 := default
      f := f
    }

    @[simp]
    lemma M_map_scanr [Alphabet α] (f: α → β): (M_map f).scanr = List.map f := by
      funext w
      simp [scanr, scanr_q, M_map]
      induction w with
      | nil => rfl
      | cons a w ih =>
        simp [scanr_step]
        rw [ih]

  end M_map


  def map_output [Alphabet α] [Alphabet β] [Alphabet γ]
      (M: FiniteStateTransducer α β) (g: β → γ): FiniteStateTransducer α γ := M_map g ⊚ M

  @[simp]
  lemma map_output_spec [Alphabet α] [Alphabet β] [Alphabet γ] {M: FiniteStateTransducer α β} {g: β → γ}:
      (M.map_output g).scanr = (List.map g) ∘ M.scanr := by simp [FiniteStateTransducer.map_output]


  def M_prod2 [Alphabet α] (M1: FiniteStateTransducer α β1) (M2: FiniteStateTransducer α β2):
      FiniteStateTransducer α (β1 × β2) := (M_prod M1 M2) ⊚ (M_map fun a => (a, a))

  @[simp]
  lemma zip_with_eq: List.map (fun a => (a, a)) w = w ⨂ w := by simp [zip_words]

  @[simp]
  lemma M_prod2_spec [Alphabet α] {M1: FiniteStateTransducer α β1} {M2: FiniteStateTransducer α β2}:
      (M_prod2 M1 M2).scanr = fun w => List.zip (M1.scanr w) (M2.scanr w) := by
      funext w
      simp [M_prod2]

  infixr:90 " ⨂₂ "  => M_prod2

end FiniteStateTransducer
