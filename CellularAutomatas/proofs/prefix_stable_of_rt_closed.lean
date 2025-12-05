import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Computability.Language
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import CellularAutomatas.defs
import CellularAutomatas.proofs.scan_lemmas

open Classical

attribute [ext] Advice

variable {α: Type u} [Alphabet α]
variable {Γ: Type u} [Alphabet Γ]

namespace prefix_stable_of_rt_closed

  axiom advice_prefixes_in_L_rt_closed (C: CA_rt α):
    (Advice.prefixes_in_L C.val.L).rt_closed

  def L_c (adv: Advice α Γ) (c: Γ) : Language α :=
    { w | (adv.f w).getLast? = some c }

  lemma L_c_in_rt (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) :
      ∃ M : tCellAutomaton α, M ∈ CA_rt α ∧ M.L = L_c adv c := by
    let myCA : tCellAutomaton (α × Γ) := {
      Q := Option (α × Γ)
      decQ := inferInstance
      finQ := inferInstance
      δ := fun _ _ r => r
      embed := some
      border := none
      t := fun n => n - 1
      p := fun _ => 0
      F_pos := fun q => match q with
        | some (_, g) => g == c
        | none => false
    }
    have h_CA_in_rt : myCA ∈ CA_rt (α × Γ) := by
      simp [CA_rt, t_rt, myCA, tCellAutomatons, CA]

    let O : OCellAutomaton α := ⟨Γ, adv, myCA⟩
    have h_L : O.L = L_c adv c := by
      ext w
      simp [OCellAutomaton.L, L_c, tCellAutomaton.L, O, myCA]
      unfold LCellAutomaton.comp
      unfold CellAutomaton.nextt
      unfold LCellAutomaton.embed_word
      unfold Advice.annotate
      unfold tensor_product

      cases h_len : w.length with
      | zero =>
        simp
        rw [List.length_eq_zero_iff] at h_len
        subst h_len
        simp [Word.range, LCellAutomaton.embed_word, apply_iterated]
        simp [LCellAutomaton.embed_word]
        split
        · simp at ⊢
        · simp
      | succ n =>
        simp
        have h_next : ∀ c, myCA.toCellAutomaton.next c = fun i => c (i + 1) := by
          intro c
          funext i
          simp [CellAutomaton.next, myCA]

        have shift_lemma : ∀ k i, (myCA.toCellAutomaton.nextt (myCA.toLCellAutomaton.embed_word (w ⊗ adv.f w)) k) i =
          (myCA.toLCellAutomaton.embed_word (w ⊗ adv.f w)) (i + k) := by
          intro k
          induction k with
          | zero => simp [CellAutomaton.nextt, apply_iterated]
          | succ k ih =>
            intro i
            simp [CellAutomaton.nextt, apply_iterated]
            rw [h_next]
            simp
            rw [ih]
            ring_nf

        simp [CellAutomaton.nextt]
        rw [shift_lemma]
        simp
        have h_idx : 0 + (w.length - 1) = n := by
          rw [h_len]
          simp
        rw [h_idx]

        have h_in_range : (n : ℤ) ∈ (w ⊗ adv.f w).range := by
          unfold Word.range
          simp
          rw [List.length_zipWith]
          rw [adv.len]
          simp [h_len]
          omega

        simp [LCellAutomaton.embed_word, h_in_range]
        unfold Word.get'
        simp
        rw [List.getElem_zipWith]
        simp
        have h_last : (adv.f w)[n] = (adv.f w).getLast (by rw [adv.len, h_len]; simp) := by
          rw [List.getLast_eq_getElem]
          congr
          rw [adv.len, h_len]
          simp
        rw [h_last]
        simp
        rw [List.getLast?_eq_getLast]
        simp
        rw [adv.len, h_len]; simp

    have h_in : O.L ∈ ℒ (CA_rt (α × Γ) + adv) := by
      use O
      constructor
      · use myCA
        simp [h_CA_in_rt]
      · rfl

    rw [h] at h_in
    rcases h_in with ⟨M, hM_in, hM_L⟩
    use M
    constructor
    · exact hM_in
    · change DefinesLanguage.L M = L_c adv c
      rw [← hM_L, h_L]
  noncomputable def M_c (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) : tCellAutomaton α :=
    Classical.choose (L_c_in_rt adv h c)

  lemma M_c_spec (adv: Advice α Γ) (h: adv.rt_closed) (c: Γ) :
    (M_c adv h c) ∈ CA_rt α ∧ (M_c adv h c).L = L_c adv c :=
    Classical.choose_spec (L_c_in_rt adv h c)

  instance PiAlphabet {I : Type u} [Alphabet I] {Z : I → Type v} [∀ i, Alphabet (Z i)] : Alphabet (∀ i, Z i) where
    dec := inferInstance
    fin := inferInstance
    inh := inferInstance

  lemma scanr_id {Q : Type u} [Alphabet Q] (w : Word Q) (q0 : Q) (δ : Q → Q → Q) (h_id : ∀ q a, δ q a = a) :
    let M : FiniteStateMachine Q := { Q := Q, decQ := inferInstance, finQ := inferInstance, δ := δ, q0 := q0 }
    M.scanr w = w := by
    simp [FiniteStateMachine.scanr, FiniteStateMachine.scanr_q]
    induction w with
    | nil => simp
    | cons a w ih =>
      simp [List.foldr]
      rw [ih]
      cases w <;> simp [FiniteStateMachine.scanr_step, h_id]


theorem prefix_stable_of_rt_closed (adv: Advice α Γ) (h1: adv.rt_closed) (h2: adv.prefix_stable) :
    adv.is_two_stage_advice := by
  -- Construct the product automaton
  let M_prod : LCellAutomaton α := {
    Q := ∀ c: Γ, (M_c adv h1 c).Q
    decQ := inferInstance
    finQ := inferInstance
    δ := fun qL qC qR c => (M_c adv h1 c).δ (qL c) (qC c) (qR c)
    embed := fun a c => (M_c adv h1 c).embed a
    border := fun c => (M_c adv h1 c).border
  }

  -- Define the trivial FSM
  let M_fsm : FiniteStateMachine M_prod.Q := {
    Q := M_prod.Q
    decQ := inferInstance
    finQ := inferInstance
    δ := fun _ a => a -- Identity transition on input
    q0 := M_prod.border -- Dummy initial state
  }

  -- Define the mapping t
  let t_map (q: M_prod.Q) : Γ :=
    let valid_c := { c | (M_c adv h1 c).F_pos (q c) }
    if h: ∃! c, c ∈ valid_c then
      Classical.choose h.exists
    else
      default

  let ts_adv : TwoStageAdvice α Γ := {
    C := M_prod
    M := M_fsm
    t := t_map
  }

  use ts_adv
  apply Advice.ext
  ext w
  simp [TwoStageAdvice.advice]
  have h_id : ∀ q a, M_fsm.δ q a = a := fun _ _ => rfl
  rw [scanr_id (ts_adv.C.scan_temporal w) M_fsm.q0 M_fsm.δ h_id]

  have h_goal : adv.f w = List.map ts_adv.t (ts_adv.C.scan_temporal w) := by
    refine List.ext_getElem ?_ ?_
    · simp [adv.len, LCellAutomaton.scan_temporal]
    · intro i h_i h_len
      have h_w_len : i < w.length := by rw [← adv.len w]; exact h_i
      have h_scan_len : i < (M_prod.scan_temporal w).length := by simp [LCellAutomaton.scan_temporal, h_w_len]

      let q := (M_prod.scan_temporal w)[i]
      have h_q : q = (M_prod.scan_temporal w)[i] := rfl

      -- Analyze q
      -- q c = ((M_c adv h1 c).scan_temporal w)[i]
      -- We need to prove this component-wise property of scan_temporal for product CA
      have h_comp : ∀ c, q c = ((M_c adv h1 c).scan_temporal w)[i] := by
        intro c
        rw [h_q]
        have h_c_len : i < ((M_c adv h1 c).scan_temporal w).length := by simp [LCellAutomaton.scan_temporal, h_w_len]
        unfold LCellAutomaton.scan_temporal
        rw [List.getElem_map]
        simp
        -- Need to show (M_prod.comp w i 0) c = (M_c c).comp w i 0
        -- This follows from definition of M_prod
        unfold LCellAutomaton.comp
        unfold CellAutomaton.nextt
        -- Induction on time i
        -- Base case i=0: embed
        -- Step: next
        generalize h_idx : (0 : ℤ) = idx
        induction i generalizing idx with
        | zero =>
          simp [apply_iterated]
          unfold LCellAutomaton.embed_word
          split_ifs
          · rfl
          · rfl
        | succ i ih =>
          simp [apply_iterated]
          unfold CellAutomaton.next
          rw [ih, ih, ih]
          rfl
        simp [LCellAutomaton.scan_temporal, h_w_len]

      -- Now use scan_temporal_independence
      -- ((M_c c).scan_temporal w)[i] depends only on w[0..i+1]
      -- Let w_pref = w.take (i+1)
      let w_pref := w.take (i+1)
      let w_suff := w.drop (i+1)
      have h_w : w = w_pref ++ w_suff := (List.take_append_drop (i+1) w).symm

      have h_q_c : ∀ c, q c = ((M_c adv h1 c).scan_temporal w_pref)[i]'(by simp [w_pref, LCellAutomaton.scan_temporal]; omega) := by
        intro c
        rw [h_comp c]
        have h_indep := scan_lemmas.scan_temporal_independence (M_c adv h1 c).toLCellAutomaton w_pref w_suff
        rw [h_w]
        rw [h_indep]
        rw [List.getElem_append_left]
        · simp [LCellAutomaton.scan_temporal]
          simp [w_pref]
          omega

      -- Relate to acceptance
      have h_accept : ∀ c, (M_c adv h1 c).F_pos (q c) ↔ w_pref ∈ (M_c adv h1 c).L := by
        intro c
        rw [h_q_c]
        have h_rt := (M_c_spec adv h1 c).1
        simp [CA_rt, t_rt] at h_rt
        unfold tCellAutomaton.L
        simp
        rw [h_rt w_pref.length]
        simp
        have h_len_pref : w_pref.length = i + 1 := by
          simp [w_pref]
          omega
        rw [h_len_pref]
        simp
        -- (comp w_pref i) 0 is exactly (scan_temporal w_pref)[i]
        unfold LCellAutomaton.scan_temporal
        rw [List.getElem_map]
        · rfl
        · simp [LCellAutomaton.scan_temporal, h_len_pref]; omega

      -- Relate to L_c
      have h_Lc : ∀ c, w_pref ∈ (M_c adv h1 c).L ↔ c = (adv.f w)[i] := by
        intro c
        rw [(M_c_spec adv h1 c).2]
        unfold L_c
        simp
        -- (adv.f w_pref).getLast? = some c
        rw [h2 w (i+1)] -- prefix_stable: adv.f (w.take (i+1)) = (adv.f w).take (i+1)
        -- (adv.f w).take (i+1) getLast? = some c
        rw [List.getLast?_eq_some_iff]
        constructor
        · intro h
          rcases h with ⟨_, h_last⟩
          rw [List.getLast_take] at h_last
          · simp at h_last
            rw [h_last]
          · simp [adv.len]; omega
        · intro h
          subst h
          constructor
          · simp [adv.len]; omega
          · rw [List.getLast_take]
            · simp
            · simp [adv.len]; omega

      -- Combine
      have h_iff : ∀ c, (M_c adv h1 c).F_pos (q c) ↔ c = (adv.f w)[i] := by
        intro c
        rw [h_accept, h_Lc]

      -- Uniqueness
      let target_c := (adv.f w)[i]
      have h_unique : ∃! c, (M_c adv h1 c).F_pos (q c) := by
        use target_c
        simp [h_iff]

      -- t_map
      rw [List.getElem_map]
      · change (adv.f w)[i] = ts_adv.t q
        simp [ts_adv]
        simp [t_map]
        rw [dif_pos h_unique]
        -- Classical.choose h.exists is target_c
        have h_choose : Classical.choose h_unique.exists = target_c := by
          apply h_unique.unique
          · exact Classical.choose_spec h_unique.exists
          · rw [h_iff]
        rw [h_choose]
      · simp [LCellAutomaton.scan_temporal, h_w_len]

  rw [h_goal]
  simp [List.getElem?_map]
