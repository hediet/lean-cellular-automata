import CellularAutomatas.proofs.constructions.two_sided_fssp_half_runtime
import CellularAutomatas.proofs.basic
import CellularAutomatas.proofs.constructions.fssp_mazoyer.bridge
import CellularAutomatas.proofs.constructions.fssp_mazoyer.small_handler

/-!
# Full two-sided FSSP from the parity-specific half simulations

The odd and even moving-boundary automata run in parallel, together with their
spatial reflections. A finite router detects the central collision parity and
propagates an oriented selection back toward both ends. At time `n - 1`, every
input cell selects exactly the half simulation that contains it.
-/

namespace CellularAutomatas
namespace TwoSidedFSSP

open CellAutomaton

private lemma word_to_config_flip_shift_local {α : Type} (w : Word α) :
    (fun p => (word_to_config w).flip (p + (1 - (w.length : ℤ)))) =
      word_to_config w.reverse := by
  funext p
  simp only [Config.flip_apply, word_to_config, List.length_reverse]
  have h_idx : -(p + (1 - (w.length : ℤ))) = (w.length : ℤ) - 1 - p := by
    ring
  rw [h_idx]
  split_ifs with h1 h2 h2
  · have h_idx2 : ((w.length : ℤ) - 1 - p).toNat =
        w.length - 1 - p.toNat := by
      omega
    simp only [h_idx2, List.getElem_reverse]
  · omega
  · omega
  · rfl

/-- Swap the left- and right-endpoint flags. -/
def swapEnds (a : Bool × Bool) : Bool × Bool := (a.2, a.1)

@[simp] lemma fssp_both_sides_map_swapEnds (n : ℕ) :
    (fssp_both_sides n).map swapEnds = (fssp_both_sides n).reverse := by
  rcases n with _ | _ | n <;>
    simp [fssp_both_sides, swapEnds, List.reverse_append]

/-- A spatially reflected CA whose input endpoint flags are swapped. -/
def reflected (A : CellAutomaton (Bool × Bool)？ Bool) :
    CellAutomaton (Bool × Bool)？ Bool :=
  A.flip.map_embed (Option.map swapEnds)

/-- Reflection sends position `p` to `n - 1 - p` on the endpoint-marked
    input of length `n`. -/
theorem reflected_comp_fssp (A : CellAutomaton (Bool × Bool)？ Bool)
    (n t : ℕ) (p : ℤ) :
    (reflected A).comp ⟬fssp_both_sides n⟭ t p =
      A.comp ⟬fssp_both_sides n⟭ t ((n : ℤ) - 1 - p) := by
  let w := fssp_both_sides n
  have h_word : (word_to_config (w.map swapEnds)).flip =
      fun q => word_to_config w (q + ((n : ℤ) - 1)) := by
    rw [show w.map swapEnds = w.reverse from fssp_both_sides_map_swapEnds n]
    funext q
    calc
      (word_to_config w.reverse).flip q = word_to_config w.reverse (-q) := rfl
      _ = (word_to_config w).flip (-q + (1 - (w.length : ℤ))) :=
        (congrFun (word_to_config_flip_shift_local w) (-q)).symm
      _ = word_to_config w (q + ((n : ℤ) - 1)) := by
        simp only [Config.flip_apply]
        rw [show w.length = n from fssp_both_sides_length n]
        congr 1
        ring
  have h_initial :
      (@embed_config _ _ A.flip (word_to_config (w.map swapEnds))).flip =
        fun q => @embed_config _ _ A (word_to_config w) (q + ((n : ℤ) - 1)) := by
    funext q
    simp only [Config.flip_apply, embed_config_apply, CellAutomaton.flip]
    exact congrArg A.embed (congrFun h_word q)
  show (reflected A).project
      ((reflected A).nextt ⦋fssp_both_sides n⦌ t p) =
    A.project (A.nextt ⦋fssp_both_sides n⦌ t ((n : ℤ) - 1 - p))
  rw [show fssp_both_sides n = w from rfl]
  change A.project
      ((A.flip.map_embed (Option.map swapEnds)).nextt ⦋w⦌ t p) = _
  rw [map_embed_nextt_word A.flip swapEnds w t p]
  rw [A.flip_nextt]
  simp only [Config.flip_apply]
  rw [h_initial]
  have h_shift := nextt_shift A (⦋word_to_config w⦌) t (-p) ((n : ℤ) - 1)
  rw [← h_shift]
  congr 2
  ring

/-- Control states for selecting a parity-specific, oriented half simulation. -/
inductive Route
  | border
  | quiet
  | R
  | L
  | singleton
  | evenSmallLeft
  | evenSmallRight
  | oddLeft
  | oddCenter
  | oddRight
  | evenLeft
  | evenRight
  deriving DecidableEq, Repr, Fintype, Inhabited

instance : Alphabet Route := {}

/-- Initial router state from the two endpoint flags. -/
def initRoute : (Bool × Bool)？ → Route
  | none => .border
  | some (true, true) => .singleton
  | some (true, false) => .R
  | some (false, true) => .L
  | some (false, false) => .quiet

/-- Router transition.

Selected states persist and spread outward. Before selection, `R` and `L`
move inward. A one-cell gap detects odd length; adjacency detects even length.
The two length-two collisions are distinguished by the adjacent outer border. -/
def routeStep : Route → Route → Route → Route
  | _, .border, _ => .border
  | _, .singleton, _ => .singleton
  | _, .evenSmallLeft, _ => .evenSmallLeft
  | _, .evenSmallRight, _ => .evenSmallRight
  | _, .oddLeft, _ => .oddLeft
  | _, .oddCenter, _ => .oddCenter
  | _, .oddRight, _ => .oddRight
  | _, .evenLeft, _ => .evenLeft
  | _, .evenRight, _ => .evenRight
  | _, _, .oddCenter => .oddLeft
  | _, _, .oddLeft => .oddLeft
  | .oddCenter, _, _ => .oddRight
  | .oddRight, _, _ => .oddRight
  | _, _, .evenLeft => .evenLeft
  | .evenRight, _, _ => .evenRight
  | .border, .R, .L => .evenSmallLeft
  | .R, .L, .border => .evenSmallRight
  | _, .R, .L => .evenLeft
  | .R, .L, _ => .evenRight
  | .R, _, .L => .oddCenter
  | .R, _, _ => .R
  | _, _, .L => .L
  | _, _, _ => .quiet

/-- Explicit initial route on an input of length `n`. -/
def routeAt0 (n : ℕ) (p : ℤ) : Route :=
  if p < 0 ∨ (n : ℤ) ≤ p then .border
  else if n = 1 then .singleton
  else if p = 0 then .R
  else if p = (n : ℤ) - 1 then .L
  else .quiet

/-- Standalone router evolution. -/
def routeAt (n : ℕ) : ℕ → ℤ → Route
  | 0, p => routeAt0 n p
  | t + 1, p => routeStep (routeAt n t (p - 1)) (routeAt n t p) (routeAt n t (p + 1))

/-- The finite router as a cellular automaton. -/
def routerCA : CellAutomaton (Bool × Bool)？ Route where
  Q := Route
  δ := routeStep
  embed := initRoute
  project := id

lemma initRoute_fssp (n : ℕ) (p : ℤ) :
    initRoute (word_to_config (fssp_both_sides n) p) = routeAt0 n p := by
  by_cases hp_in : 0 ≤ p ∧ p < (n : ℤ)
  · have hp_nat : p.toNat < n := by omega
    have hp_toNat : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp_in.1
    rw [word_to_config_apply, dif_pos (by simpa using hp_in)]
    rw [fssp_both_sides_getElem_eq n p.toNat hp_nat]
    unfold routeAt0
    rw [if_neg (by omega)]
    by_cases hn_one : n = 1
    · subst n
      have hp_zero : p = 0 := by omega
      subst p
      rfl
    · rw [if_neg hn_one]
      have hn_two : 2 ≤ n := by omega
      by_cases hp_zero : p = 0
      · subst p
        simp [initRoute, show 0 ≠ n - 1 by omega]
      · rw [if_neg hp_zero]
        by_cases hp_last : p = (n : ℤ) - 1
        · rw [if_pos hp_last]
          have hp_nat_last : p.toNat = n - 1 := by omega
          simp [initRoute, hp_nat_last, show n - 1 ≠ 0 by omega]
        · rw [if_neg hp_last]
          have hp_nat_zero : p.toNat ≠ 0 := by omega
          have hp_nat_last : p.toNat ≠ n - 1 := by omega
          simp [initRoute, hp_nat_zero, hp_nat_last]
  · rw [word_to_config_apply, dif_neg (by simpa [fssp_both_sides_length] using hp_in)]
    unfold routeAt0
    rw [if_pos (by omega)]
    rfl

theorem routerCA_nextt_fssp (n t : ℕ) (p : ℤ) :
    routerCA.nextt ⦋fssp_both_sides n⦌ t p = routeAt n t p := by
  induction t generalizing p with
  | zero => exact initRoute_fssp n p
  | succ t ih =>
      rw [nextt_succ, next_apply]
      change routeStep _ _ _ = routeStep _ _ _
      rw [ih, ih, ih]

@[simp] theorem routerCA_comp_fssp (n t : ℕ) (p : ℤ) :
    routerCA.comp ⟬fssp_both_sides n⟭ t p = routeAt n t p := by
  rw [CellAutomaton.comp_apply, routerCA_nextt_fssp]
  rfl

@[simp] lemma routeAt_zero (n : ℕ) (p : ℤ) : routeAt n 0 p = routeAt0 n p := rfl

@[simp] lemma routeAt_succ (n t : ℕ) (p : ℤ) :
    routeAt n (t + 1) p =
      routeStep (routeAt n t (p - 1)) (routeAt n t p) (routeAt n t (p + 1)) := rfl

/-- Closed form of the router on an odd input `2 * k + 1`, for `k ≥ 1`. -/
def oddRouteShape (k t : ℕ) (p : ℤ) : Route :=
  if p < 0 ∨ 2 * (k : ℤ) < p then .border
  else if (t : ℤ) < k then
    if p = (t : ℤ) then .R
    else if p = 2 * (k : ℤ) - (t : ℤ) then .L
    else .quiet
  else if 2 * (k : ℤ) - (t : ℤ) ≤ p ∧ p < k then .oddLeft
  else if p = (k : ℤ) then .oddCenter
  else if (k : ℤ) < p ∧ p ≤ (t : ℤ) then .oddRight
  else .quiet

/-- Closed form of the router on an even input `2 * k`, for `k ≥ 2`. -/
def evenRouteShape (k t : ℕ) (p : ℤ) : Route :=
  if p < 0 ∨ 2 * (k : ℤ) ≤ p then .border
  else if (t : ℤ) < k then
    if p = (t : ℤ) then .R
    else if p = 2 * (k : ℤ) - 1 - (t : ℤ) then .L
    else .quiet
  else if 2 * (k : ℤ) - 1 - (t : ℤ) ≤ p ∧ p < k then .evenLeft
  else if (k : ℤ) ≤ p ∧ p ≤ (t : ℤ) then .evenRight
  else .quiet

lemma routeAt0_odd (k : ℕ) (hk : k ≥ 1) (p : ℤ) :
    routeAt0 (2 * k + 1) p = oddRouteShape k 0 p := by
  unfold routeAt0 oddRouteShape
  split_ifs <;> first | rfl | (exfalso; push_cast at *; omega)

set_option maxHeartbeats 2000000 in
lemma oddRouteShape_succ (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ) :
    routeStep (oddRouteShape k t (p - 1))
      (oddRouteShape k t p) (oddRouteShape k t (p + 1)) =
        oddRouteShape k (t + 1) p := by
  unfold oddRouteShape routeStep
  split_ifs <;> first
    | rfl
    | contradiction
    | (exfalso; push_cast at *; omega)

theorem routeAt_odd (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ) :
    routeAt (2 * k + 1) t p = oddRouteShape k t p := by
  induction t generalizing p with
  | zero => exact routeAt0_odd k hk p
  | succ t ih =>
      rw [routeAt_succ, ih (p - 1), ih p, ih (p + 1)]
      exact oddRouteShape_succ k hk t p

lemma routeAt0_even (k : ℕ) (hk : k ≥ 2) (p : ℤ) :
    routeAt0 (2 * k) p = evenRouteShape k 0 p := by
  unfold routeAt0 evenRouteShape
  split_ifs <;> first | rfl | (exfalso; push_cast at *; omega)

set_option maxHeartbeats 2000000 in
lemma evenRouteShape_succ (k : ℕ) (hk : k ≥ 2) (t : ℕ) (p : ℤ) :
    routeStep (evenRouteShape k t (p - 1))
      (evenRouteShape k t p) (evenRouteShape k t (p + 1)) =
        evenRouteShape k (t + 1) p := by
  unfold evenRouteShape routeStep
  split_ifs <;> first
    | rfl
    | contradiction
    | (exfalso; push_cast at *; omega)

theorem routeAt_even (k : ℕ) (hk : k ≥ 2) (t : ℕ) (p : ℤ) :
    routeAt (2 * k) t p = evenRouteShape k t p := by
  induction t generalizing p with
  | zero => exact routeAt0_even k hk p
  | succ t ih =>
      rw [routeAt_succ, ih (p - 1), ih p, ih (p + 1)]
      exact evenRouteShape_succ k hk t p

@[simp] lemma routeAt_one (t : ℕ) : routeAt 1 t 0 = .singleton := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [routeAt_succ, ih]
      rfl

@[simp] lemma routeAt_two_zero_left : routeAt 2 0 0 = .R := by decide

@[simp] lemma routeAt_two_zero_right : routeAt 2 0 1 = .L := by decide

@[simp] lemma routeAt_two_succ_left (t : ℕ) :
    routeAt 2 (t + 1) 0 = .evenSmallLeft := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [routeAt_succ, ih]
      rfl

@[simp] lemma routeAt_two_succ_right (t : ℕ) :
    routeAt 2 (t + 1) 1 = .evenSmallRight := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [routeAt_succ, ih]
      rfl

abbrev TrackOutputs := Route × (Bool × (Bool × (Bool × Bool)))

/-- Read the output selected by the router from the odd-left, odd-right,
    even-left, and even-right tracks, in that order. -/
def selectTrack : TrackOutputs → Bool
  | (.singleton, _, _, _, _) => true
  | (.evenSmallLeft, _, _, _, _) => true
  | (.evenSmallRight, _, _, _, _) => true
  | (.oddLeft, oddLeft, _, _, _) => oddLeft
  | (.oddCenter, oddLeft, _, _, _) => oddLeft
  | (.oddRight, _, oddRight, _, _) => oddRight
  | (.evenLeft, _, _, evenLeft, _) => evenLeft
  | (.evenRight, _, _, _, evenRight) => evenRight
  | _ => false

/-- Router and four parity/orientation simulations running in parallel. -/
def tracks (C : CellAutomaton Bool？ Bool) :
    CellAutomaton (Bool × Bool)？ TrackOutputs :=
  routerCA ⨂
    (OddTwoSidedBetaBoundary.ca C ⨂
      (reflected (OddTwoSidedBetaBoundary.ca C) ⨂
        (EvenTwoSidedBetaBoundary.ca C ⨂
          reflected (EvenTwoSidedBetaBoundary.ca C))))

/-- The fixed two-sided automaton obtained by selecting one of the four
    one-sided simulation tracks at each cell. -/
def solver (C : CellAutomaton Bool？ Bool) :
    CellAutomaton (Bool × Bool)？ Bool :=
  (tracks C).map_project selectTrack

@[simp] theorem solver_comp_fssp (C : CellAutomaton Bool？ Bool)
    (n t : ℕ) (p : ℤ) :
    (solver C).comp ⟬fssp_both_sides n⟭ t p =
      selectTrack
        (routeAt n t p,
          (OddTwoSidedBetaBoundary.ca C).comp
            ⟬fssp_both_sides n⟭ t p,
          (reflected (OddTwoSidedBetaBoundary.ca C)).comp
            ⟬fssp_both_sides n⟭ t p,
          (EvenTwoSidedBetaBoundary.ca C).comp
            ⟬fssp_both_sides n⟭ t p,
          (reflected (EvenTwoSidedBetaBoundary.ca C)).comp
            ⟬fssp_both_sides n⟭ t p) := by
  simp [solver, tracks]

private lemma quiescent_of_mem {α β : Type} (A : CellAutomaton α β)
    {states : Set A.Q} (hstates : A.quiescent_set states)
    {q : A.Q} (hq : q ∈ states) : A.quiescent q := by
  rw [CellAutomaton.quiescent_iff]
  exact hstates ⟨q, hq⟩ ⟨q, hq⟩ ⟨q, hq⟩

private lemma ca_zip_quiescent_border {α β γ : Type}
    [Alphabet α] [Alphabet β] [Alphabet γ]
    (A : CellAutomaton α？ β) (B : CellAutomaton α？ γ)
    (hA : A.quiescent A.border) (hB : B.quiescent B.border) :
    (A ⨂ B).quiescent (A ⨂ B).border := by
  rw [CellAutomaton.quiescent_iff] at hA hB ⊢
  funext component
  refine Fin.cases ?_ (fun component => Fin.cases ?_ (fun empty => Fin.elim0 empty) component) component
  · exact hA
  · exact hB

private lemma ca_zip_quiescent_border_inner {α β γ : Type}
    [Alphabet α] [Alphabet β] [Alphabet γ]
    (A : CellAutomaton α？ β) (B : CellAutomaton α？ γ) (input : α)
    (hA : A.quiescent_set {A.border, A.inner input})
    (hB : B.quiescent_set {B.border, B.inner input}) :
    (A ⨂ B).quiescent_set {(A ⨂ B).border, (A ⨂ B).inner input} := by
  intro ⟨left, hleft⟩ ⟨center, hcenter⟩ ⟨right, hright⟩
  have inA (state : (A ⨂ B).Q)
      (hstate : state ∈ ({(A ⨂ B).border, (A ⨂ B).inner input} : Set (A ⨂ B).Q)) :
      (state (0 : Fin 2) : A.Q) ∈ ({A.border, A.inner input} : Set A.Q) := by
    rcases hstate with hstate | hstate
    · exact Or.inl (congrFun hstate 0)
    · exact Or.inr (congrFun hstate 0)
  have inB (state : (A ⨂ B).Q)
      (hstate : state ∈ ({(A ⨂ B).border, (A ⨂ B).inner input} : Set (A ⨂ B).Q)) :
      (state (1 : Fin 2) : B.Q) ∈ ({B.border, B.inner input} : Set B.Q) := by
    rcases hstate with hstate | hstate
    · exact Or.inl (congrFun hstate 1)
    · exact Or.inr (congrFun hstate 1)
  funext component
  refine Fin.cases ?_ (fun component => Fin.cases ?_ (fun empty => Fin.elim0 empty) component) component
  · exact hA ⟨left 0, inA left hleft⟩ ⟨center 0, inA center hcenter⟩
      ⟨right 0, inA right hright⟩
  · exact hB ⟨left 1, inB left hleft⟩ ⟨center 1, inB center hcenter⟩
      ⟨right 1, inB right hright⟩

private lemma reflected_quiescent_border
    (A : CellAutomaton (Bool × Bool)？ Bool)
    (hA : A.quiescent A.border) :
    (reflected A).quiescent (reflected A).border := by
  rw [CellAutomaton.quiescent_iff] at hA ⊢
  simpa [reflected, CellAutomaton.flip, CellAutomaton.map_embed,
    CellAutomaton.border] using hA

theorem solver_quiescent_border (C : CellAutomaton Bool？ Bool)
    (hC : SolvesFSSPOptimal C) :
    (solver C).quiescent (solver C).border := by
  have hrouter : routerCA.quiescent routerCA.border := by
    rw [CellAutomaton.quiescent_iff]
    rfl
  have hodd : (OddTwoSidedBetaBoundary.ca C).quiescent
      (OddTwoSidedBetaBoundary.ca C).border :=
    quiescent_of_mem _
      (OddTwoSidedBetaBoundary.spec_quiescent_set C hC.quiescent_set) (by simp)
  have heven : (EvenTwoSidedBetaBoundary.ca C).quiescent
      (EvenTwoSidedBetaBoundary.ca C).border :=
    quiescent_of_mem _
      (EvenTwoSidedBetaBoundary.spec_quiescent_set C hC.quiescent_set) (by simp)
  exact ca_zip_quiescent_border routerCA _ hrouter
    (ca_zip_quiescent_border _ _ hodd
      (ca_zip_quiescent_border _ _ (reflected_quiescent_border _ hodd)
        (ca_zip_quiescent_border _ _ heven
          (reflected_quiescent_border _ heven))))

@[simp] theorem solver_border_projects_false (C : CellAutomaton Bool？ Bool) :
    (solver C).project (solver C).border = false := by
  rfl

theorem solver_odd_fires_iff
    (C : CellAutomaton Bool？ Bool) (hC : SolvesFSSPOptimal C)
    (k : ℕ) (hk : k ≥ 1) (t : ℕ) (p : ℤ)
    (hp_nn : 0 ≤ p) (hp_lt : p < (2 * k + 1 : ℕ)) :
    (solver C).comp ⟬fssp_both_sides (2 * k + 1)⟭ t p = true ↔
      t ≥ 2 * k := by
  rw [solver_comp_fssp, routeAt_odd k hk t p]
  rw [reflected_comp_fssp (OddTwoSidedBetaBoundary.ca C) (2 * k + 1) t p]
  unfold oddRouteShape
  split_ifs with houtside hbefore hpR hpL hleft hcenter hright
  · exfalso
    push_cast at *
    omega
  · simp [selectTrack]
    omega
  · simp [selectTrack]
    omega
  · simp [selectTrack]
    omega
  · simpa [selectTrack] using
      (odd_two_sided_left_half_fires_iff C hC k hk t p hp_nn (by omega))
  · simpa [selectTrack] using
      (odd_two_sided_left_half_fires_iff C hC k hk t p hp_nn (by omega))
  · simpa [selectTrack] using
      (odd_two_sided_left_half_fires_iff C hC k hk t
        (((2 * k + 1 : ℕ) : ℤ) - 1 - p) (by
          push_cast at *
          omega) (by
          push_cast at *
          omega))
  · simp [selectTrack]
    push_cast at *
    omega

theorem solver_even_fires_iff
    (C : CellAutomaton Bool？ Bool) (hC : SolvesFSSPOptimal C)
    (k : ℕ) (hk : k ≥ 2) (t : ℕ) (p : ℤ)
    (hp_nn : 0 ≤ p) (hp_lt : p < (2 * k : ℕ)) :
    (solver C).comp ⟬fssp_both_sides (2 * k)⟭ t p = true ↔
      t ≥ 2 * k - 1 := by
  rw [solver_comp_fssp, routeAt_even k hk t p]
  rw [reflected_comp_fssp (EvenTwoSidedBetaBoundary.ca C) (2 * k) t p]
  unfold evenRouteShape
  split_ifs with houtside hbefore hpR hpL hleft hright
  · exfalso
    push_cast at *
    omega
  · simp [selectTrack]
    omega
  · simp [selectTrack]
    omega
  · simp [selectTrack]
    omega
  · simpa [selectTrack] using
      (even_two_sided_left_half_fires_iff C hC k hk t p hp_nn (by omega))
  · simpa [selectTrack] using
      (even_two_sided_left_half_fires_iff C hC k hk t
        (((2 * k : ℕ) : ℤ) - 1 - p) (by
          push_cast at *
          omega) (by
          push_cast at *
          omega))
  · simp [selectTrack]
    push_cast at *
    omega

theorem solver_one_fires_iff
    (C : CellAutomaton Bool？ Bool) (t : ℕ) (p : ℤ)
    (hp_nn : 0 ≤ p) (hp_lt : p < (1 : ℤ)) :
    (solver C).comp ⟬fssp_both_sides 1⟭ t p = true ↔ t ≥ 1 - 1 := by
  have hp_zero : p = 0 := by omega
  subst p
  rw [solver_comp_fssp, routeAt_one]
  simp [selectTrack]

theorem solver_two_fires_iff
    (C : CellAutomaton Bool？ Bool) (t : ℕ) (p : ℤ)
    (hp_nn : 0 ≤ p) (hp_lt : p < (2 : ℤ)) :
    (solver C).comp ⟬fssp_both_sides 2⟭ t p = true ↔ t ≥ 2 - 1 := by
  have hp : p = 0 ∨ p = 1 := by omega
  rcases hp with rfl | rfl
  · rcases t with _ | t
    · rw [solver_comp_fssp, routeAt_two_zero_left]
      simp [selectTrack]
    · rw [solver_comp_fssp, routeAt_two_succ_left]
      simp [selectTrack]
  · rcases t with _ | t
    · rw [solver_comp_fssp, routeAt_two_zero_right]
      simp [selectTrack]
    · rw [solver_comp_fssp, routeAt_two_succ_right]
      simp [selectTrack]

/-- A fixed one-sided optimal FSSP solver yields a fixed optimal two-sided
    solver. The router chooses parity and orientation locally. -/
theorem solver_solves_two_sided
    (C : CellAutomaton Bool？ Bool) (hC : SolvesFSSPOptimal C) :
    SolvesTwoSidedFSSPOptimal (solver C) where
  quiescent_border := solver_quiescent_border C hC
  border_projects_false := solver_border_projects_false C
  fire_iff := by
    intro n hn t p hp_nn hp_lt
    by_cases hn_one : n = 1
    · subst n
      exact solver_one_fires_iff C t p hp_nn hp_lt
    by_cases hn_two : n = 2
    · subst n
      exact solver_two_fires_iff C t p hp_nn hp_lt
    have hn_three : 3 ≤ n := by omega
    rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨k, hk_eq⟩ := heven
      have hn_eq : n = 2 * k := by omega
      have hk : k ≥ 2 := by omega
      rw [hn_eq] at hp_lt ⊢
      exact solver_even_fires_iff C hC k hk t p hp_nn hp_lt
    · obtain ⟨k, hk_eq⟩ := hodd
      have hn_eq : n = 2 * k + 1 := by omega
      have hk : k ≥ 1 := by omega
      rw [hn_eq] at hp_lt ⊢
      exact solver_odd_fires_iff C hC k hk t p hp_nn hp_lt

/-- The checked Mazoyer solver and the length-two handler running in
    parallel. Their disjunction solves every one-sided input in the domain. -/
def optimalOneSided : CellAutomaton Bool？ Bool :=
  (FsspMazoyerCA.C ⨂ SmallHandler.C).map_project
    (fun output => output.1 || output.2)

@[simp] theorem optimalOneSided_comp_fssp (n t : ℕ) (p : ℤ) :
    optimalOneSided.comp ⟬fssp_left_side n⟭ t p =
      (FsspMazoyerCA.C.comp ⟬fssp_left_side n⟭ t p ||
        SmallHandler.C.comp ⟬fssp_left_side n⟭ t p) := by
  simp [optimalOneSided]

theorem optimalOneSided_quiescent_set :
    optimalOneSided.quiescent_set
      {optimalOneSided.border, optimalOneSided.inner false} := by
  exact ca_zip_quiescent_border_inner FsspMazoyerCA.C SmallHandler.C false
    FsspMazoyer.quiescent_set_border_L
    SmallHandler.quiescent_set_border_soldier

private lemma mazoyer_n2_fire_implies_time (t : ℕ) (p : ℤ)
    (hp_nn : 0 ≤ p) (hp_lt : p < (2 : ℤ))
    (hfire : FsspMazoyerCA.C.comp ⟬fssp_left_side 2⟭ t p = true) :
    t ≥ 2 := by
  by_contra ht
  push_neg at ht
  have hp : p = 0 ∨ p = 1 := by omega
  have htime : t = 0 ∨ t = 1 := by omega
  rcases hp with rfl | rfl
  · rcases htime with rfl | rfl
    · have hnot :
          FsspMazoyerCA.C.comp ⟬fssp_left_side 2⟭ 0 0 ≠ true := by
        decide
      exact hnot hfire
    · have hnot :
          FsspMazoyerCA.C.comp ⟬fssp_left_side 2⟭ 1 0 ≠ true := by
        decide
      exact hnot hfire
  · rcases htime with rfl | rfl
    · have hnot :
          FsspMazoyerCA.C.comp ⟬fssp_left_side 2⟭ 0 1 ≠ true := by
        decide
      exact hnot hfire
    · have hnot :
          FsspMazoyerCA.C.comp ⟬fssp_left_side 2⟭ 1 1 ≠ true := by
        decide
      exact hnot hfire

/-- A concrete, checked optimal one-sided FSSP solver. -/
theorem optimalOneSided_solves : SolvesFSSPOptimal optimalOneSided where
  quiescent_set := optimalOneSided_quiescent_set
  fire_iff := by
    intro n hn
    dsimp
    intro t p hp
    have hp_n : p < (n : ℤ) := by simpa using hp.2
    rw [optimalOneSided_comp_fssp, Bool.or_eq_true]
    by_cases hn_two : n = 2
    · subst n
      rw [SmallHandler.n2_iff t p hp.1 hp_n]
      constructor
      · intro hfire
        rcases hfire with hfire | htime
        · exact mazoyer_n2_fire_implies_time t p hp.1 hp_n hfire
        · exact htime
      · exact Or.inr
    · have hn_three : 3 ≤ n := by omega
      rw [show SmallHandler.C.comp ⟬fssp_left_side n⟭ t p = false from
        SmallHandler.n_ge3_never_fires n hn_three t p hp.1 hp_n]
      simp only [Bool.false_eq_true, or_false]
      exact FsspMazoyer.FsspMazoyerCA_fire_iff n hn_three t p hp

/-- A fixed two-sided CA obtained from the checked one-sided solver. -/
def optimal : CellAutomaton (Bool × Bool)？ Bool :=
  solver optimalOneSided

/-- The concrete two-sided solver fires every interior cell exactly from time
    `n - 1` onward, for every nonempty input length. -/
theorem optimal_solves : SolvesTwoSidedFSSPOptimal optimal :=
  solver_solves_two_sided optimalOneSided optimalOneSided_solves

end TwoSidedFSSP

/-- A constructive witness for the optimal two-sided firing-squad problem. -/
theorem TwoSidedFSSP_exists :
    ∃ C : CellAutomaton (Bool × Bool)？ Bool, SolvesTwoSidedFSSPOptimal C :=
  ⟨TwoSidedFSSP.optimal, TwoSidedFSSP.optimal_solves⟩

end CellularAutomatas
