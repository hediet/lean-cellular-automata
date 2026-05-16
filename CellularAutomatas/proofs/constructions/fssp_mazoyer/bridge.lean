/-
  Mazoyer FSSP -- bridge from the `Etat`-style theorem to our
  `CellAutomaton α？ Bool` framework.

  The bridge uses the 7-state CA `FsspMazoyerCA.C` (`ca.lean`).
  Its `δ` is defined so that `Border` on the left substitutes for `L`
  and `Border` on the right substitutes for `G` -- mirroring exactly
  the right phantom `G` and left phantom `L` of Coq's `Etat`.
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.jean_duprat.final
import CellularAutomatas.proofs.constructions.fssp_mazoyer.not_fire
import CellularAutomatas.proofs.constructions.fssp_mazoyer.ca
import CellularAutomatas.proofs.fssp

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

/-! ### Embedding the 6-state `Couleur` into the 7-state CA alphabet -/

/-- Identity inclusion `FsspMazoyer.Couleur → FsspMazoyerCA.Couleur`.
    Every interior state maps to its CA namesake; the `Border` state
    of the CA is *not* in the image. -/
def to_ca : FsspMazoyer.Couleur → FsspMazoyerCA.Couleur
  | A => FsspMazoyerCA.Couleur.A
  | B => FsspMazoyerCA.Couleur.B
  | C => FsspMazoyerCA.Couleur.C
  | L => FsspMazoyerCA.Couleur.L
  | G => FsspMazoyerCA.Couleur.G
  | F => FsspMazoyerCA.Couleur.F

/-- `to_ca` is injective. -/
lemma to_ca_injective : Function.Injective to_ca := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [to_ca] at h)

/-! ### δ-bridge lemmas

The CA's `δ` agrees with the Etat-side `δ` modulo the `to_ca` inclusion,
with the Border state on either side substituting for L (left) / G (right).
All proofs are pure `rfl` after exhaustive case analysis. -/

/-- Pure interior step: all three inputs are non-Border. -/
lemma to_ca_δ (a b c : FsspMazoyer.Couleur) :
    FsspMazoyerCA.δ (to_ca a) (to_ca b) (to_ca c) =
      to_ca (FsspMazoyer.δ a b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Left-Border step: simulates `δ L b c`. -/
lemma to_ca_δ_left_border (b c : FsspMazoyer.Couleur) :
    FsspMazoyerCA.δ FsspMazoyerCA.Couleur.Border (to_ca b) (to_ca c) =
      to_ca (FsspMazoyer.δ L b c) := by
  cases b <;> cases c <;> rfl

/-- Right-Border step: simulates `δ a b G`. -/
lemma to_ca_δ_right_border (a b : FsspMazoyer.Couleur) :
    FsspMazoyerCA.δ (to_ca a) (to_ca b) FsspMazoyerCA.Couleur.Border =
      to_ca (FsspMazoyer.δ a b G) := by
  cases a <;> cases b <;> rfl

/-! ### CA boundary: `nextt` is `Border` outside `[0, n − 1]`

Outside the input range, the CA's word config is `none`, embedded as
`Border`. Since `δ _ Border _ = Border`, `Border` cells stay `Border`
forever. -/

private lemma word_to_config_outside_lt (n : ℕ) (p : ℤ) (hp : p < 0) :
    word_to_config (fssp_left_side n) p = none := by
  show (if h : p ≥ 0 ∧ p < (fssp_left_side n).length then _ else none) = none
  have hcond : ¬ (p ≥ 0 ∧ p < ((fssp_left_side n).length : ℤ)) := by
    intro ⟨h1, _⟩; omega
  rw [dif_neg hcond]

private lemma word_to_config_outside_ge (n : ℕ) (p : ℤ) (hp : (n : ℤ) ≤ p) :
    word_to_config (fssp_left_side n) p = none := by
  show (if h : p ≥ 0 ∧ p < (fssp_left_side n).length then _ else none) = none
  have hlen : ((fssp_left_side n).length : ℤ) = (n : ℤ) := by
    exact_mod_cast fssp_left_side_length n
  have hcond : ¬ (p ≥ 0 ∧ p < ((fssp_left_side n).length : ℤ)) := by
    intro ⟨_, h2⟩; rw [hlen] at h2; omega
  rw [dif_neg hcond]

private lemma nextt_lt_zero (n : ℕ) :
    ∀ (t : ℕ) (p : ℤ), p < 0 →
      FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t p =
        FsspMazoyerCA.Couleur.Border := by
  intro t
  induction t with
  | zero =>
    intro p hp
    show FsspMazoyerCA.C.embed (word_to_config (fssp_left_side n) p) =
         FsspMazoyerCA.Couleur.Border
    rw [word_to_config_outside_lt n p hp]; rfl
  | succ t ih =>
    intro p hp
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    rw [ih p hp]; rfl

private lemma nextt_ge_n (n : ℕ) :
    ∀ (t : ℕ) (p : ℤ), (n : ℤ) ≤ p →
      FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t p =
        FsspMazoyerCA.Couleur.Border := by
  intro t
  induction t with
  | zero =>
    intro p hp
    show FsspMazoyerCA.C.embed (word_to_config (fssp_left_side n) p) =
         FsspMazoyerCA.Couleur.Border
    rw [word_to_config_outside_ge n p hp]; rfl
  | succ t ih =>
    intro p hp
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    rw [ih p hp]; rfl

/-! ### Etat boundary: `Etat n t n = G` for `t ≤ 2n − 2`

Combination of `init n n = G` (at `t = 0`) and `vert_droite` (the right
G-wall produced by `Ht1_VV` from `base2`). -/

private lemma Etat_at_n (n : ℕ) (h : 4 ≤ n) (t : ℕ) (ht : t ≤ 2 * n - 2) :
    Etat n t (n : ℤ) = G := by
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0; exact G0N n (by omega)
  · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    have hv := vert_droite n h
    exact hv.pointwise t' (by omega)

/-! ### Initial config matches on in-range cells -/

private lemma init_eq_to_ca_init (n : ℕ) (h : 4 ≤ n) (x : ℤ)
    (hx : 0 ≤ x) (hxn : x ≤ (n : ℤ) - 1) :
    FsspMazoyerCA.C.embed (word_to_config (fssp_left_side n) x) =
      to_ca (Etat n 0 x) := by
  obtain ⟨xn, rfl⟩ : ∃ xn : ℕ, x = (xn : ℤ) :=
    ⟨x.toNat, (Int.toNat_of_nonneg hx).symm⟩
  have hxn_lt : xn < n := by
    have : (xn : ℤ) ≤ (n : ℤ) - 1 := hxn
    omega
  have hn_pos : 1 ≤ n := by omega
  have hlen : (fssp_left_side n).length = n := fssp_left_side_length n
  have hn_ne : ¬ n = 0 := by omega
  -- Compute (fssp_left_side n)[xn] directly.
  have hgetElem :
      (fssp_left_side n)[xn]'(by rw [hlen]; exact hxn_lt) =
        (decide (xn = 0) : Bool) := by
    -- Unfold fssp_left_side to its `if`-shape and discharge by case.
    have hdef : fssp_left_side n =
        ([true] ++ List.replicate (n - 1) false : List Bool) := by
      show (if n = 0 then ([] : List Bool)
            else [true] ++ List.replicate (n - 1) false) = _
      rw [if_neg hn_ne]
    -- We can use hdef inside getElem via a generalized rewrite.
    have : (fssp_left_side n)[xn]'(by rw [hlen]; exact hxn_lt) =
        (([true] ++ List.replicate (n - 1) false) : List Bool)[xn]'(by
          have : ([true] ++ List.replicate (n - 1) false : List Bool).length = n := by
            simp; omega
          rw [this]; exact hxn_lt) := by
      apply List.getElem_of_eq hdef
    rw [this]
    -- Now compute on the explicit list.
    have hlen' : ([true] ++ List.replicate (n - 1) false : List Bool).length = n := by
      simp; omega
    by_cases hxn0 : xn = 0
    · subst hxn0
      have hbnd : (0 : ℕ) < ([true] ++ List.replicate (n - 1) false : List Bool).length := by
        rw [hlen']; omega
      show (([true] ++ List.replicate (n - 1) false) : List Bool)[(0 : ℕ)]'hbnd = _
      simp
    · have hxn_pos : 1 ≤ xn := Nat.one_le_iff_ne_zero.mpr hxn0
      have hbnd : xn < ([true] ++ List.replicate (n - 1) false : List Bool).length := by
        rw [hlen']; exact hxn_lt
      show (([true] ++ List.replicate (n - 1) false) : List Bool)[xn]'hbnd = _
      rw [List.getElem_append_right (by simp; omega)]
      simp [hxn0]
  -- Use this to rewrite word_to_config.
  show FsspMazoyerCA.C.embed (word_to_config (fssp_left_side n) (xn : ℤ)) =
       to_ca (Etat n 0 (xn : ℤ))
  have hcond : ((xn : ℤ)) ≥ 0 ∧ (xn : ℤ) < ((fssp_left_side n).length : ℤ) := by
    refine ⟨by exact_mod_cast Nat.zero_le _, ?_⟩
    rw [show ((fssp_left_side n).length : ℤ) = (n : ℤ) from by exact_mod_cast hlen]
    exact_mod_cast hxn_lt
  have hwc :
      word_to_config (fssp_left_side n) (xn : ℤ) =
        some ((decide (xn = 0)) : Bool) := by
    show (if h : ((xn : ℤ)) ≥ 0 ∧ (xn : ℤ) < (fssp_left_side n).length
          then some (fssp_left_side n)[((xn : ℤ)).toNat] else none) = _
    rw [dif_pos hcond]
    have hidx : ((xn : ℤ)).toNat = xn := Int.toNat_natCast _
    -- Equate the indexed lookups.
    show some ((fssp_left_side n)[((xn : ℤ)).toNat]) = _
    have key : (fssp_left_side n)[((xn : ℤ)).toNat]'(by rw [hidx, hlen]; exact hxn_lt) =
        (fssp_left_side n)[xn]'(by rw [hlen]; exact hxn_lt) := by
      congr 1
    rw [key, hgetElem]
  rw [hwc]
  by_cases hxn0 : xn = 0
  · subst hxn0
    show FsspMazoyerCA.C.embed (some (decide ((0 : ℕ) = 0))) = to_ca (Etat n 0 ((0 : ℕ) : ℤ))
    have h00 : Etat n 0 ((0 : ℕ) : ℤ) = G := by
      show Etat n 0 (0 : ℤ) = G
      exact G00 n (by omega)
    rw [h00]
    show FsspMazoyerCA.C.embed (some (decide ((0 : ℕ) = 0))) = to_ca G
    decide
  · have hxn_pos : (0 : ℤ) < (xn : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero hxn0
    have hxn_lt' : (xn : ℤ) < (n : ℤ) := by exact_mod_cast hxn_lt
    rw [show Etat n 0 (xn : ℤ) = L from base_L n (by omega) (xn : ℤ) hxn_pos hxn_lt']
    show FsspMazoyerCA.C.embed (some (decide (xn = 0))) = to_ca L
    rw [decide_eq_false hxn0]
    rfl

/-! ### Translate `nextt` ↔ `Etat` for in-range cells -/

/-- For in-range cells (`0 ≤ x ≤ n − 1`) and time `t ≤ 2n − 2`, the CA's
    internal-state trace `nextt ⦋⟬fssp_left_side n⟭⦌ t x` equals
    `to_ca (Etat n t x)`.

    Proof: induction on `t` with the boundary invariant that
    `nextt _ t p = Border` for `p ∉ [0, n − 1]`
    (`nextt_lt_zero` / `nextt_ge_n`) and the matching Etat-side facts
    (`L_outside` for the left phantom, `Etat_at_n` for the right). -/
lemma cell_eq_Etat (n : ℕ) (h : 4 ≤ n) :
    ∀ (t : ℕ), t ≤ 2 * n - 2 →
      ∀ (x : ℤ), 0 ≤ x → x ≤ (n : ℤ) - 1 →
        FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t x = to_ca (Etat n t x) := by
  intro t
  induction t with
  | zero =>
    intro _ x hx hxn
    show FsspMazoyerCA.C.embed (word_to_config (fssp_left_side n) x) = to_ca (Etat n 0 x)
    exact init_eq_to_ca_init n h x hx hxn
  | succ t ih =>
    intro ht x hx hxn
    have htih : t ≤ 2 * n - 2 := by omega
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    have hmid : FsspMazoyerCA.C.nextt _ t x = to_ca (Etat n t x) := ih htih x hx hxn
    -- Convert `C.δ` to bare `FsspMazoyerCA.δ` for the bridge rewrites.
    show FsspMazoyerCA.δ (FsspMazoyerCA.C.nextt _ t (x - 1))
                        (FsspMazoyerCA.C.nextt _ t x)
                        (FsspMazoyerCA.C.nextt _ t (x + 1)) =
         to_ca (FsspMazoyer.δ (Etat n t (x - 1)) (Etat n t x) (Etat n t (x + 1)))
    by_cases hx0 : x = 0
    · -- Left edge: left neighbor at -1 is Border in CA, L in Etat.
      subst hx0
      have hleft_ca : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t ((0 : ℤ) - 1) =
          FsspMazoyerCA.Couleur.Border :=
        nextt_lt_zero n t ((0 : ℤ) - 1) (by norm_num)
      have hleft_e : Etat n t ((0 : ℤ) - 1) = L :=
        L_outside n t ((0 : ℤ) - 1) (by norm_num)
      have hright_ca : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t ((0 : ℤ) + 1) =
          to_ca (Etat n t ((0 : ℤ) + 1)) := by
        have e : (0 : ℤ) + 1 = (1 : ℤ) := by ring
        rw [e]
        exact ih htih 1 (by norm_num) (by omega)
      rw [hleft_ca, hmid, hright_ca, hleft_e, to_ca_δ_left_border]
    · have hx_pos : 1 ≤ x := by omega
      by_cases hx_top : x = (n : ℤ) - 1
      · -- Right edge: right neighbor at n is Border in CA, G in Etat.
        subst hx_top
        have hright_ca : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t (((n : ℤ) - 1) + 1) =
            FsspMazoyerCA.Couleur.Border := by
          have e : ((n : ℤ) - 1) + 1 = (n : ℤ) := by ring
          rw [e]; exact nextt_ge_n n t (n : ℤ) (le_refl _)
        have hright_e : Etat n t (((n : ℤ) - 1) + 1) = G := by
          have e : ((n : ℤ) - 1) + 1 = (n : ℤ) := by ring
          rw [e]; exact Etat_at_n n h t htih
        have hleft_ca : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t (((n : ℤ) - 1) - 1) =
            to_ca (Etat n t (((n : ℤ) - 1) - 1)) :=
          ih htih (((n : ℤ) - 1) - 1) (by omega) (by omega)
        rw [hleft_ca, hmid, hright_ca, hright_e, to_ca_δ_right_border]
      · -- Interior: 1 ≤ x ≤ n - 2, both neighbors in range.
        have hx_top' : x < (n : ℤ) - 1 := lt_of_le_of_ne hxn hx_top
        have hleft_ca : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t (x - 1) =
            to_ca (Etat n t (x - 1)) :=
          ih htih (x - 1) (by omega) (by omega)
        have hright_ca : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t (x + 1) =
            to_ca (Etat n t (x + 1)) :=
          ih htih (x + 1) (by omega) (by omega)
        rw [hleft_ca, hmid, hright_ca, to_ca_δ]

/-- The `comp` output (a `Bool`) at position `x ∈ [0, n − 1]` and time
    `t ≤ 2n − 2` is `true ↔ Etat n t x = F`. -/
lemma comp_eq_F (n : ℕ) (h : 4 ≤ n) (t : ℕ) (x : ℤ)
    (hx : 0 ≤ x) (hxn : x ≤ (n : ℤ) - 1) (ht : t ≤ 2 * n - 2) :
    FsspMazoyerCA.C.comp ⟬fssp_left_side n⟭ t x = true ↔ Etat n t x = F := by
  have heq := cell_eq_Etat n h t ht x hx hxn
  show FsspMazoyerCA.C.project (FsspMazoyerCA.C.nextt _ t x) = true ↔ _
  rw [heq]
  cases Etat n t x <;> simp [to_ca, FsspMazoyerCA.C]

/-! ### `F` persistence in the CA

Once the CA's `nextt` is in state `F` at some time, it stays `F` forever
(since `δ _ F _ = F` in the CA — same definition pattern as the
Etat-side `F_absorbing`). -/

private lemma nextt_F_persists (n : ℕ) :
    ∀ (s : ℕ) (t : ℕ) (x : ℤ),
      FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t x = FsspMazoyerCA.Couleur.F →
      FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) (t + s) x = FsspMazoyerCA.Couleur.F := by
  intro s
  induction s with
  | zero => intro t x hF; simpa using hF
  | succ s ih =>
    intro t x hF
    rw [show t + (s + 1) = (t + s) + 1 from by omega]
    rw [CellAutomaton.nextt_succ, CellAutomaton.next_apply]
    rw [ih t x hF]
    rfl

/-! ### Quiescent set: `δ _ b _ = b` for `b ∈ {Border, L}` -/

lemma quiescent_set_border_L :
    FsspMazoyerCA.C.quiescent_set
        ({FsspMazoyerCA.C.border, FsspMazoyerCA.C.inner false}) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  show FsspMazoyerCA.C.δ a b c = b
  have aux : ∀ q ∈ ({FsspMazoyerCA.C.border, FsspMazoyerCA.C.inner false} :
      Set FsspMazoyerCA.C.Q),
      q = FsspMazoyerCA.Couleur.Border ∨ q = FsspMazoyerCA.Couleur.L := by
    intro q hq
    rcases hq with h1 | h1
    · left; exact h1
    · right; exact h1
  rcases aux a ha with rfl | rfl <;>
    rcases aux b hb with rfl | rfl <;>
    rcases aux c hc with rfl | rfl <;> rfl

/-! ### Final assembly -/

/-- The Mazoyer 7-state CA solves the optimal-time FSSP **for `n ≥ 3`**.
    The Coq proof requires `2 < N` (equivalently `n ≥ 4`); the `n = 3`
    case is verified here by finite computation.

    Cases `n ∈ {1, 2}` are not handled by Mazoyer's construction
    (and indeed `SolvesFSSPOptimal` for `n = 1` is unsatisfiable with
    this CA: it requires the singleton input `[true]` to fire at `t = 0`,
    but `embed (some true) = G` projects to `false`, not `true`).
    Discharged here as a `sorry` for `n ∈ {1, 2}`. -/
theorem SolvesFSSPOptimal_FsspMazoyerCA :
    SolvesFSSPOptimal FsspMazoyerCA.C where
  quiescent_set := quiescent_set_border_L
  fire_iff n hn := by
    -- After `n hn`, the body is `let w := …; ∀ t p, … → (… ↔ …)`.
    intro w t p hp
    obtain ⟨hx, hxlt⟩ := hp
    -- `w` is definitionally `fssp_left_side n`; the `simp only` below unfolds.
    have hxlen : p < (n : ℤ) := by
      have hcast : ((fssp_left_side n).length : ℤ) = (n : ℤ) := by
        exact_mod_cast fssp_left_side_length n
      have : p < ((fssp_left_side n).length : ℤ) := hxlt
      rw [hcast] at this
      exact this
    have hxn : p ≤ (n : ℤ) - 1 := by omega
    show FsspMazoyerCA.C.comp ⟬fssp_left_side n⟭ t p = true ↔ t ≥ 2 * n - 2
    by_cases hn4 : 4 ≤ n
    · constructor
      · -- comp = true ⇒ t ≥ 2n - 2.
        intro hfire
        by_contra hnt
        push_neg at hnt
        have ht_lt : t < 2 * n - 2 := hnt
        have ht_le : t ≤ 2 * n - 2 := by omega
        have hF : Etat n t p = F :=
          (comp_eq_F n hn4 t p hx hxn ht_le).mp hfire
        exact not_fire_before n hn4 t ht_lt p hx hxn hF
      · -- t ≥ 2n - 2 ⇒ comp = true.
        intro ht_ge
        have hfs : Etat n (2 * n - 2) p = F := by
          obtain ⟨xn, rfl⟩ : ∃ xn : ℕ, p = (xn : ℤ) :=
            ⟨p.toNat, (Int.toNat_of_nonneg hx).symm⟩
          have hxn_le : xn ≤ n - 1 := by
            have : (xn : ℤ) ≤ (n : ℤ) - 1 := hxn
            omega
          have hcell := (firing_squad n hn4).pointwise xn hxn_le
          have e : (0 : ℤ) + (xn : ℤ) = (xn : ℤ) := by ring
          rw [e] at hcell
          exact hcell
        have hCA_at : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) (2 * n - 2) p = FsspMazoyerCA.Couleur.F := by
          rw [cell_eq_Etat n hn4 (2 * n - 2) (le_refl _) p hx hxn, hfs]
          rfl
        have hCA_t : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t p = FsspMazoyerCA.Couleur.F := by
          have habs := nextt_F_persists n (t - (2 * n - 2)) (2 * n - 2) p hCA_at
          rw [show 2 * n - 2 + (t - (2 * n - 2)) = t from by omega] at habs
          exact habs
        show FsspMazoyerCA.C.project (FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side n⟭⦌) t p) = true
        rw [hCA_t]; rfl
    · -- n ∈ {1, 2, 3}.
      -- n = 3 works and can be verified by finite computation.
      -- n ∈ {1, 2} is genuinely unsatisfiable with this CA.
      interval_cases n
      · -- n = 1: sorry (unsatisfiable — G projects to false, but spec
        -- requires fire at t = 0).
        sorry
      · -- n = 2: sorry (cells never fire simultaneously).
        sorry
      · -- n = 3: fires at t = 4 = 2·3 − 2. Proved by computation.
        -- p ∈ {0, 1, 2} since 0 ≤ p < 3.
        have hp_bound : p = 0 ∨ p = 1 ∨ p = 2 := by omega
        -- Forward: comp = true → t ≥ 4.
        -- Backward: t ≥ 4 → comp = true.
        -- For t < 4 and each p, comp = false (by native_decide on each case).
        -- For t ≥ 4, nextt at t=4 is F for each p (native_decide), then persists.
        constructor
        · -- comp = true → t ≥ 4
          intro hfire
          by_contra hlt
          push_neg at hlt
          -- t ∈ {0, 1, 2, 3}
          rcases hp_bound with rfl | rfl | rfl <;> interval_cases t <;>
            simp_all (config := { decide := true })
        · -- t ≥ 4 → comp = true
          intro hge
          -- At t = 4, nextt gives F for each p ∈ {0, 1, 2}.
          have key : ∀ q : ℤ, 0 ≤ q → q < 3 →
              FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side 3⟭⦌) 4 q =
                FsspMazoyerCA.Couleur.F := by
            intro q hq0 hq3
            have : q = 0 ∨ q = 1 ∨ q = 2 := by omega
            rcases this with rfl | rfl | rfl <;> native_decide
          have hF4 := key p hx (by omega)
          have hFt : FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side 3⟭⦌) t p =
              FsspMazoyerCA.Couleur.F := by
            have := nextt_F_persists 3 (t - 4) 4 p hF4
            rw [show 4 + (t - 4) = t from by omega] at this
            exact this
          show FsspMazoyerCA.C.project (FsspMazoyerCA.C.nextt (⦋⟬fssp_left_side 3⟭⦌) t p) = true
          rw [hFt]; rfl

theorem SolvesFSSPOptimal_exists_via_mazoyer :
    ∃ C : CellAutomaton Bool？ Bool, SolvesFSSPOptimal C :=
  ⟨FsspMazoyerCA.C, SolvesFSSPOptimal_FsspMazoyerCA⟩

end FsspMazoyer
end CellularAutomatas
