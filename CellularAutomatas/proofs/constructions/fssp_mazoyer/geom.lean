/-
  Mazoyer FSSP -- geometric figure predicates and the abstract
  "Local_Prop" infrastructure (ports `bib.v` `Local_Prop`, `loi`,
  `loi_droite` plus arithmetic helpers, and `geom.v` figures and
  induction principles).
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer

namespace CellularAutomatas
namespace FsspMazoyer

open Couleur

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ### `bib.v` analogues -/

/-- Coq's `Local_Prop := nat → nat → Prop`. We use `ℤ` for the
    spatial coordinate so it composes with our `Etat : ℕ → ℤ → Couleur`. -/
abbrev Local_Prop := ℕ → ℤ → Prop

/-- `loi P Q R T` says that the local rule, applied to three cells
    satisfying `P, Q, R` at time `t`, produces a cell satisfying `T`
    at time `t + 1`. -/
def loi (P Q R T : Local_Prop) : Prop :=
  ∀ (t : ℕ) (x : ℤ), P t x → Q t (x + 1) → R t (x + 2) → T (t + 1) (x + 1)

/-- `loi_droite Q R T` is the *boundary* version: only two cells
    determine the next state (used at the leftmost cell since there
    is a phantom `L` to its left in Mazoyer's `Etat`). -/
def loi_droite (Q R T : Local_Prop) : Prop :=
  ∀ (t : ℕ) (x : ℤ), Q t x → R t (x + 1) → T (t + 1) x

/-! #### Coq's `un, deux, …` constants -/

abbrev un    : ℕ := 1
abbrev deux  : ℕ := 2
abbrev trois : ℕ := 3
abbrev quatre : ℕ := 4
abbrev cinq  : ℕ := 5
abbrev six   : ℕ := 6
abbrev sept  : ℕ := 7
abbrev huit  : ℕ := 8
abbrev neuf  : ℕ := 9

/-! #### Doubling/tripling/halving -/

def double (n : ℕ) : ℕ := n + n
def triple (n : ℕ) : ℕ := n + n + n
def tiers (n : ℕ) : ℕ := n / 3

def Omod3   (n : ℕ) : Prop := n % 3 = 0
def Unmod3  (n : ℕ) : Prop := n % 3 = 1
def Deuxmod3 (n : ℕ) : Prop := n % 3 = 2

/-! Arithmetic facts about `tiers`/`double`/`triple` and the modular
    classes (`bib.v`). -/

lemma double_S (n : ℕ) : double (n + 1) = double n + 2 := by
  unfold double; omega

lemma triple_S (n : ℕ) : triple (n + 1) = triple n + 3 := by
  unfold triple; omega

lemma le_double (n m : ℕ) : double n ≤ double m → n ≤ m := by
  unfold double; omega

lemma le_S_double (n m : ℕ) : double n ≤ double m + 1 → n ≤ m := by
  unfold double; omega

lemma le_triple (n m : ℕ) : triple n ≤ triple m → n ≤ m := by
  unfold triple; omega

lemma lt_triple (n m : ℕ) : triple n < triple m → n < m := by
  unfold triple; omega

lemma le_double_triple (n : ℕ) : double n ≤ triple n := by
  unfold double triple; omega

lemma le_troistiers_un (n : ℕ) : triple (tiers n) ≤ n := by
  unfold triple tiers; omega

lemma le_deuxtiers_un (a : ℕ) : double (tiers a) ≤ a := by
  unfold double tiers; omega

lemma lt_tiersn_n (n : ℕ) : 0 < n → tiers n < n := by
  unfold tiers; omega

lemma lt_deuxtiersn_n (n : ℕ) : 0 < n → double (tiers n) < n := by
  unfold double tiers; omega

lemma lt_Sdeuxtiersn_n (n : ℕ) : 3 < n → double (tiers n) + 1 < n := by
  unfold double tiers; omega

lemma lt_O_tiers (n : ℕ) : 2 < n → 0 < tiers n := by
  unfold tiers; omega

lemma lt_O_deuxtiers (n : ℕ) : 3 ≤ n → 0 < double (tiers n) := by
  unfold double tiers; omega

lemma le_tiers_trois (n : ℕ) : 3 ≤ n → 1 ≤ tiers n := by
  unfold tiers; omega

lemma le_tiers_six (n : ℕ) : 6 ≤ n → 2 ≤ tiers n := by
  unfold tiers; omega

lemma triple_tiers (n : ℕ) (h : Omod3 n) : tiers n + tiers n + tiers n = n := by
  unfold tiers Omod3 at *; omega

lemma Striple_tiers (n : ℕ) (h : Unmod3 n) : (tiers n + tiers n + tiers n) + 1 = n := by
  unfold tiers Unmod3 at *; omega

lemma SStriple_tiers (n : ℕ) (h : Deuxmod3 n) : (tiers n + tiers n + tiers n) + 2 = n := by
  unfold tiers Deuxmod3 at *; omega

lemma plus_deuxtiers_untiers (n : ℕ) (h : Omod3 n) : double (tiers n) + tiers n = n := by
  unfold double tiers Omod3 at *; omega

lemma Splus_deuxtiers_untiers (n : ℕ) (h : Unmod3 n) :
    (double (tiers n) + tiers n) + 1 = n := by
  unfold double tiers Unmod3 at *; omega

lemma SSplus_deuxtiers_untiers (n : ℕ) (h : Deuxmod3 n) :
    (double (tiers n) + tiers n) + 2 = n := by
  unfold double tiers Deuxmod3 at *; omega

lemma Omod3_Unmod3 (n : ℕ) : Omod3 n → Unmod3 (n + 1) := by
  unfold Omod3 Unmod3; omega

lemma Unmod3_Deuxmod3 (n : ℕ) : Unmod3 n → Deuxmod3 (n + 1) := by
  unfold Unmod3 Deuxmod3; omega

lemma Deuxmod3_Omod3 (n : ℕ) : Deuxmod3 n → Omod3 (n + 1) := by
  unfold Deuxmod3 Omod3; omega

lemma tiers_S (n : ℕ) (h : Omod3 n) : tiers n = tiers (n + 1) := by
  unfold tiers Omod3 at *; omega

lemma tiers_SS (n : ℕ) (h : Unmod3 n) : tiers n = tiers (n + 1) := by
  unfold tiers Unmod3 at *; omega

lemma tiers_SSS (n : ℕ) (h : Deuxmod3 n) : tiers n + 1 = tiers (n + 1) := by
  unfold tiers Deuxmod3 at *; omega

/-! #### `Rec*` modus-ponens chains. -/

lemma Rec2 (A B C : Prop) : (A → B → C) → A → (A → B) → C := by
  intro h a hab; exact h a (hab a)

lemma Rec3 (A B C D : Prop) : (A → B → C → D) → A → B → (B → C) → D := by
  intro h a b hbc; exact h a b (hbc b)

lemma Rec3' (A B C D : Prop) : (A → B → C → D) → A → (A → B) → (A → B → C) → D := by
  intro h a hab habc; exact h a (hab a) (habc a (hab a))

lemma Rec4 (A B C D E : Prop) : (A → B → C → D → E) → A → B → (B → C) → (C → D) → E := by
  intro h a b hbc hcd; exact h a b (hbc b) (hcd (hbc b))

lemma Rec4' (A B C D E : Prop) : (A → B → C → D → E) → A → B → C → (B → C → D) → E := by
  intro h a b c hbcd; exact h a b c (hbcd b c)

lemma Rec4'' (A B C D E : Prop) :
    (A → B → C → D → E) → A → (A → B) → (B → C) → (C → D) → E := by
  intro h a hab hbc hcd
  exact h a (hab a) (hbc (hab a)) (hcd (hbc (hab a)))

lemma Rec5 (A B C D E F : Prop) :
    (A → B → C → D → E → F) → A → B → (B → C) → (C → D) → (D → E) → F := by
  intro h a b hbc hcd hde
  exact h a b (hbc b) (hcd (hbc b)) (hde (hcd (hbc b)))

lemma Rec5' (A B C D E F : Prop) :
    (A → B → C → D → E → F) → A → B → (A → C) → (B → C → D) → (C → D → E) → F := by
  intro h a b hac hbcd hcde
  have c := hac a
  have d := hbcd b c
  exact h a b c d (hcde c d)

lemma recur_nSn (P : ℕ → Prop) (n : ℕ) :
    P n → P (n + 1) → (∀ p : ℕ, P p → P (p + 1) → P (p + 2)) →
    ∀ p : ℕ, n ≤ p → P p := by
  intro hn hSn step p hp
  -- Strengthen to `P p ∧ P (p + 1)` so the induction step has both predecessors.
  suffices h : P p ∧ P (p + 1) from h.1
  induction p, hp using Nat.le_induction with
  | base => exact ⟨hn, hSn⟩
  | succ k _ ih => exact ⟨ih.2, step k ih.1 ih.2⟩

lemma recur2 (P : ℕ → Prop) :
    (∀ n : ℕ, (∀ p : ℕ, p < n → P p) → P n) → ∀ m : ℕ, P m := by
  intro h m
  -- Prove the stronger `∀ k p, p < k → P p` by induction on k, then use k = m+1.
  suffices key : ∀ k p, p < k → P p from key (m + 1) m (Nat.lt_succ_self m)
  intro k
  induction k with
  | zero => intro p hp; omega
  | succ n ih =>
    intro p hp
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hp) with h' | h'
    · exact ih p h'
    · subst h'; exact h p ih

/-! ### Geometric figure predicates (port of `geom.v`) -/

/-- `Horizontale t x long P` -- a horizontal segment of `long + 1`
    cells at time `t`, all satisfying `P`. -/
structure Horizontale (t : ℕ) (x : ℤ) (long : ℕ) (P : Local_Prop) : Prop where
  pointwise : ∀ dx : ℕ, dx ≤ long → P t (x + dx)

/-- `Horizontale_t0 t x long P0 P` -- distinguished leftmost cell. -/
structure Horizontale_t0 (t : ℕ) (x : ℤ) (long : ℕ) (P0 P : Local_Prop) : Prop where
  head : P0 t x
  tail : Horizontale t (x + 1) long P

/-- `Horizontale_t1 t x long P0 P1 P` -- two distinguished leftmost
    cells (used for the `G : C : L^*` recursion-input rows). -/
structure Horizontale_t1 (t : ℕ) (x : ℤ) (long : ℕ) (P0 P1 P : Local_Prop) : Prop where
  head  : P0 t x
  next1 : P1 t (x + 1)
  tail  : Horizontale t (x + 2) long P

/-- `Verticale t x haut P` -- a vertical segment of `haut + 1` cells
    at column `x`, starting at time `t`. -/
structure Verticale (t : ℕ) (x : ℤ) (haut : ℕ) (P : Local_Prop) : Prop where
  pointwise : ∀ dt : ℕ, dt ≤ haut → P (t + dt) x

/-- `Triangle_inf t x cote P` -- the lower-right triangle of side `cote`. -/
structure Triangle_inf (t : ℕ) (x : ℤ) (cote : ℕ) (P : Local_Prop) : Prop where
  pointwise : ∀ dt dx : ℕ, dx ≤ cote → dt ≤ dx → P (t + dt) (x + dx)

/-- `Diag t x cote P Q R` -- a right-isoceles triangle of side `cote`
    with the apex `(t, x + cote)` satisfying `P`, the bottom-left
    vertex `(t + cote, x)` satisfying `R`, and every strictly-interior
    cell satisfying `Q`. Requires `1 < cote`. -/
structure Diag (t : ℕ) (x : ℤ) (cote : ℕ) (P Q R : Local_Prop) : Prop where
  size_pos    : 1 < cote
  apex        : P t (x + cote)
  interior    : ∀ dt dx : ℕ,
                  0 < dt → 0 < dx → dt + dx = cote → Q (t + dt) (x + dx)
  bottomLeft  : R (t + cote) x

/-- `Diag' t x cote P Q' Q R` -- like `Diag` but with the row at
    time `t + 1` carrying a different predicate `Q'`. Requires
    `2 < cote`. -/
structure Diag' (t : ℕ) (x : ℤ) (cote : ℕ) (P Q' Q R : Local_Prop) : Prop where
  size_pos    : 2 < cote
  apex        : P t (x + cote)
  topRow      : ∀ dx : ℕ, dx + 1 = cote → Q' (t + 1) (x + dx)
  interior    : ∀ dt dx : ℕ,
                  1 < dt → 0 < dx → dt + dx = cote → Q (t + dt) (x + dx)
  bottomLeft  : R (t + cote) x

/-- `Semi_Diag t x cote P Q` -- triangle with `P` at apex and `Q`
    everywhere strictly inside / on the slanted edge. -/
structure Semi_Diag (t : ℕ) (x : ℤ) (cote : ℕ) (P Q : Local_Prop) : Prop where
  size_pos : 0 < cote
  apex     : P t (x + cote)
  interior : ∀ dt dx : ℕ, 0 < dt → dt + dx = cote → Q (t + dt) (x + dx)

/-! ### Induction principles -/

/-- 2D induction filler from `geom.v` -- analogue of `inter`. -/
lemma inter (a b long : ℕ) (T : ℕ → ℕ → Prop) :
    (∀ dx : ℕ, b < dx → (a + 1) + dx = long → T (a + 1) dx) →
    (∀ dt dx : ℕ, a < dt → b < dx → (dt + 1) + (dx + 1) = long →
       T dt (dx + 2) → T (dt + 1) (dx + 1)) →
    (∀ dt : ℕ, a < dt → (dt + 1) + (b + 1) = long →
       T dt (b + 2) → T (dt + 1) (b + 1)) →
    ∀ dt dx : ℕ, a < dt → b < dx → dt + dx = long → T dt dx := by
  intro H1 H2 H3 dt dx hdt hdx hsum
  -- `a < dt` is definitionally `a + 1 ≤ dt`, drive `Nat.le_induction` on that.
  induction dt, hdt using Nat.le_induction generalizing dx with
  | base =>
    -- Base case: dt = a + 1; conclusion follows directly from H1.
    exact H1 dx hdx hsum
  | succ k hk ih =>
    -- Step: dt = k + 1 with a + 1 ≤ k. Peel off the rightmost column.
    obtain ⟨dx', rfl⟩ : ∃ m, dx = m + 1 := ⟨dx - 1, by omega⟩
    rcases (Nat.lt_or_eq_of_le (show b ≤ dx' by omega)) with hbdx | hbdx
    · -- b < dx': interior step uses H2.
      have htk := ih (dx' + 2) (by omega) (by omega)
      exact H2 k dx' (by omega) hbdx (by omega) htk
    · -- dx' = b: leftmost-interior column uses H3.
      subst hbdx
      have htk := ih (b + 2) (by omega) (by omega)
      exact H3 k (by omega) (by omega) htk

/-! Local helpers for normalizing `Nat.cast` distribution in the index
    arguments. The `inter` lambda elaborates to `Q (t + a) (x + ↑b)`, but
    the user-facing rules are written with `x + (↑dx + n)`. The helpers
    below let us bridge the two forms with `push_cast` followed by an
    `exact`. -/

/-- Constructor for `Diag` from boundary updates. `geom.v` `Rec_Diag`. -/
lemma Rec_Diag (t : ℕ) (x : ℤ) (cote : ℕ) (P Q R : Local_Prop) :
    1 < cote →
    P t (x + cote) →
    (∀ dx : ℕ, dx + 2 = cote → P t (x + cote) → Q (t + 1) (x + (dx + 1))) →
    (∀ dt dx : ℕ, 0 < dt → 0 < dx → (dt + 1) + (dx + 1) = cote →
       Q (t + dt) (x + (dx + 2)) → Q (t + dt + 1) (x + (dx + 1))) →
    (∀ dt : ℕ, dt + 2 = cote → Q (t + dt) (x + 2) → Q (t + dt + 1) (x + 1)) →
    (∀ dt : ℕ, dt + 1 = cote → Q (t + dt) (x + 1) → R (t + cote) x) →
    Diag t x cote P Q R := by
  intro hc hP top gen leftCol bottom
  -- Build the interior via `inter` with a = b = 0 (so dt > 0, dx > 0).
  have interior : ∀ dt dx : ℕ, 0 < dt → 0 < dx → dt + dx = cote →
                    Q (t + dt) (x + dx) := by
    apply inter 0 0 cote (fun a b => Q (t + a) (x + b))
    · -- top row: dx > 0, 1 + dx = cote → Q (t + 1) (x + ↑dx)
      intro dx hdx hsum
      obtain ⟨dx', rfl⟩ : ∃ k, dx = k + 1 := ⟨dx - 1, by omega⟩
      have h := top dx' (by omega) hP
      -- h : Q (t + 1) (x + (↑dx' + 1)); goal : Q (t + (0+1)) (x + ↑(dx'+1))
      push_cast
      exact h
    · -- generic interior step
      intro dt dx hdt hdx hsum hPrev
      -- hPrev : Q (t + dt) (x + ↑(dx + 2))
      push_cast at hPrev
      have h := gen dt dx hdt hdx (by omega) hPrev
      push_cast
      exact h
    · -- left-column step: b = 0, so the index `(b + 2) = 2` and `(b + 1) = 1`
      -- are numeric and the casts collapse definitionally.
      intro dt _ hsum hPrev
      exact leftCol dt (by omega) hPrev
  refine ⟨hc, hP, interior, ?_⟩
  -- bottom-left: feed Q at (t + (cote - 1), x + 1) into the `bottom` rule.
  have q := interior (cote - 1) 1 (by omega) (by omega) (by omega)
  -- q : Q (t + (cote - 1)) (x + ↑1) = Q (t + (cote - 1)) (x + 1)
  exact bottom (cote - 1) (by omega) q

/-- Constructor for `Diag'`. `geom.v` `Rec_Diag'`. -/
lemma Rec_Diag' (t : ℕ) (x : ℤ) (cote : ℕ) (P Q' Q R : Local_Prop) :
    2 < cote →
    P t (x + cote) →
    (∀ dx : ℕ, dx + 2 = cote → P t (x + cote) → Q' (t + 1) (x + (dx + 1))) →
    (∀ dx : ℕ, dx + 3 = cote → Q' (t + 1) (x + (dx + 2)) → Q (t + 2) (x + (dx + 1))) →
    (∀ dt dx : ℕ, 1 < dt → 0 < dx → (dt + 1) + (dx + 1) = cote →
       Q (t + dt) (x + (dx + 2)) → Q (t + dt + 1) (x + (dx + 1))) →
    (∀ dt : ℕ, dt + 2 = cote → Q (t + dt) (x + 2) → Q (t + dt + 1) (x + 1)) →
    (∀ dt : ℕ, dt + 1 = cote → Q (t + dt) (x + 1) → R (t + cote) x) →
    Diag' t x cote P Q' Q R := by
  intro hc hP topQ' topQ gen leftCol bottom
  -- Top row carries Q' at time t + 1.
  have topRow : ∀ dx : ℕ, dx + 1 = cote → Q' (t + 1) (x + dx) := by
    intro dx hdx
    obtain ⟨dx', rfl⟩ : ∃ k, dx = k + 1 := ⟨dx - 1, by omega⟩
    have h := topQ' dx' (by omega) hP
    push_cast
    exact h
  -- Interior (rows ≥ t + 2): build via `inter` with a = 1, b = 0.
  have interior : ∀ dt dx : ℕ, 1 < dt → 0 < dx → dt + dx = cote →
                    Q (t + dt) (x + dx) := by
    apply inter 1 0 cote (fun a b => Q (t + a) (x + b))
    · -- a + 1 = 2: derive `Q (t + 2) (x + ↑dx)` from the Q' top row.
      intro dx hdx hsum
      obtain ⟨dx', rfl⟩ : ∃ k, dx = k + 1 := ⟨dx - 1, by omega⟩
      have hQ' := topRow (dx' + 2) (by omega)
      -- hQ' : Q' (t + 1) (x + ↑(dx' + 2)); convert via push_cast.
      push_cast at hQ'
      have h := topQ dx' (by omega) hQ'
      push_cast
      exact h
    · -- generic interior step
      intro dt dx hdt hdx hsum hPrev
      push_cast at hPrev
      have h := gen dt dx hdt hdx (by omega) hPrev
      push_cast
      exact h
    · -- left-column step
      intro dt _ hsum hPrev
      exact leftCol dt (by omega) hPrev
  refine ⟨hc, hP, topRow, interior, ?_⟩
  have q := interior (cote - 1) 1 (by omega) (by omega) (by omega)
  exact bottom (cote - 1) (by omega) q

/-- Constructor for `Semi_Diag`. `geom.v` `Rec_SemiDiag`. -/
lemma Rec_SemiDiag (t : ℕ) (x : ℤ) (cote : ℕ) (P Q : Local_Prop) :
    0 < cote →
    P t (x + cote) →
    (∀ dx : ℕ, 1 + dx = cote → P t (x + cote) → Q (t + 1) (x + dx)) →
    (∀ dt dx : ℕ, 0 < dt → (dt + 1) + dx = cote →
       Q (t + dt) (x + (dx + 1)) → Q (t + dt + 1) (x + dx)) →
    Semi_Diag t x cote P Q := by
  intro hc hP top step
  refine ⟨hc, hP, ?_⟩
  -- Strengthen so the induction motive includes all dx; induct on dt ≥ 1.
  have key : ∀ dt, 1 ≤ dt → ∀ dx : ℕ, dt + dx = cote → Q (t + dt) (x + dx) := by
    intro dt hdt
    induction dt, hdt using Nat.le_induction with
    | base => intro dx hsum; exact top dx hsum hP
    | succ k _ ih =>
      intro dx hsum
      have h := ih (dx + 1) (by omega)
      -- h : Q (t + k) (x + ↑(dx + 1))
      push_cast at h
      exact step k dx (by omega) (by omega) h
  intro dt dx hdt hsum
  exact key dt hdt dx hsum

/-- Trivial `Diag` of side 2: an explicit one-row interior. -/
lemma deux_Diag (P Q : Local_Prop) (t : ℕ) (x : ℤ) :
    P t (x + 2) → Q (t + 1) (x + 1) → P (t + 2) x → Diag t x 2 P Q P := by
  intro h0 h1 h2
  refine ⟨by decide, h0, ?_, h2⟩
  intro dt dx hdt hdx hsum
  obtain rfl : dt = 1 := by omega
  obtain rfl : dx = 1 := by omega
  exact h1

/-- A horizontal `L`-row extends downward as a triangle. -/
lemma rec_triangle_inf (t : ℕ) (x : ℤ) (cote : ℕ) (P : Local_Prop) :
    Horizontale t x cote P →
    (∀ t' x', P t' x' → P t' (x' + 1) → P (t' + 1) (x' + 1)) →
    Triangle_inf t x cote P := by
  intro H step
  refine ⟨?_⟩
  -- Outer induction on dt, generalizing over dx so the IH can be applied
  -- at neighboring columns.
  intro dt
  induction dt with
  | zero =>
    intro dx hdx _
    -- Goal: P (t + 0) (x + ↑dx). Reduce `t + 0 = t` (defeq) and use H.
    exact H.pointwise dx hdx
  | succ n ih =>
    intro dx hdx hdt
    -- Peel off the rightmost column: dx = dx' + 1 with dx' ≥ n.
    obtain ⟨dx', rfl⟩ : ∃ k, dx = k + 1 := ⟨dx - 1, by omega⟩
    have h1 : P (t + n) (x + ↑dx') :=
      ih dx' (by omega) (by omega)
    have h2 : P (t + n) ((x + ↑dx') + 1) := by
      have h2_raw := ih (dx' + 1) (by omega) (by omega)
      -- h2_raw : P (t + n) (x + ↑(dx' + 1)); reassociate via push_cast + ring.
      have eq : ((x + ↑dx') + 1 : ℤ) = x + ↑(dx' + 1) := by push_cast; ring
      rw [eq]; exact h2_raw
    have h3 := step (t + n) (x + ↑dx') h1 h2
    -- h3 : P (t + n + 1) ((x + ↑dx') + 1); goal : P (t + (n + 1)) (x + ↑(dx' + 1))
    -- Time arg defeq via Nat.add reduction; bridge space arg through ring + cast.
    have eq : (x + ↑(dx' + 1) : ℤ) = (x + ↑dx') + 1 := by push_cast; ring
    rw [eq]
    exact h3

/-! ### Vertical / Horizontal concatenators -/

lemma inclus_vert (t t' : ℕ) (x : ℤ) (haut haut' : ℕ) (P : Local_Prop) :
    t ≤ t' → t' + haut' ≤ t + haut →
    Verticale t x haut P → Verticale t' x haut' P := by
  intro htt hsum H
  refine ⟨fun dt hdt => ?_⟩
  have h := H.pointwise ((t' - t) + dt) (by omega)
  have eq : t + ((t' - t) + dt) = t' + dt := by omega
  exact eq ▸ h

lemma vv_vert (t : ℕ) (x : ℤ) (haut haut' : ℕ) (P : Local_Prop) :
    Verticale t x haut P →
    Verticale (t + haut + 1) x haut' P →
    Verticale t x ((haut + 1) + haut') P := by
  intro H1 H2
  refine ⟨fun dt hdt => ?_⟩
  by_cases hd : dt ≤ haut
  · -- Lower segment: take from H1.
    exact H1.pointwise dt hd
  · -- Upper segment: shift index by `haut + 1`.
    push_neg at hd
    have h := H2.pointwise (dt - (haut + 1)) (by omega)
    have eq : (t + haut + 1) + (dt - (haut + 1)) = t + dt := by omega
    exact eq ▸ h

lemma rec_vert (t : ℕ) (x : ℤ) (haut : ℕ) (P : Local_Prop) :
    (∀ dt : ℕ, dt ≤ haut → P (t + double dt) x ∧ P (t + double dt + 1) x) →
    Verticale t x (double haut + 1) P := by
  intro H
  refine ⟨fun dt hdt => ?_⟩
  rcases Nat.even_or_odd dt with hev | hod
  · obtain ⟨q, hq⟩ := hev
    -- hq : dt = q + q, so dt = double q.
    have hq_le : q ≤ haut := by unfold double at hdt; omega
    have h := (H q hq_le).1
    have eq : t + dt = t + double q := by unfold double; omega
    exact eq ▸ h
  · obtain ⟨q, hq⟩ := hod
    -- hq : dt = 2 * q + 1, so dt = double q + 1.
    have hq_le : q ≤ haut := by unfold double at hdt; omega
    have h := (H q hq_le).2
    have eq : t + dt = t + double q + 1 := by unfold double; omega
    exact eq ▸ h

lemma vert_un (t : ℕ) (x : ℤ) (P : Local_Prop) :
    P t x → P (t + 1) x → Verticale t x 1 P := by
  intro h0 h1
  refine ⟨fun dt hdt => ?_⟩
  obtain rfl | rfl : dt = 0 ∨ dt = 1 := by omega
  · exact h0
  · exact h1

lemma vert_deux (t : ℕ) (x : ℤ) (P : Local_Prop) :
    P t x → P (t + 1) x → P (t + 2) x → Verticale t x 2 P := by
  intro h0 h1 h2
  refine ⟨fun dt hdt => ?_⟩
  obtain rfl | rfl | rfl : dt = 0 ∨ dt = 1 ∨ dt = 2 := by omega
  · exact h0
  · exact h1
  · exact h2

lemma vert_trois (t : ℕ) (x : ℤ) (P : Local_Prop) :
    P t x → P (t + 1) x → P (t + 2) x → P (t + 3) x → Verticale t x 3 P := by
  intro h0 h1 h2 h3
  refine ⟨fun dt hdt => ?_⟩
  obtain rfl | rfl | rfl | rfl : dt = 0 ∨ dt = 1 ∨ dt = 2 ∨ dt = 3 := by omega
  · exact h0
  · exact h1
  · exact h2
  · exact h3

lemma hh_hor (t : ℕ) (x : ℤ) (cote cote' : ℕ) (P : Local_Prop) :
    Horizontale t x cote P →
    Horizontale t (x + cote + 1) cote' P →
    Horizontale t x ((cote + 1) + cote') P := by
  intro H1 H2
  refine ⟨fun dx hdx => ?_⟩
  by_cases hd : dx ≤ cote
  · exact H1.pointwise dx hd
  · push_neg at hd
    have h := H2.pointwise (dx - (cote + 1)) (by omega)
    -- h : P t ((x + ↑cote + 1) + ↑(dx - (cote + 1)))
    -- goal : P t (x + ↑dx)
    have hsub : ((dx - (cote + 1) : ℕ) : ℤ) = (dx : ℤ) - (↑cote + 1) := by
      have hge : (cote + 1 : ℕ) ≤ dx := by omega
      rw [Nat.cast_sub hge]; push_cast; ring
    have eq : (x + ↑cote + 1) + ((dx - (cote + 1) : ℕ) : ℤ) = x + (dx : ℤ) := by
      rw [hsub]; ring
    exact eq ▸ h

lemma hor_un (t : ℕ) (x : ℤ) (P : Local_Prop) :
    P t x → P t (x + 1) → Horizontale t x 1 P := by
  intro h0 h1
  refine ⟨fun dx hdx => ?_⟩
  obtain rfl | rfl : dx = 0 ∨ dx = 1 := by omega
  · simpa using h0
  · exact h1

lemma hor_deux (t : ℕ) (x : ℤ) (P : Local_Prop) :
    P t x → P t (x + 1) → P t (x + 2) → Horizontale t x 2 P := by
  intro h0 h1 h2
  refine ⟨fun dx hdx => ?_⟩
  obtain rfl | rfl | rfl : dx = 0 ∨ dx = 1 ∨ dx = 2 := by omega
  · simpa using h0
  · exact h1
  · exact h2

lemma hor_trois (t : ℕ) (x : ℤ) (P : Local_Prop) :
    P t x → P t (x + 1) → P t (x + 2) → P t (x + 3) →
    Horizontale t x 3 P := by
  intro h0 h1 h2 h3
  refine ⟨fun dx hdx => ?_⟩
  obtain rfl | rfl | rfl | rfl : dx = 0 ∨ dx = 1 ∨ dx = 2 ∨ dx = 3 := by omega
  · simpa using h0
  · exact h1
  · exact h2
  · exact h3

lemma hor_quatre (t : ℕ) (x : ℤ) (P : Local_Prop) :
    P t x → P t (x + 1) → P t (x + 2) → P t (x + 3) → P t (x + 4) →
    Horizontale t x 4 P := by
  intro h0 h1 h2 h3 h4
  refine ⟨fun dx hdx => ?_⟩
  obtain rfl | rfl | rfl | rfl | rfl :
      dx = 0 ∨ dx = 1 ∨ dx = 2 ∨ dx = 3 ∨ dx = 4 := by omega
  · simpa using h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end FsspMazoyer
end CellularAutomatas
