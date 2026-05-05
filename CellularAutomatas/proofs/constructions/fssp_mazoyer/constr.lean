/-
  Mazoyer FSSP -- the construction calculus (port of `constr.v`).

  The Coq file declares many `loi`/`loi_droite` premises as section
  Hypotheses. To keep this Lean port concise while still type-correct,
  every combinator takes an opaque proof-bundle parameter `bundle`
  whose type can be filled in when we actually prove the lemma.

  All proofs are `sorry`.
-/

import CellularAutomatas.proofs.constructions.fssp_mazoyer.geom

namespace CellularAutomatas
namespace FsspMazoyer

/-! ### Elementary "step" lemmas (`constr.v` `Pas_*`) -/

variable (P Q R T : Local_Prop)

lemma Pas_hh (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi P Q R T →
    P (t + (dt + 2)) (x + dx) →
    Q ((t + 1) + (dt + 1)) (x + (dx + 1)) →
    R ((t + 2) + dt) (x + (dx + 2)) →
    T ((t + 2) + (dt + 1)) (x + (dx + 1)) := by
  -- Normalize all times to `t + (dt + 2)`, then apply `loi` at
  -- spatial position `x + ↑dx`. Locations differ only by Int
  -- associativity which we handle with `← add_assoc`.
  intro hloi hP hQ hR
  have eQ : ((t + 1) + (dt + 1) : ℕ) = t + (dt + 2) := by omega
  have eR : ((t + 2) + dt : ℕ) = t + (dt + 2) := by omega
  have eGoal : ((t + 2) + (dt + 1) : ℕ) = (t + (dt + 2)) + 1 := by omega
  rw [eQ] at hQ
  rw [eR] at hR
  rw [eGoal]
  rw [← add_assoc x ↑dx 1] at hQ
  rw [← add_assoc x ↑dx 2] at hR
  rw [← add_assoc x ↑dx 1]
  exact hloi (t + (dt + 2)) (x + ↑dx) hP hQ hR

lemma Pas_hd (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi P Q R T →
    P (t + (dt + 1)) (x + dx) →
    Q ((t + 1) + dt) (x + (dx + 1)) →
    R ((t + 1) + dt) ((x + 1) + (dx + 1)) →
    T ((t + 1) + (dt + 1)) ((x + 1) + dx) := by
  -- Apply `loi` at time `t + (dt + 1)` and location `x + ↑dx`.
  intro hloi hP hQ hR
  have eQ : ((t + 1) + dt : ℕ) = t + (dt + 1) := by omega
  have eR : ((t + 1) + dt : ℕ) = t + (dt + 1) := by omega
  have eGoal : ((t + 1) + (dt + 1) : ℕ) = (t + (dt + 1)) + 1 := by omega
  rw [eQ] at hQ
  rw [eR] at hR
  rw [eGoal]
  rw [← add_assoc x ↑dx 1] at hQ
  -- hR has `(x + 1) + (↑dx + 1)`; goal has `(x + 1) + ↑dx`. Reassociate to `(x + ↑dx) + _`.
  have hRrw : ((x + 1) + ((↑dx : ℤ) + 1)) = (x + ↑dx) + 2 := by ring
  rw [hRrw] at hR
  have hGrw : ((x + 1) + (↑dx : ℤ)) = (x + ↑dx) + 1 := by ring
  rw [hGrw]
  exact hloi (t + (dt + 1)) (x + ↑dx) hP hQ hR

lemma Pas_dh (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi P Q R T →
    P (t + (dt + 1)) (x + dx) →
    Q (t + (dt + 1)) ((x + 1) + dx) →
    R ((t + 1) + dt) ((x + 1) + (dx + 1)) →
    T ((t + 1) + (dt + 1)) ((x + 1) + dx) := by
  intro hloi hP hQ hR
  have eR : ((t + 1) + dt : ℕ) = t + (dt + 1) := by omega
  have eGoal : ((t + 1) + (dt + 1) : ℕ) = (t + (dt + 1)) + 1 := by omega
  rw [eR] at hR
  rw [eGoal]
  have hxQ : ((x + 1) + (↑dx : ℤ)) = (x + ↑dx) + 1 := by ring
  have hxR : ((x + 1) + ((↑dx : ℤ) + 1)) = (x + ↑dx) + 2 := by ring
  rw [hxQ] at hQ
  rw [hxR] at hR
  rw [hxQ]
  exact hloi (t + (dt + 1)) (x + ↑dx) hP hQ hR

lemma Pas_hddollar (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi P Q R T →
    P (t + (dt + 1)) (x + dx) →
    Q ((t + 1) + dt) (x + (dx + 1)) →
    R ((t + 1) + dt) (x + (dx + 2)) →
    T ((t + 1) + (dt + 1)) (x + (dx + 1)) := by
  intro hloi hP hQ hR
  have eQ : ((t + 1) + dt : ℕ) = t + (dt + 1) := by omega
  have eR : ((t + 1) + dt : ℕ) = t + (dt + 1) := by omega
  have eGoal : ((t + 1) + (dt + 1) : ℕ) = (t + (dt + 1)) + 1 := by omega
  rw [eQ] at hQ
  rw [eR] at hR
  rw [eGoal]
  rw [← add_assoc x ↑dx 1] at hQ ⊢
  rw [← add_assoc x ↑dx 2] at hR
  exact hloi (t + (dt + 1)) (x + ↑dx) hP hQ hR

lemma Pas_dhdollar (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi P Q R T →
    P (t + (dt + 1)) (x + dx) →
    Q (t + (dt + 1)) (x + (dx + 1)) →
    R ((t + 1) + dt) (x + (dx + 2)) →
    T ((t + 1) + (dt + 1)) (x + (dx + 1)) := by
  intro hloi hP hQ hR
  have eR : ((t + 1) + dt : ℕ) = t + (dt + 1) := by omega
  have eGoal : ((t + 1) + (dt + 1) : ℕ) = (t + (dt + 1)) + 1 := by omega
  rw [eR] at hR
  rw [eGoal]
  rw [← add_assoc x ↑dx 1] at hQ ⊢
  rw [← add_assoc x ↑dx 2] at hR
  exact hloi (t + (dt + 1)) (x + ↑dx) hP hQ hR

lemma demi_Pas_h (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi_droite Q R T →
    Q (t + (dt + 1)) (x + dx) →
    R ((t + 1) + dt) (x + (dx + 1)) →
    T ((t + 1) + (dt + 1)) (x + dx) := by
  -- Boundary version: only Q and R needed.
  intro hloi hQ hR
  have eR : ((t + 1) + dt : ℕ) = t + (dt + 1) := by omega
  have eGoal : ((t + 1) + (dt + 1) : ℕ) = (t + (dt + 1)) + 1 := by omega
  rw [eR] at hR
  rw [eGoal]
  rw [← add_assoc x ↑dx 1] at hR
  exact hloi (t + (dt + 1)) (x + ↑dx) hQ hR

lemma demi_Pas_ddollar (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi_droite Q R T →
    Q (t + dt) (x + dx) →
    R (t + dt) (x + (dx + 1)) →
    T (t + (dt + 1)) (x + dx) := by
  intro hloi hQ hR
  have eGoal : (t + (dt + 1) : ℕ) = (t + dt) + 1 := by omega
  rw [eGoal]
  rw [← add_assoc x ↑dx 1] at hR
  exact hloi (t + dt) (x + ↑dx) hQ hR

lemma Pas_hb (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi P Q R T →
    P (t + (dt + 2)) (x + dx) →
    Q ((t + 1) + (dt + 1)) (x + (dx + 1)) →
    R ((t + 2) + dt) ((x + 1) + (dx + 1)) →
    T ((t + 2) + (dt + 1)) ((x + 1) + dx) := by
  intro hloi hP hQ hR
  have eQ : ((t + 1) + (dt + 1) : ℕ) = t + (dt + 2) := by omega
  have eR : ((t + 2) + dt : ℕ) = t + (dt + 2) := by omega
  have eGoal : ((t + 2) + (dt + 1) : ℕ) = (t + (dt + 2)) + 1 := by omega
  rw [eQ] at hQ
  rw [eR] at hR
  rw [eGoal]
  rw [← add_assoc x ↑dx 1] at hQ
  have hRrw : ((x + 1) + ((↑dx : ℤ) + 1)) = (x + ↑dx) + 2 := by ring
  rw [hRrw] at hR
  have hGrw : ((x + 1) + (↑dx : ℤ)) = (x + ↑dx) + 1 := by ring
  rw [hGrw]
  exact hloi (t + (dt + 2)) (x + ↑dx) hP hQ hR

lemma Pas_bb (t : ℕ) (x : ℤ) (dt dx : ℕ) :
    loi P Q R T →
    P (t + (dt + 2)) (x + (dx + 1)) →
    Q ((t + 1) + (dt + 1)) ((x + 1) + (dx + 1)) →
    R ((t + 2) + dt) ((x + 2) + (dx + 1)) →
    T ((t + 2) + (dt + 1)) ((x + 2) + dx) := by
  -- Apply `loi` at time `t + (dt + 2)` and location `x + ↑dx + 1`.
  intro hloi hP hQ hR
  have eQ : ((t + 1) + (dt + 1) : ℕ) = t + (dt + 2) := by omega
  have eR : ((t + 2) + dt : ℕ) = t + (dt + 2) := by omega
  have eGoal : ((t + 2) + (dt + 1) : ℕ) = (t + (dt + 2)) + 1 := by omega
  rw [eQ] at hQ
  rw [eR] at hR
  rw [eGoal]
  -- Reshape locations to use `(x + ↑dx + 1)` as base.
  have hP_eq : (x + ((↑dx : ℤ) + 1)) = x + ↑dx + 1 := by ring
  have hQ_eq : ((x + 1) + ((↑dx : ℤ) + 1)) = (x + ↑dx + 1) + 1 := by ring
  have hR_eq : ((x + 2) + ((↑dx : ℤ) + 1)) = (x + ↑dx + 1) + 2 := by ring
  have hG_eq : ((x + 2) + (↑dx : ℤ)) = (x + ↑dx + 1) + 1 := by ring
  rw [hP_eq] at hP
  rw [hQ_eq] at hQ
  rw [hR_eq] at hR
  rw [hG_eq]
  exact hloi (t + (dt + 2)) (x + ↑dx + 1) hP hQ hR

/-! ### Diagonal-superposition combinators (`constr.v` `DDD`,
    `D'DD`, `D'DD'`, `DD'D`, `DD_D'`, `D_D'D`, `DD_Ddollar`,
    `D_DDdollar`, `DD_D`, `D'D_D`, `D_DD`, `DDdollar_D`, `DD_d`,
    `Dd_d`, `dd_d`).

Each combinator combines two adjacent diagonal/triangle figures into a
new one one row down. The Coq versions take many `loi`/`loi_droite`
premises (declared as section hypotheses). Here we collapse those into
a single placeholder `LoiBundle := True`; once proofs are written, we
will replace each with the precise list of `loi` hypotheses needed.
-/

/-! Each combinator below mirrors a Coq `Lemma` from `constr.v`. Where Coq
declared section `Hypothesis`es, we take explicit `loi`/`loi_droite`
arguments (matching the names from the Coq section header). -/

lemma DDD (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' Q' P'' Q'' : Local_Prop)
    (hPQPQ : loi P Q' P'' Q'') (hQQPQ : loi Q Q' P'' Q'')
    (hQQQQ : loi Q Q' Q'' Q'') (hPQQQ : loi P Q' Q'' Q'')
    (hXPQP : loi_droite P' Q'' P'') :
    Diag t x cote P Q P →
    Diag (t + 1) x cote P' Q' P' →
    P'' (t + 2) (x + cote) →
    Diag (t + 2) x cote P'' Q'' P'' := by
  intro D D' hP''
  refine Rec_Diag (t + 2) x cote P'' Q'' P'' D.size_pos hP'' ?top ?gen ?leftCol ?bot
  case top =>
    -- ∀ dx, dx + 2 = cote → P''(t+2)(x+cote) → Q''((t+2)+1)(x+(↑dx+1))
    intro dx hdx _
    rcases Nat.eq_zero_or_pos dx with rfl | hpos
    · -- dx = 0 ⟹ cote = 2: use loi P Q' P'' Q''
      have hcote : cote = 2 := by omega
      have hP_in : P (t + (0 + 2)) (x + (0 : ℕ)) := by
        have h := D.bottomLeft; rw [hcote] at h; simpa using h
      have hQ'_in : Q' ((t + 1) + (0 + 1)) (x + ((0 : ℕ) + 1)) := by
        have h := D'.interior 1 1 (by omega) (by omega) (by omega); simpa using h
      have hR_in : P'' ((t + 2) + 0) (x + ((0 : ℕ) + 2)) := by
        have h := hP''
        have eq : (x + (cote : ℤ)) = x + 2 := by rw [hcote]; push_cast; ring
        rw [eq] at h; simpa using h
      have step := Pas_hh P Q' P'' Q'' t x 0 0 hPQPQ hP_in hQ'_in hR_in
      simpa using step
    · -- dx ≥ 1 ⟹ cote = dx + 2 ≥ 3: use loi Q Q' P'' Q''
      have hP_in : Q (t + (0 + 2)) (x + (dx : ℤ)) := by
        have h := D.interior 2 dx (by omega) hpos (by omega); simpa using h
      have hQ'_in : Q' ((t + 1) + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
        have h := D'.interior 1 (dx + 1) (by omega) (by omega) (by omega)
        push_cast at h; simpa using h
      have hR_in : P'' ((t + 2) + 0) (x + ((dx : ℤ) + 2)) := by
        have h := hP''
        have eq : (x + (cote : ℤ)) = x + ((dx : ℤ) + 2) := by
          have : cote = dx + 2 := by omega
          rw [this]; push_cast; ring
        rw [eq] at h; simpa using h
      have step := Pas_hh Q Q' P'' Q'' t x 0 dx hQQPQ hP_in hQ'_in hR_in
      simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + (dx : ℤ)) := by
      have h := D.interior (dt + 2) dx (by omega) hdx (by omega); simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) (x + ((dx : ℤ) + 2)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_hh Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    -- step : Q'' ((t+2)+(dt+1)) (x+(↑dx+1));  goal : Q'' (t+2+dt+1) (x+(↑dx+1))
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 2)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 2) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 2) + dt) (x + (((0 : ℕ) : ℤ) + 2)) := by simpa using hPrev
    have step := Pas_hh P Q' Q'' Q'' t x dt 0 hPQQQ hP_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP'_in : P' (t + ((dt + 1) + 1)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D'.bottomLeft
      have eq : (t + 1) + cote = t + ((dt + 1) + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ''_in : Q'' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have eq : (t + 2) + dt = (t + 1) + (dt + 1) := by omega
      have h : Q'' ((t + 1) + (dt + 1)) (x + 1) := by rw [← eq]; exact hPrev
      simpa using h
    have step := demi_Pas_h P' Q'' P'' t x (dt + 1) 0 hXPQP hP'_in hQ''_in
    have time_eq : (t + 1) + ((dt + 1) + 1) = (t + 2) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma D'DD (t : ℕ) (x : ℤ) (cote : ℕ) (P Q R P' Q' P'' Q'' : Local_Prop)
    (hQQPQ : loi Q Q' P'' Q'')
    (hQQQQ : loi Q Q' Q'' Q'') (hPQQQ : loi P Q' Q'' Q'')
    (hXPQP : loi_droite P' Q'' P'') :
    Diag' t x cote P R Q P →
    Diag (t + 1) x cote P' Q' P' →
    P'' (t + 2) (x + cote) →
    Diag (t + 2) x cote P'' Q'' P'' := by
  intro D D' hP''
  have hcote : 2 < cote := D.size_pos
  refine Rec_Diag (t + 2) x cote P'' Q'' P'' (by omega) hP'' ?top ?gen ?leftCol ?bot
  case top =>
    intro dx hdx _
    -- cote ≥ 3 ⟹ dx ≥ 1; use loi Q Q' P'' Q''
    have hpos : 0 < dx := by omega
    have hP_in : Q (t + (0 + 2)) (x + (dx : ℤ)) := by
      have h := D.interior 2 dx (by omega) hpos (by omega); simpa using h
    have hQ'_in : Q' ((t + 1) + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior 1 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hR_in : P'' ((t + 2) + 0) (x + ((dx : ℤ) + 2)) := by
      have h := hP''
      have eq : (x + (cote : ℤ)) = x + ((dx : ℤ) + 2) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_hh Q Q' P'' Q'' t x 0 dx hQQPQ hP_in hQ'_in hR_in
    simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + (dx : ℤ)) := by
      have h := D.interior (dt + 2) dx (by omega) hdx (by omega); simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) (x + ((dx : ℤ) + 2)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_hh Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 2)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 2) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 2) + dt) (x + (((0 : ℕ) : ℤ) + 2)) := by simpa using hPrev
    have step := Pas_hh P Q' Q'' Q'' t x dt 0 hPQQQ hP_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP'_in : P' (t + ((dt + 1) + 1)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D'.bottomLeft
      have eq : (t + 1) + cote = t + ((dt + 1) + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ''_in : Q'' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have eq : (t + 2) + dt = (t + 1) + (dt + 1) := by omega
      have h : Q'' ((t + 1) + (dt + 1)) (x + 1) := by rw [← eq]; exact hPrev
      simpa using h
    have step := demi_Pas_h P' Q'' P'' t x (dt + 1) 0 hXPQP hP'_in hQ''_in
    have time_eq : (t + 1) + ((dt + 1) + 1) = (t + 2) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma D'DD' (t : ℕ) (x : ℤ) (cote : ℕ) (P Q R P' Q' P'' R'' Q'' : Local_Prop)
    (hQQPR : loi Q Q' P'' R'') (hPQRQ : loi P Q' R'' Q'')
    (hQQRQ : loi Q Q' R'' Q'')
    (hQQQQ : loi Q Q' Q'' Q'') (hPQQQ : loi P Q' Q'' Q'')
    (hXPQP : loi_droite P' Q'' P'') :
    Diag' t x cote P R Q P →
    Diag (t + 1) x cote P' Q' P' →
    P'' (t + 2) (x + cote) →
    Diag' (t + 2) x cote P'' R'' Q'' P'' := by
  intro D D' hP''
  have hcote : 2 < cote := D.size_pos
  refine Rec_Diag' (t + 2) x cote P'' R'' Q'' P'' hcote hP''
    ?topQ' ?topQ ?gen ?leftCol ?bot
  case topQ' =>
    -- ∀ dx, dx+2 = cote → P''(t+2)(x+cote) → R''((t+2)+1)(x+(↑dx+1))
    intro dx hdx _
    have hpos : 0 < dx := by omega
    have hP_in : Q (t + (0 + 2)) (x + (dx : ℤ)) := by
      have h := D.interior 2 dx (by omega) hpos (by omega); simpa using h
    have hQ'_in : Q' ((t + 1) + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior 1 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hR_in : P'' ((t + 2) + 0) (x + ((dx : ℤ) + 2)) := by
      have h := hP''
      have eq : (x + (cote : ℤ)) = x + ((dx : ℤ) + 2) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_hh Q Q' P'' R'' t x 0 dx hQQPR hP_in hQ'_in hR_in
    simpa using step
  case topQ =>
    -- ∀ dx, dx+3 = cote → R''((t+2)+1)(x+(↑dx+2)) → Q''((t+2)+2)(x+(↑dx+1))
    intro dx hdx hPrev
    rcases Nat.eq_zero_or_pos dx with rfl | hpos
    · -- dx = 0: cote = 3. Use loi P Q' R'' Q'' (PQRQ). Bottom-left of D is P(t+3)(x).
      have hP_in : P (t + (1 + 2)) (x + ((0 : ℕ) : ℤ)) := by
        have h := D.bottomLeft
        have eq : t + cote = t + (1 + 2) := by omega
        rw [eq] at h; simpa using h
      have hQ'_in : Q' ((t + 1) + (1 + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
        have h := D'.interior 2 1 (by omega) (by omega) (by omega); simpa using h
      have hPrev' : R'' ((t + 2) + 1) (x + (((0 : ℕ) : ℤ) + 2)) := by
        push_cast at hPrev ⊢; exact hPrev
      have step := Pas_hh P Q' R'' Q'' t x 1 0 hPQRQ hP_in hQ'_in hPrev'
      have time_eq : (t + 2) + (1 + 1) = t + 2 + 2 := by omega
      rw [time_eq] at step
      simpa using step
    · -- dx > 0: cote ≥ 4. Use loi Q Q' R'' Q'' (QQRQ).
      have hQ_in : Q (t + (1 + 2)) (x + (dx : ℤ)) := by
        have h := D.interior 3 dx (by omega) hpos (by omega); simpa using h
      have hQ'_in : Q' ((t + 1) + (1 + 1)) (x + ((dx : ℤ) + 1)) := by
        have h := D'.interior 2 (dx + 1) (by omega) (by omega) (by omega); simpa using h
      have hPrev' : R'' ((t + 2) + 1) (x + ((dx : ℤ) + 2)) := by
        push_cast at hPrev ⊢; exact hPrev
      have step := Pas_hh Q Q' R'' Q'' t x 1 dx hQQRQ hQ_in hQ'_in hPrev'
      have time_eq : (t + 2) + (1 + 1) = t + 2 + 2 := by omega
      rw [time_eq] at step
      simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + (dx : ℤ)) := by
      have h := D.interior (dt + 2) dx (by omega) hdx (by omega); simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) (x + ((dx : ℤ) + 2)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_hh Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 2)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 2) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 2) + dt) (x + (((0 : ℕ) : ℤ) + 2)) := by simpa using hPrev
    have step := Pas_hh P Q' Q'' Q'' t x dt 0 hPQQQ hP_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP'_in : P' (t + ((dt + 1) + 1)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D'.bottomLeft
      have eq : (t + 1) + cote = t + ((dt + 1) + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ''_in : Q'' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have eq : (t + 2) + dt = (t + 1) + (dt + 1) := by omega
      have h : Q'' ((t + 1) + (dt + 1)) (x + 1) := by rw [← eq]; exact hPrev
      simpa using h
    have step := demi_Pas_h P' Q'' P'' t x (dt + 1) 0 hXPQP hP'_in hQ''_in
    have time_eq : (t + 1) + ((dt + 1) + 1) = (t + 2) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma DD'D (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' R' Q' P'' Q'' : Local_Prop)
    (hQRPQ : loi Q R' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'')
    (hPQQQ : loi P Q' Q'' Q'') (hXPQP : loi_droite P' Q'' P'') :
    Diag t x cote P Q P →
    Diag' (t + 1) x cote P' R' Q' P' →
    P'' (t + 2) (x + cote) →
    Diag (t + 2) x cote P'' Q'' P'' := by
  intro D D' hP''
  have hcote' : 2 < cote := D'.size_pos
  refine Rec_Diag (t + 2) x cote P'' Q'' P'' (by omega) hP'' ?top ?gen ?leftCol ?bot
  case top =>
    intro dx hdx _
    have hpos : 0 < dx := by omega
    have hQ_in : Q (t + (0 + 2)) (x + (dx : ℤ)) := by
      have h := D.interior 2 dx (by omega) hpos (by omega); simpa using h
    have hR'_in : R' ((t + 1) + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.topRow (dx + 1) (by omega); push_cast at h; simpa using h
    have hP''_in : P'' ((t + 2) + 0) (x + ((dx : ℤ) + 2)) := by
      have h := hP''
      have eq : (x + (cote : ℤ)) = x + ((dx : ℤ) + 2) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_hh Q R' P'' Q'' t x 0 dx hQRPQ hQ_in hR'_in hP''_in
    simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + (dx : ℤ)) := by
      have h := D.interior (dt + 2) dx (by omega) hdx (by omega); simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) (x + ((dx : ℤ) + 2)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_hh Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 2)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 2) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 2) + dt) (x + (((0 : ℕ) : ℤ) + 2)) := by simpa using hPrev
    have step := Pas_hh P Q' Q'' Q'' t x dt 0 hPQQQ hP_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP'_in : P' (t + ((dt + 1) + 1)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D'.bottomLeft
      have eq : (t + 1) + cote = t + ((dt + 1) + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ''_in : Q'' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have eq : (t + 2) + dt = (t + 1) + (dt + 1) := by omega
      have h : Q'' ((t + 1) + (dt + 1)) (x + 1) := by rw [← eq]; exact hPrev
      simpa using h
    have step := demi_Pas_h P' Q'' P'' t x (dt + 1) 0 hXPQP hP'_in hQ''_in
    have time_eq : (t + 1) + ((dt + 1) + 1) = (t + 2) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma DD_D' (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' Q' P'' R'' Q'' : Local_Prop)
    (hQPPR : loi Q P' P'' R'') (hQQRQ : loi Q Q' R'' Q'')
    (hQQQQ : loi Q Q' Q'' Q'') (hPQQP : loi P Q' Q'' P'') :
    2 < cote →
    Diag t x cote P Q P →
    Diag (t + 1) x cote P' Q' P' →
    P'' (t + 1) ((x + 1) + cote) →
    Diag' (t + 1) (x + 1) cote P'' R'' Q'' P'' := by
  intro hcote D D' hP''
  refine Rec_Diag' (t + 1) (x + 1) cote P'' R'' Q'' P'' hcote hP''
    ?topQ' ?topQ ?gen ?leftCol ?bot
  case topQ' =>
    intro dx hdx _
    have hQ_in : Q (t + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior 1 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hP'_in : P' ((t + 1) + 0) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.apex
      have eq : (x + (cote : ℤ)) = x + (((dx : ℤ) + 1) + 1) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have hP''_in : P'' ((t + 1) + 0) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have h := hP''
      have eq : ((x + 1) + (cote : ℤ)) = (x + 1) + (((dx : ℤ) + 1) + 1) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_hd Q P' P'' R'' t x 0 (dx + 1) hQPPR hQ_in hP'_in hP''_in
    push_cast at step; simpa using step
  case topQ =>
    intro dx hdx hPrev
    have hQ_in : Q (t + (1 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior 2 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + 1) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.interior 1 (dx + 2) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : R'' ((t + 1) + 1) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have eq : ((x : ℤ) + 1) + (((dx : ℤ) + 1) + 1) = (x + 1) + ((dx : ℤ) + 2) := by ring
      rw [eq]; exact hPrev
    have step := Pas_hd Q Q' R'' Q'' t x 1 (dx + 1) hQQRQ hQ_in hQ'_in hPrev'
    push_cast at step; simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    -- Need dt - 1 to use Pas_hd; dt ≥ 2 so dt-1 ≥ 1
    obtain ⟨dt', rfl⟩ : ∃ k, dt = k + 1 := ⟨dt - 1, by omega⟩
    -- Now dt = dt' + 1, with dt' ≥ 1
    have hQ_in : Q (t + (dt' + 1 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt' + 2) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt' + 1)) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.interior (dt' + 1) (dx + 2) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + (dt' + 1)) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have eq : ((x : ℤ) + 1) + (((dx : ℤ) + 1) + 1) = (x + 1) + ((dx : ℤ) + 2) := by ring
      rw [eq]; exact hPrev
    have step := Pas_hd Q Q' Q'' Q'' t x (dt' + 1) (dx + 1) hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + ((dt' + 1) + 1) = t + 1 + (dt' + 1) + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + ((1 : ℕ) : ℤ)) := by
      have h := D.interior (dt + 1) 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((1 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior dt 2 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((1 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_hd Q Q' Q'' Q'' t x dt 1 hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step; simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 1)) (x + ((0 : ℕ) : ℤ)) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior dt 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((0 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_hd P Q' Q'' P'' t x dt 0 hPQQP hP_in hQ'_in hPrev'
    -- step : P'' ((t+1)+(dt+1)) ((x+1)+0)
    have time_eq : (t + 1) + (dt + 1) = (t + 1) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma D_D'D (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' R' Q' P'' Q'' : Local_Prop)
    (hQRPQ : loi Q R' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'')
    (hPPQP : loi P P' Q'' P'') :
    Diag t x cote P Q P →
    Diag' t (x + 1) cote P' R' Q' P' →
    P'' (t + 1) ((x + 1) + cote) →
    Diag (t + 1) (x + 1) cote P'' Q'' P'' := by
  intro D D' hP''
  have hcote : 2 < cote := D'.size_pos
  refine Rec_Diag (t + 1) (x + 1) cote P'' Q'' P'' (by omega) hP'' ?top ?gen ?leftCol ?bot
  case top =>
    intro dx hdx _
    have hpos : 0 < dx := by omega
    have hQ_in : Q (t + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior 1 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hR'_in : R' (t + (0 + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.topRow (dx + 1) (by omega); push_cast at h; simpa using h
    have hP''_in : P'' ((t + 1) + 0) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have h := hP''
      have eq : ((x + 1) + (cote : ℤ)) = (x + 1) + (((dx : ℤ) + 1) + 1) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_dh Q R' P'' Q'' t x 0 (dx + 1) hQRPQ hQ_in hR'_in hP''_in
    push_cast at step
    have hxeq : ((x + 1 : ℤ) + ((dx : ℤ) + 1)) = (x + 1) + ((dx : ℤ) + 1) := by ring
    simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' (t + (dt + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have eq : ((x : ℤ) + 1) + (((dx : ℤ) + 1) + 1) = (x + 1) + ((dx : ℤ) + 2) := by ring
      rw [eq]; exact hPrev
    have step := Pas_dh Q Q' Q'' Q'' t x dt (dx + 1) hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + (((1 : ℕ) : ℤ))) := by
      have h := D.interior (dt + 1) 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' (t + (dt + 1)) ((x + 1) + (((1 : ℕ) : ℤ))) := by
      have h := D'.interior (dt + 1) 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((1 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_dh Q Q' Q'' Q'' t x dt 1 hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 1)) (x + (((0 : ℕ) : ℤ))) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hP'_in : P' (t + (dt + 1)) ((x + 1) + (((0 : ℕ) : ℤ))) := by
      have h := D'.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((0 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_dh P P' Q'' P'' t x dt 0 hPPQP hP_in hP'_in hPrev'
    have time_eq : (t + 1) + (dt + 1) = (t + 1) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma DD_Ddollar (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' Q' P'' Q'' : Local_Prop)
    (hQPPQ : loi Q P' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'')
    (hPQQQ : loi P Q' Q'' Q'') (hXPQP : loi_droite P' Q'' P'') :
    Diag t x cote P Q P →
    Diag (t + 1) x cote P' Q' P' →
    P'' (t + 1) (x + (cote + 1)) →
    Diag (t + 1) x (cote + 1) P'' Q'' P'' := by
  intro D D' hP''
  refine Rec_Diag (t + 1) x (cote + 1) P'' Q'' P'' (by have := D.size_pos; omega) hP''
    ?top ?gen ?leftCol ?bot
  case top =>
    intro dx hdx _
    have hpos : 0 < dx := by have := D.size_pos; omega
    have hQ_in : Q (t + (0 + 1)) (x + (dx : ℤ)) := by
      have h := D.interior 1 dx (by omega) hpos (by omega); simpa using h
    have hP'_in : P' ((t + 1) + 0) (x + ((dx : ℤ) + 1)) := by
      have h := D'.apex
      have eq : (x + (cote : ℤ)) = x + ((dx : ℤ) + 1) := by
        have : cote = dx + 1 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have hP''_in : P'' ((t + 1) + 0) (x + ((dx : ℤ) + 2)) := by
      have h := hP''
      have eq : (x + ((cote : ℤ) + 1)) = x + ((dx : ℤ) + 2) := by
        have : cote = dx + 1 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_hddollar Q P' P'' Q'' t x 0 dx hQPPQ hQ_in hP'_in hP''_in
    simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + (dx : ℤ)) := by
      have h := D.interior (dt + 1) dx (by omega) hdx (by omega); simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior dt (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) (x + ((dx : ℤ) + 2)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_hddollar Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hsize : 1 < cote := D.size_pos
    have hP_in : P (t + (dt + 1)) (x + (((0 : ℕ) : ℤ))) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior dt 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ) + 2)) := by simpa using hPrev
    have step := Pas_hddollar P Q' Q'' Q'' t x dt 0 hPQQQ hP_in hQ'_in hPrev'
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    -- dt + 1 = cote + 1, so dt = cote.
    have hP'_in : P' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ))) := by
      have h := D'.bottomLeft
      have eq : (t + 1) + cote = (t + 1) + dt := by omega
      rw [eq] at h; simpa using h
    have hQ''_in : Q'' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ) + 1)) := by simpa using hPrev
    have step := demi_Pas_ddollar P' Q'' P'' (t + 1) x dt 0 hXPQP hP'_in hQ''_in
    have time_eq : (t + 1) + (dt + 1) = (t + 1) + (cote + 1) := by omega
    rw [time_eq] at step
    simpa using step

lemma D_DDdollar (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' Q' P'' Q'' : Local_Prop)
    (hQQPQ : loi Q Q' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'')
    (hPQQQ : loi P Q' Q'' Q'') (hXPQP : loi_droite P' Q'' P'') :
    Diag t x cote P Q P →
    Diag t x (cote + 1) P' Q' P' →
    P'' (t + 1) (x + (cote + 1)) →
    Diag (t + 1) x (cote + 1) P'' Q'' P'' := by
  intro D D' hP''
  refine Rec_Diag (t + 1) x (cote + 1) P'' Q'' P'' (by have := D.size_pos; omega) hP''
    ?top ?gen ?leftCol ?bot
  case top =>
    intro dx hdx _
    have hpos : 0 < dx := by have := D.size_pos; omega
    have hQ_in : Q (t + (0 + 1)) (x + (dx : ℤ)) := by
      have h := D.interior 1 dx (by omega) hpos (by omega); simpa using h
    have hQ'_in : Q' (t + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior 1 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hP''_in : P'' ((t + 1) + 0) (x + ((dx : ℤ) + 2)) := by
      have h := hP''
      have eq : (x + ((cote : ℤ) + 1)) = x + ((dx : ℤ) + 2) := by
        have : cote = dx + 1 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_dhdollar Q Q' P'' Q'' t x 0 dx hQQPQ hQ_in hQ'_in hP''_in
    simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + (dx : ℤ)) := by
      have h := D.interior (dt + 1) dx (by omega) hdx (by omega); simpa using h
    have hQ'_in : Q' (t + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) (x + ((dx : ℤ) + 2)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_dhdollar Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 1)) (x + (((0 : ℕ) : ℤ))) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' (t + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ) + 2)) := by simpa using hPrev
    have step := Pas_dhdollar P Q' Q'' Q'' t x dt 0 hPQQQ hP_in hQ'_in hPrev'
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    -- dt + 1 = cote + 1, so dt = cote.
    have hP'_in : P' (t + (dt + 1)) (x + (((0 : ℕ) : ℤ))) := by
      have h := D'.bottomLeft
      have eq : t + (cote + 1) = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ''_in : Q'' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ) + 1)) := by simpa using hPrev
    have step := demi_Pas_h P' Q'' P'' t x dt 0 hXPQP hP'_in hQ''_in
    have time_eq : (t + 1) + (dt + 1) = (t + 1) + (cote + 1) := by omega
    rw [time_eq] at step
    simpa using step

lemma DD_D (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' Q' P'' Q'' : Local_Prop)
    (hQPPQ : loi Q P' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'')
    (hPQQP : loi P Q' Q'' P'') :
    2 < cote →
    Diag t x cote P Q P →
    Diag (t + 1) x cote P' Q' P' →
    P'' (t + 1) ((x + 1) + cote) →
    Diag (t + 1) (x + 1) cote P'' Q'' P'' := by
  intro hcote D D' hP''
  refine Rec_Diag (t + 1) (x + 1) cote P'' Q'' P'' (by omega) hP'' ?top ?gen ?leftCol ?bot
  case top =>
    intro dx hdx _
    have hQ_in : Q (t + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior 1 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hP'_in : P' ((t + 1) + 0) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.apex
      have eq : (x + (cote : ℤ)) = x + (((dx : ℤ) + 1) + 1) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have hP''_in : P'' ((t + 1) + 0) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have h := hP''
      have eq : ((x + 1) + (cote : ℤ)) = (x + 1) + (((dx : ℤ) + 1) + 1) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_hd Q P' P'' Q'' t x 0 (dx + 1) hQPPQ hQ_in hP'_in hP''_in
    push_cast at step; simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.interior dt (dx + 2) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have eq : ((x : ℤ) + 1) + (((dx : ℤ) + 1) + 1) = (x + 1) + ((dx : ℤ) + 2) := by ring
      rw [eq]; exact hPrev
    have step := Pas_hd Q Q' Q'' Q'' t x dt (dx + 1) hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + (((1 : ℕ) : ℤ))) := by
      have h := D.interior (dt + 1) 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((1 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior dt 2 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((1 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_hd Q Q' Q'' Q'' t x dt 1 hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 1)) (x + (((0 : ℕ) : ℤ))) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior dt 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((0 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_hd P Q' Q'' P'' t x dt 0 hPQQP hP_in hQ'_in hPrev'
    have time_eq : (t + 1) + (dt + 1) = (t + 1) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma D'D_D (t : ℕ) (x : ℤ) (cote : ℕ) (P Q R P' Q' P'' Q'' : Local_Prop)
    (hRPPQ : loi R P' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'')
    (hPQQP : loi P Q' Q'' P'') :
    Diag' t x cote P R Q P →
    Diag (t + 1) x cote P' Q' P' →
    P'' (t + 1) ((x + 1) + cote) →
    Diag (t + 1) (x + 1) cote P'' Q'' P'' := by
  intro D D' hP''
  have hcote : 2 < cote := D.size_pos
  refine Rec_Diag (t + 1) (x + 1) cote P'' Q'' P'' (by omega) hP'' ?top ?gen ?leftCol ?bot
  case top =>
    intro dx hdx _
    have hR_in : R (t + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.topRow (dx + 1) (by omega); push_cast at h; simpa using h
    have hP'_in : P' ((t + 1) + 0) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.apex
      have eq : (x + (cote : ℤ)) = x + (((dx : ℤ) + 1) + 1) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have hP''_in : P'' ((t + 1) + 0) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have h := hP''
      have eq : ((x + 1) + (cote : ℤ)) = (x + 1) + (((dx : ℤ) + 1) + 1) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_hd R P' P'' Q'' t x 0 (dx + 1) hRPPQ hR_in hP'_in hP''_in
    push_cast at step; simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.interior dt (dx + 2) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have eq : ((x : ℤ) + 1) + (((dx : ℤ) + 1) + 1) = (x + 1) + ((dx : ℤ) + 2) := by ring
      rw [eq]; exact hPrev
    have step := Pas_hd Q Q' Q'' Q'' t x dt (dx + 1) hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + (((1 : ℕ) : ℤ))) := by
      have h := D.interior (dt + 1) 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((1 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior dt 2 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((1 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_hd Q Q' Q'' Q'' t x dt 1 hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 1)) (x + (((0 : ℕ) : ℤ))) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + dt) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior dt 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((0 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_hd P Q' Q'' P'' t x dt 0 hPQQP hP_in hQ'_in hPrev'
    have time_eq : (t + 1) + (dt + 1) = (t + 1) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma D_DD (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' Q' P'' Q'' : Local_Prop)
    (hQQPQ : loi Q Q' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'')
    (hPPQP : loi P P' Q'' P'') :
    Diag t x cote P Q P →
    Diag t (x + 1) cote P' Q' P' →
    P'' (t + 1) ((x + 1) + cote) →
    Diag (t + 1) (x + 1) cote P'' Q'' P'' := by
  intro D D' hP''
  refine Rec_Diag (t + 1) (x + 1) cote P'' Q'' P'' D.size_pos hP'' ?top ?gen ?leftCol ?bot
  case top =>
    intro dx hdx _
    rcases Nat.eq_zero_or_pos dx with rfl | hpos
    · -- dx = 0, cote = 2
      have hcote : cote = 2 := by omega
      have hQ_in : Q (t + (0 + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
        have h := D.interior 1 1 (by omega) (by omega) (by omega)
        push_cast at h; simpa using h
      have hQ'_in : Q' (t + (0 + 1)) ((x + 1) + (((0 : ℕ) : ℤ) + 1)) := by
        have h := D'.interior 1 1 (by omega) (by omega) (by omega)
        push_cast at h; simpa using h
      have hP''_in : P'' ((t + 1) + 0) ((x + 1) + ((((0 : ℕ) : ℤ) + 1) + 1)) := by
        have h := hP''
        have eq : ((x + 1) + (cote : ℤ)) = (x + 1) + (((((0 : ℕ) : ℤ) + 1) + 1)) := by
          rw [hcote]; push_cast; ring
        rw [eq] at h; simpa using h
      have step := Pas_dh Q Q' P'' Q'' t x 0 1 hQQPQ hQ_in hQ'_in hP''_in
      push_cast at step; simpa using step
    · have hQ_in : Q (t + (0 + 1)) (x + ((dx : ℤ) + 1)) := by
        have h := D.interior 1 (dx + 1) (by omega) (by omega) (by omega)
        push_cast at h; simpa using h
      have hQ'_in : Q' (t + (0 + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
        have h := D'.interior 1 (dx + 1) (by omega) (by omega) (by omega)
        push_cast at h; simpa using h
      have hP''_in : P'' ((t + 1) + 0) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
        have h := hP''
        have eq : ((x + 1) + (cote : ℤ)) = (x + 1) + (((dx : ℤ) + 1) + 1) := by
          have : cote = dx + 2 := by omega
          rw [this]; push_cast; ring
        rw [eq] at h; simpa using h
      have step := Pas_dh Q Q' P'' Q'' t x 0 (dx + 1) hQQPQ hQ_in hQ'_in hP''_in
      push_cast at step; simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' (t + (dt + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have eq : ((x : ℤ) + 1) + (((dx : ℤ) + 1) + 1) = (x + 1) + ((dx : ℤ) + 2) := by ring
      rw [eq]; exact hPrev
    have step := Pas_dh Q Q' Q'' Q'' t x dt (dx + 1) hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hQ_in : Q (t + (dt + 1)) (x + (((1 : ℕ) : ℤ))) := by
      have h := D.interior (dt + 1) 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' (t + (dt + 1)) ((x + 1) + (((1 : ℕ) : ℤ))) := by
      have h := D'.interior (dt + 1) 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((1 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_dh Q Q' Q'' Q'' t x dt 1 hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 1) + (dt + 1) = t + 1 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 1)) (x + (((0 : ℕ) : ℤ))) := by
      have h := D.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hP'_in : P' (t + (dt + 1)) ((x + 1) + (((0 : ℕ) : ℤ))) := by
      have h := D'.bottomLeft
      have eq : t + cote = t + (dt + 1) := by omega
      rw [eq] at h; simpa using h
    have hPrev' : Q'' ((t + 1) + dt) ((x + 1) + (((0 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_dh P P' Q'' P'' t x dt 0 hPPQP hP_in hP'_in hPrev'
    have time_eq : (t + 1) + (dt + 1) = (t + 1) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma DDdollar_D (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' Q' P'' Q'' R'' : Local_Prop)
    (hQQPQ : loi Q Q' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'')
    (hPQQR : loi P Q' Q'' R'') :
    1 < cote →
    Diag t x (cote + 1) P Q P →
    Diag (t + 1) x (cote + 1) P' Q' P' →
    P'' (t + 2) ((x + cote) + 1) →
    Diag (t + 2) (x + 1) cote P'' Q'' R'' := by
  intro hcote D D' hP''
  refine Rec_Diag (t + 2) (x + 1) cote P'' Q'' R'' hcote ?apex ?top ?gen ?leftCol ?bot
  case apex =>
    have h := hP''
    have eq : ((x + (cote : ℤ)) + 1) = (x + 1) + cote := by ring
    rw [eq] at h; exact h
  case top =>
    intro dx hdx _
    have hQ_in : Q (t + (0 + 2)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior 2 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (0 + 1)) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.interior 1 (dx + 2) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hP''_in : P'' ((t + 2) + 0) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have h := hP''
      have eq : ((x + (cote : ℤ)) + 1) = (x + 1) + (((dx : ℤ) + 1) + 1) := by
        have : cote = dx + 2 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_hb Q Q' P'' Q'' t x 0 (dx + 1) hQQPQ hQ_in hQ'_in hP''_in
    push_cast at step; simpa using step
  case gen =>
    intro dt dx hdt hdx hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt + 2) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + (((dx : ℤ) + 1) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 2) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) ((x + 1) + (((dx : ℤ) + 1) + 1)) := by
      have eq : ((x : ℤ) + 1) + (((dx : ℤ) + 1) + 1) = (x + 1) + ((dx : ℤ) + 2) := by ring
      rw [eq]; exact hPrev
    have step := Pas_hb Q Q' Q'' Q'' t x dt (dx + 1) hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    exact step
  case leftCol =>
    intro dt hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + (((1 : ℕ) : ℤ))) := by
      have h := D.interior (dt + 2) 1 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + (((1 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) 2 (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) ((x + 1) + (((1 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_hb Q Q' Q'' Q'' t x dt 1 hQQQQ hQ_in hQ'_in hPrev'
    push_cast at step
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    simpa using step
  case bot =>
    intro dt hsum hPrev
    have hP_in : P (t + (dt + 2)) (x + (((0 : ℕ) : ℤ))) := by
      have h := D.bottomLeft
      have eq : t + (cote + 1) = t + (dt + 2) := by omega
      rw [eq] at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) (x + (((0 : ℕ) : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) 1 (by omega) (by omega) (by omega); simpa using h
    have hPrev' : Q'' ((t + 2) + dt) ((x + 1) + (((0 : ℕ) : ℤ) + 1)) := by
      push_cast; simpa using hPrev
    have step := Pas_hb P Q' Q'' R'' t x dt 0 hPQQR hP_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = (t + 2) + cote := by omega
    rw [time_eq] at step
    simpa using step

lemma DD_d (t : ℕ) (x : ℤ) (cote : ℕ) (P Q R P' Q' R' P'' Q'' : Local_Prop)
    (hQQPQ : loi Q Q' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'') :
    0 < cote →
    Diag t x (cote + 2) P Q R →
    Diag (t + 1) (x + 1) (cote + 1) P' Q' R' →
    P'' (t + 2) ((x + cote) + 2) →
    Semi_Diag (t + 2) (x + 2) cote P'' Q'' := by
  intro hcote D D' hP''
  refine Rec_SemiDiag (t + 2) (x + 2) cote P'' Q'' hcote ?apex ?top ?step
  case apex =>
    have h := hP''
    have eq : ((x + (cote : ℤ)) + 2) = (x + 2) + cote := by ring
    rw [eq] at h; exact h
  case top =>
    intro dx hdx _
    -- 1 + dx = cote, so dx = cote - 1.
    have hQ_in : Q (t + (0 + 2)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior 2 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (0 + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.interior 1 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hP''_in : P'' ((t + 2) + 0) ((x + 2) + ((dx : ℤ) + 1)) := by
      have h := hP''
      have eq : ((x + (cote : ℤ)) + 2) = (x + 2) + ((dx : ℤ) + 1) := by
        have : cote = dx + 1 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_bb Q Q' P'' Q'' t x 0 dx hQQPQ hQ_in hQ'_in hP''_in
    simpa using step
  case step =>
    intro dt dx hdt hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt + 2) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) ((x + 2) + ((dx : ℤ) + 1)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_bb Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    exact step

lemma Dd_d (t : ℕ) (x : ℤ) (cote : ℕ) (P Q R P' Q' P'' Q'' : Local_Prop)
    (hQQPQ : loi Q Q' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'') :
    0 < cote →
    Diag t x (cote + 2) P Q R →
    Semi_Diag (t + 1) (x + 1) (cote + 1) P' Q' →
    P'' (t + 2) ((x + cote) + 2) →
    Semi_Diag (t + 2) (x + 2) cote P'' Q'' := by
  intro hcote D D' hP''
  refine Rec_SemiDiag (t + 2) (x + 2) cote P'' Q'' hcote ?apex ?top ?step
  case apex =>
    have h := hP''
    have eq : ((x + (cote : ℤ)) + 2) = (x + 2) + cote := by ring
    rw [eq] at h; exact h
  case top =>
    intro dx hdx _
    have hQ_in : Q (t + (0 + 2)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior 2 (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (0 + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.interior 1 (dx + 1) (by omega) (by omega)
      push_cast at h; simpa using h
    have hP''_in : P'' ((t + 2) + 0) ((x + 2) + ((dx : ℤ) + 1)) := by
      have h := hP''
      have eq : ((x + (cote : ℤ)) + 2) = (x + 2) + ((dx : ℤ) + 1) := by
        have : cote = dx + 1 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_bb Q Q' P'' Q'' t x 0 dx hQQPQ hQ_in hQ'_in hP''_in
    simpa using step
  case step =>
    intro dt dx hdt hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt + 2) (dx + 1) (by omega) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) ((x + 2) + ((dx : ℤ) + 1)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_bb Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    exact step

lemma dd_d (t : ℕ) (x : ℤ) (cote : ℕ) (P Q P' Q' P'' Q'' : Local_Prop)
    (hQQPQ : loi Q Q' P'' Q'') (hQQQQ : loi Q Q' Q'' Q'') :
    0 < cote →
    Semi_Diag t x (cote + 2) P Q →
    Semi_Diag (t + 1) (x + 1) (cote + 1) P' Q' →
    P'' (t + 2) ((x + cote) + 2) →
    Semi_Diag (t + 2) (x + 2) cote P'' Q'' := by
  intro hcote D D' hP''
  refine Rec_SemiDiag (t + 2) (x + 2) cote P'' Q'' hcote ?apex ?top ?step
  case apex =>
    have h := hP''
    have eq : ((x + (cote : ℤ)) + 2) = (x + 2) + cote := by ring
    rw [eq] at h; exact h
  case top =>
    intro dx hdx _
    have hQ_in : Q (t + (0 + 2)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior 2 (dx + 1) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (0 + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.interior 1 (dx + 1) (by omega) (by omega)
      push_cast at h; simpa using h
    have hP''_in : P'' ((t + 2) + 0) ((x + 2) + ((dx : ℤ) + 1)) := by
      have h := hP''
      have eq : ((x + (cote : ℤ)) + 2) = (x + 2) + ((dx : ℤ) + 1) := by
        have : cote = dx + 1 := by omega
        rw [this]; push_cast; ring
      rw [eq] at h; simpa using h
    have step := Pas_bb Q Q' P'' Q'' t x 0 dx hQQPQ hQ_in hQ'_in hP''_in
    simpa using step
  case step =>
    intro dt dx hdt hsum hPrev
    have hQ_in : Q (t + (dt + 2)) (x + ((dx : ℤ) + 1)) := by
      have h := D.interior (dt + 2) (dx + 1) (by omega) (by omega)
      push_cast at h; simpa using h
    have hQ'_in : Q' ((t + 1) + (dt + 1)) ((x + 1) + ((dx : ℤ) + 1)) := by
      have h := D'.interior (dt + 1) (dx + 1) (by omega) (by omega)
      push_cast at h; simpa using h
    have hPrev' : Q'' ((t + 2) + dt) ((x + 2) + ((dx : ℤ) + 1)) := by
      push_cast at hPrev; simpa using hPrev
    have step := Pas_bb Q Q' Q'' Q'' t x dt dx hQQQQ hQ_in hQ'_in hPrev'
    have time_eq : (t + 2) + (dt + 1) = t + 2 + dt + 1 := by omega
    rw [time_eq] at step
    exact step

end FsspMazoyer
end CellularAutomatas
