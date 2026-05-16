I now have a thorough understanding of all 14 Coq files plus the Lean target. Producing the report:

---

# Mazoyer/Duprat Coq → Lean 4 Proof Plan
## Formal Analysis & Translation Roadmap

This report analyzes Jean Duprat's 1997 Coq formalization of Jacques Mazoyer's 6-state minimal-time (2n−2) firing-squad solution, located in [external/firing-squad/](external/firing-squad/), and lays out a concrete plan for porting it to Lean 4 against the existing `FsspMazoyerCA.C` and `SolvesFSSPOptimal` predicate.

---

## 1. Reading order and dependency graph

The `Require` directives induce a strict topological order. The 14 source files form an almost-linear pipeline with one fork (vertical/reflection both depend on basic+constr, and trapeze depends on both):

```
bib.v                            # arithmetic + induction principles + Local_Prop
  └── autom.v                    # 6 states, transition table δ, Etat n p, base lemmas
        └── geom.v               # geometric figure predicates + Rec_Diag, Rec_SemiDiag
              └── constr.v       # 22 "Pas_*" / "DDD"/"D'DD"/… lemmas combining figures
                    └── basic.v  # A_basic, B_basic, C_basic + sommet helpers GA_G, GBA_dollarC...
                          ├── reflection.v   # UA, UAB, ZCB, A_ZCB, B_ZCB, C_ZCB, *_Vg, ZCB_Ht1
                          └── bord.v         # un_end..cinq_end + closure lemmas
                                └── double_diag.v  # DD inductive type + DD_hh, DD_hddollar
                                      └── vertical.v    # Ht1_End2/4, Ht1_DD, Ht0_DD, Ht1_VV
                                            └── trapeze.v   # Ha_Vg/Hb_Vg/Hc_Vg, Ha_DD/Hb_DD/Hc_DD, Hg_Hf?
                                                  └── sommet.v    # quatre_Hg, cinq_Hg, DD_Hg, Hg_Hf
                                                        └── final.v   # diagonale → sommet_1 → firing_squad
                                                              └── algo.v   # list-based equivalence (for extraction)
                                                                    └── extract.v # OCaml extraction
```

One-line role for each file:

| File | Role |
|---|---|
| [bib.v](external/firing-squad/bib.v) | Induction skeletons (`Rec2..Rec5'`, `inter`), arithmetic on `un..neuf`, `double`/`triple`/`tiers`, `Omod3`/`Unmod3`/`Deuxmod3`, the `Local_Prop := nat → nat → Prop` abstraction, and the local-rule schemas `loi`/`loi_droite`. |
| [autom.v](external/firing-squad/autom.v) | The 6 states `A B C L G F`, all 16 helper transitions `Transition_*_*`, the assembled `Transition c0 c1 c2`, the global state `Etat : nat → nat → Couleur` with the right phantom `[G,C,L,L,…]` baked into `Etat 0`, basic facts `un_pas`, `demi_pas`, `G00`, `G0N`, `C0N1`, `base_L`, `basedollar_L`. The parameter `N` and axiom `necessaire : 2 < N`. |
| [geom.v](external/firing-squad/geom.v) | Inductive geometric predicates `Horizontale`, `Horizontale_t0`, `Horizontale_t1`, `Verticale`, `Triangle_inf`, `Diag`, `Diag'`, `Semi_Diag`, plus their constructors/eliminators `Rec_Diag`, `Rec_Diag'`, `Rec_SemiDiag`, `inter`, `deux_Diag`, `rec_triangle_inf`, `inclus_vert`, `vv_vert`, `rec_vert`, `vert_un/deux/trois`, `hh_hor`, `hor_un/deux/trois/quatre`. The geometric-language layer. |
| [constr.v](external/firing-squad/constr.v) | "Construction calculus": elementary `Pas_hh`, `Pas_hd`, `Pas_dh`, `Pas_hddollar`, `Pas_dhdollar`, `Pas_hb`, `Pas_bb` and the half-step variants `demi_Pas_h`, `demi_Pas_ddollar`. From them are built the *combinators* `DDD`, `D'DD`, `D'DD'`, `DD'D`, `DD_D'`, `D_D'D`, `DD_Ddollar`, `D_DDdollar`, `DD_D`, `D'D_D`, `D_DD`, `DDdollar_D`, `DD_d`, `Dd_d`, `dd_d`. Each takes two/three diagonals at consecutive times and produces a new diagonal/semi-diagonal one step later. The "calculus of diagonal superpositions". |
| [basic.v](external/firing-squad/basic.v) | The three "basic bricks" `A_basic`, `B_basic`, `C_basic` (each is a pair of consecutive `Diag`/`Diag'` figures of `L`/`*-Etat`/`L`); brick succession lemmas `A_A`, `B_B`, `C_C` (vertical reuse), `A_B`, `C_A`, `B_C` (rotation: a brick of side `cote` becomes a brick of the next type either reused or extended by one column). Plus the apex helpers `GA_G`, `GB_G`, `GC_G`, `GA_dollarC`, `GBA_dollarC`, `GBG_dollarG`, `GBC_dollarB`, `GC_dollarB`. |
| [reflection.v](external/firing-squad/reflection.v) | The "reflected" / above-the-brick wedges `UA`, `UAB`, `ZCB` (apex region surrounded by `G` instead of `L`); `B_UA`, `C_UAB`, `A_ZCB`, `B_ZCB`, `C_ZCB` deduce these from the bricks plus rightward `G` columns. Then `ZCB_GLC`, `ZCB_l`, `ZCB_ll`, `ZCB_lll`, `ZCB_Ht1` (the central translation: a `ZCB` triangle plus a vertical `G`-wall yields an `Horizontale_t1` `G:C:L^*` row), and the verticals `A_Vg`, `B_Vg`, `C_Vg`. |
| [bord.v](external/firing-squad/bord.v) | The left-edge inductive families `un_end`, `deux_end`, `trois_end`, `quatre_end`, `cinq_end` describing the `G`/`C`/`B`/`A`/`L` staircase that lives on column 0 due to the half-step rule `Etat (S t) 0 = Transition L (Etat t 0) (Etat t 1)`. Closure: `un_GG`..`cinq_GG` (extracts the two consecutive `G`s at column 0), the propagators `un_deux`, `deux_trois`, `deux_quatre`, `trois_quatre`, `trois_cinq`, `quatre_quatre`, `cinq_cinq`, `quatre_cinq`, and the key `cinq_quatre` (a `cinq_end` plus two `L`s yields a `C_basic` brick of side 2 plus a continuing `quatre_end`). |
| [double_diag.v](external/firing-squad/double_diag.v) | The recursive predicate `DD t x cote` (the central proof object): "from corner `(t,x)` opens a self-similar wedge of side `cote`". Five constructors `DD_4`, `DD_5`, `DD_A`, `DD_B`, `DD_C`. The base cases `DD_4`/`DD_5` are `quatre_end`/`cinq_end`; the recursive constructors say `DD t x cote` holds iff there is an `A_basic`/`B_basic`/`C_basic` brick of side `tiers(cote)+1` at the appropriate offset, on top of which sits another `DD` of strictly smaller side `pred(2·tiers(cote))` / `2·tiers(cote)` / `1+2·tiers(cote)`. `DD_GG` extracts `G` at `(t+cote, x)` and `(t+cote+1, x)`. `DD_hh` and `DD_hddollar` are the "vertical reuse" and "extension by one" closure lemmas. |
| [vertical.v](external/firing-squad/vertical.v) | Bridge from horizontal rows to `DD`. `Hor_tr_inf`: a horizontal row of `L` extends downward as a triangle of `L`s (because `δ L L L = L`). `Ht1_End2`/`Ht1_End4`: a `G:C:L^*` row is the apex of a `deux_end`/`quatre_end`. `Ht1_DD`: the central recursion entry — a `Horizontale_t1` row of length ≥ 1 generates a `DD` of side `S(S(S dx))` for each `dx`. `Ht1_VV`: such a row also generates a `Verticale` of `G`s of height `S(2·cote)`. `Ht0_DD`/`Ht0_DDf`: same for the *initial* base row at time 0 (where the "general" of size 0 is at column 0). |
| [trapeze.v](external/firing-squad/trapeze.v) | The "trapezoid" lemmas: given a brick `A/B/C_basic` and a vertical wall of `G`s of length `triple(cote)` to its right, we can deduce both a *new* vertical wall on the left (`Ha_Vg`/`Hb_Vg`/`Hc_Vg`) and a *new* `DD` below (`Ha_DD`/`Hb_DD`/`Hc_DD`). The bottom row helpers `Ha3_Hg`/`Hb3_Hg`/`Hc3_Hg` handle the smallest cases with `H2_Hg`. Also `R5` (the case-split `un = n ∨ un < n`) and the closed forms `R1`/`R1'`/`R2`/`R3` for `tiers/double/pred(double)`. |
| [sommet.v](external/firing-squad/sommet.v) | The "apex" theorem `DD_Hg`: given `DD t x cote` and a vertical wall of `G`s on the right of height `cote`, the row at time `S(t+cote)` is fully `G` of length `cote`. Proven by strong induction on `cote` using the `recur2` principle. Base cases `quatre_Hg`/`cinq_Hg` discharge `cote = 3` and `cote = 4`. The recursive cases call `Ha_Vg`/`Ha_DD` (and B/C analogues) from `trapeze.v`. Finally `Hg_Hf` lifts a horizontal `G`-row plus a `G` to its right by one step into a horizontal `F`-row. |
| [final.v](external/firing-squad/final.v) | Glue. `N_un/deux/trois`: rewrites `N = S(pred N)` etc. (since `2 < N`). `base1` = the initial bottom row `G:L^(N-1)` is `Horizontale_t0`. `diagonale` = `DD (N-2) 0 N` via `Ht0_DDf` on `base1`. `base2` = the right-phantom row `G:C:L^(N-1)` is `Horizontale_t1`. `vert_droite` = the right column `S N` stays `G` for `2N - 1` steps via `Ht1_VV`. `GN1` extracts `G` at `(2N-1, S N)`. `sommet_1` = row `2N-1` is all `G` via `DD_Hg(diagonale, vert_droite)`. `firing_squad` = row `2N` is all `F` via `Hg_Hf(sommet_1, GN1)`. |
| [algo.v](external/firing-squad/algo.v) | A list-encoded simulation `nth_line : nat → list Couleur` proven equivalent to `Etat` via `nth_nth_line_is_etat`, then `nth_line_2N_is_fire` repackages `firing_squad`. Provides an executable program. *Not on the correctness path*; only needed if you also want extracted/efficient evaluation. |
| [extract.v](external/firing-squad/extract.v) | OCaml extraction directives. *Not on the correctness path*. |

---

## 2. The geometric figure predicates ([geom.v](external/firing-squad/geom.v))

All 8 predicates have type `nat → nat → nat → … → Local_Prop → Prop`, where the first two `nat` arguments are time `t` and column `x`. They are inductive *one-constructor* records — each just packages a quantified pointwise statement about the global `Etat`.

| Predicate | Definition site | Region of space-time covered | Use in proofs |
|---|---|---|---|
| **`Horizontale t x long P`** | [geom.v#L43](external/firing-squad/geom.v#L43) | Single time row: `{ (t, x+dx) : 0 ≤ dx ≤ long }` (length `long+1`). | Universal output shape. The final theorem `firing_squad` is itself a `Horizontale (2N) 0 N F_Etat`. Used both as a hypothesis (an all-`L` initial row) and as a conclusion (an all-`G` row, an all-`F` row). |
| **`Horizontale_t0 t x long P0 P`** | [geom.v#L47](external/firing-squad/geom.v#L47) | Single row with a *distinguished leftmost cell*: `(t, x)` satisfies `P0`, while `(t, x+1) … (t, x+long+1)` satisfy `P`. | Models the t=0 row of the original problem: `(0, 0)` is `G` (`P0`), the rest is `L` (`P`). |
| **`Horizontale_t1 t x long P0 P1 P`** | [geom.v#L51](external/firing-squad/geom.v#L51) | Single row with a *distinguished leftmost cell and second-from-left*: `(t, x)` satisfies `P0`, `(t, x+1)` satisfies `P1`, the rest satisfies `P`. | Models any row of the form `G C L L … L`. This is the *recursion seed*: every interior synchronization sub-problem reduces to such a row. The right-phantom row `(0, S N) = G C L L …` is `Horizontale_t1` ([final.v#L91 base2](external/firing-squad/final.v)). |
| **`Verticale t x haut P`** | [geom.v#L57](external/firing-squad/geom.v#L57) | Single column: `{ (t+dt, x) : 0 ≤ dt ≤ haut }` (height `haut+1`). | All "wall of G" hypotheses. `vert_droite` is a `Verticale 1 (S N) (pred(double N)) G_Etat`. The trapezoid lemmas all consume a vertical `G`-wall on the right and produce one on the left. |
| **`Triangle_inf t x cote P`** | [geom.v#L61](external/firing-squad/geom.v#L61) | Lower-right triangle: `{ (t+dt, x+dx) : 0 ≤ dx ≤ cote, 0 ≤ dt ≤ dx }`. | Used once: `Hor_tr_inf` says an all-`L` row generates an all-`L` triangle below (because `δ L L L = L`). Implicitly used in `Ht0_bissect`/`Ht1_bissect` to know the "interior" of the `L^*` part stays `L` long enough for the recursive sub-diagram to fit. |
| **`Diag t x cote P Q R`** | [geom.v#L66](external/firing-squad/geom.v#L66) | Right-isoceles triangle of side `cote`, hypotenuse from `(t, x+cote)` to `(t+cote, x)`: top-right vertex `P`, interior strictly between the two slanted edges `Q`, bottom-left vertex `R`. Requires `1 < cote`. | The *foundational shape* of the proof. Every brick `A/B/C_basic` is a pair of `Diag`s. `DDD` etc. compose two `Diag`s (at times `t`, `t+1`) into one new `Diag` (at time `t+2`). |
| **`Diag' t x cote P Q' Q R`** | [geom.v#L73](external/firing-squad/geom.v#L73) | Same as `Diag` but with the *first interior row* (at time `t+1`) potentially carrying a different predicate `Q'`. Requires `2 < cote`. | Used only by `B_basic`: the row immediately under the `L:G:B:…` apex carries `G` (not `B`), and `Diag'` lets `Q' = G_Etat` while keeping `Q = B_Etat` for the rest. |
| **`Semi_Diag t x cote P Q`** | [geom.v#L81](external/firing-squad/geom.v#L81) | Triangle without the bottom-left vertex: `P` at `(t, x+cote)`, `Q` everywhere strictly inside / on the slanted edge but not at `(t+cote, x)`. | Used inside `ZCB_l/ll/lll` to peel off `L`-strips from a `ZCB` triangle row by row. |

The **principles** in `geom.v`:
- `Rec_Diag` ([geom.v#L116](external/firing-squad/geom.v#L116)): builds a `Diag` from four "step" obligations (top-row pas, generic interior pas, ground-row pas, vertex pas). This is *the* recursion engine for diagonals.
- `Rec_Diag'` ([geom.v#L141](external/firing-squad/geom.v#L141)): same for `Diag'`.
- `Rec_SemiDiag` ([geom.v#L177](external/firing-squad/geom.v#L177)): same for `Semi_Diag`.
- `inter` ([geom.v#L97](external/firing-squad/geom.v#L97)): a 2D induction principle on `(dt, dx)` for filling a region.
- `rec_triangle_inf` ([geom.v#L210](external/firing-squad/geom.v#L210)): horizontal `L`-row + closure-under-`δ` ⇒ triangle.
- `inclus_vert`, `vv_vert`, `rec_vert`, `vert_un/deux/trois`, `hh_hor`, `hor_un/deux/trois/quatre`: trivial constructors and concatenation lemmas.

---

## 3. Induction principles ([bib.v#L96-L143](external/firing-squad/bib.v))

All `Rec*` are 2- to 6-place chained `intuition`-style implications. They are *modus-ponens skeletons* used to discharge a multi-conclusion goal in a single tactic block. They do not implement induction in the mathematical sense — they linearize the proof obligations:

```
Rec2 : (A → B → C) → A → (A → B) → C.
Rec3 : (A → B → C → D) → A → B → (B → C) → D.
Rec3' : (A → B → C → D) → A → (A → B) → (A → B → C) → D.
Rec4 / Rec4' / Rec4'' : 4-input variants.
Rec5  : (A → B → C → D → E → F) → A → B → (B → C) → (C → D) → (D → E) → F.
Rec5' : variant with two parallel chains.
```

**Where they are used:**

- `Rec3`/`Rec3'` *everywhere* in `basic.v` and `bord.v` to build the multi-field constructors of `A_basic`, `B_basic`, `C_basic`, `deux_end`, `trois_end` etc. by stating "first prove the first field, then the second uses the first, then the third uses the second…". For example [basic.v#L82](external/firing-squad/basic.v) uses `Rec3 _ _ _ _ (make_A_basic …)`.
- `Rec4` for `DD_A`/`DD_B`/`DD_C` (4 obligations: `*basic*` at top, `DD` at bottom, side-arithmetic constraints) — see [double_diag.v#L106-L150](external/firing-squad/double_diag.v).
- `Rec5'` for the 5-field `cinq_end` constructor in [bord.v#L175-L195](external/firing-squad/bord.v).
- `inter` ([geom.v#L97](external/firing-squad/geom.v#L97)) is the only true 2-D induction; it underlies `Rec_Diag` / `Rec_Diag'` by filling the "interior" of a triangle from its boundary.
- `Rec_Diag`/`Rec_Diag'`/`Rec_SemiDiag` are *combinators* on `Diag`/`Diag'`/`Semi_Diag` as inductive predicates: they build a new figure by giving the four boundary updates.
- `recur2` ([bib.v#L88](external/firing-squad/bib.v)) is strong induction on `nat`. Used in [sommet.v#L266 DD_Hg](external/firing-squad/sommet.v) — the only place strong induction (rather than structural induction on `DD`) is used.
- `recur_nSn` ([bib.v#L78](external/firing-squad/bib.v)) is double-step induction (prove `P n`, `P(n+1)`, then `P p ∧ P(p+1) → P(p+2)`). Used in [reflection.v#L367 ZCB_lll](external/firing-squad/reflection.v) for the row-by-row peeling of L-strips.

In Lean 4 these are mostly trivial (`fun a b => f a b a` etc.) and Lean's `obtain ⟨…⟩` / `refine ⟨…, ?_, ?_⟩` syntax already supports them natively. The only ones to *actually replicate* are `Rec_Diag`, `Rec_Diag'`, `Rec_SemiDiag`, `inter`, `recur2` — these are mathematically substantive.

---

## 4. The basic bricks `A_basic` / `B_basic` / `C_basic` ([basic.v#L51-L65](external/firing-squad/basic.v))

```
Inductive A_basic (t x cote : nat) : Prop :=
  make_A_basic : 2 < cote
    → Diag t     x cote L_Etat A_Etat L_Etat
    → Diag (S t) x cote L_Etat A_Etat L_Etat
    → A_basic t x cote.

Inductive B_basic (t x cote : nat) : Prop :=
  make_B_basic : 2 < cote
    → Diag' t     x cote L_Etat G_Etat B_Etat L_Etat   -- top row G, rest B
    → Diag  (S t) x cote L_Etat        B_Etat L_Etat
    → B_basic t x cote.

Inductive C_basic (t x cote : nat) : Prop :=
  make_C_basic : 1 < cote
    → Diag t     x cote L_Etat C_Etat L_Etat
    → Diag (S t) x cote L_Etat C_Etat L_Etat
    → C_basic t x cote.
```

**Geometric meaning.** A "basic brick" is a *pair of consecutive diagonals* of the same shape, both with the same vertex at `(t, x+cote)`/`(t+1, x+cote)` and the same bottom-left vertex `(t+cote, x)`/`(t+cote+1, x)`. The interior is filled with `A_Etat` (resp. `B_Etat`, `C_Etat`); the diagonal "edges" are `L_Etat`. The two-row thickness exists precisely so that the brick has its own *vertical* structure that matches the propagation of `δ`'s 3-cell stencil.

A brick of type `?` of side `cote` looks like (drawn in the (t, x) plane, time growing downward, x growing right; let `c = cote`):

```
         ↓ x = x+c   t
    L .  .    .   .  L      time t
    L L  .    .   L  L      time t+1
    . L L     . L L .       …
              ?
              .
              .   c rows
              ?
    . L L L L L .            time t+c-1
       L L L                 time t+c
        L                    time t+c+1
```

(For `B_basic` the very top *single-cell* row is `G` rather than `B`, encoded by `Diag'`.)

**How they feed into each other** (([basic.v construction2 section, L70-L260](external/firing-squad/basic.v))):

Vertical reuse — same brick, two time steps later:

| Lemma | Statement |
|---|---|
| `A_A` | `A_basic t x c` + two `L`s at `(t+2, x+c)`, `(t+3, x+c)` ⇒ `A_basic (t+2) x c`. |
| `B_B` | analogue for `B`. |
| `C_C` | analogue for `C`. |

Type-rotation — a brick of one type plus extension data turns into the *next* type, possibly with side increased by one:

| Lemma | Effect |
|---|---|
| `A_B` | `A_basic t x c` + 2 `L`s right ⇒ `B_basic (t+1) (x+1) c` (same side, shifted right). |
| `B_C` | `B_basic t x c` + 2 `L`s right ⇒ `C_basic (t+1) (x+1) c` (same side, shifted right). |
| `C_A` | `C_basic t x c` + 2 `L`s right ⇒ `A_basic (t+1) x (S c)` (**side grows by 1**, anchor unchanged). |

So the cycle `C → A → B → C` increases the side by 1 every three steps. The side-growing edge (`C_A`) is the *only* one that adds a column; this is what makes the geometry self-similar at scale 1/3.

The brick lemmas all reduce to *single-step* applications of `δ` via the elementary `Pas_*` lemmas ([constr.v#L46-L130](external/firing-squad/constr.v)) wrapped by the `DDD`/`D'DD'`/`DD_D'`/etc. *combinators* ([constr.v#L150-L685](external/firing-squad/constr.v)). Each `unfold loi, X_Etat, Y_Etat; intros; simpl; rewrite … ` block at the leaves does *case analysis on the local rule* — these are the only places where the actual transition table is touched.

The "apex/vertex" lemmas at the end of [basic.v#L301-L388](external/firing-squad/basic.v) — `GA_G`, `GB_G`, `GC_G`, `GA_dollarC`, `GBA_dollarC`, `GBG_dollarG`, `GBC_dollarB`, `GC_dollarB` — are also direct local-rule case checks. They say things like "if `(t, x) = G` and `(t, x+1) = A` then `(t+1, x) = G`". These are the only `δ`-evaluations needed *outside* of the bricks.

---

## 5. Border reasoning ([bord.v](external/firing-squad/bord.v))

The "left edge" of the squad has the asymmetry that cell 0 has no left neighbour, so the rule used at column 0 is `Etat (S t) 0 = δ L (Etat t 0) (Etat t 1)` ([autom.v#L431](external/firing-squad/autom.v)). This means the column-0 trace cannot be analyzed with the brick combinators (which are 3-input). Duprat's solution is the **staircase predicates** `un_end…cinq_end`, each capturing a fixed multi-row, multi-column pattern of states *along the left edge*.

The five families are:

```
un_end   t x ::=  G_Etat t x       ∧ G_Etat (t+1) x
deux_end t x ::=  C_Etat t (x+1)   ∧ B_Etat (t+1) (x+1) ∧ un_end (t+1) x
trois_end t x ::=  A_Etat t (x+2)  ∧ G_Etat (t+1) (x+2) ∧ deux_end (t+1) x
quatre_end t x ::=  L_Etat t (x+3) ∧ L_Etat (t+1) (x+3) ∧ trois_end (t+1) x
cinq_end t x ::=  L_Etat t (x+4)   ∧ L_Etat (t+1) (x+4)
                ∧ G_Etat (t+1) (x+3) ∧ B_Etat (t+2) (x+3) ∧ trois_end (t+2) x
```

So each level *adds one more diagonal column* on top of the previous staircase. Geometrically (column index horizontal, time downward, `x = 0` for definiteness):

```
cinq_end :     col 0   col 1   col 2   col 3   col 4
       t:                                      L
       t+1:                            G        L     ← cinq_end body
       t+2:                            B
                   ┌─ trois_end (t+2) 0 ─────────┐
       t+2:                    A                
       t+3:                    G                       
                   ┌─ deux_end (t+3) 0 ──────┐         
       t+3:           C                     
       t+4:           B                              
                   ┌─ un_end (t+4) 0 ──┐                  
       t+4:    G                                          
       t+5:    G                                       
```

**The asymmetry handled.** Each predicate carries enough information to tell the column-0 step rule (which uses the phantom `L`) what state to produce next. Concretely:

- `un_end → G` at column 0 is preserved by *any* surrounding states because of `δ L G _ = G` and `δ L G G = G` and `δ L G C = G` etc., as long as the right neighbour is one of `A`/`B`/`C`/`G`. The `un_GG` lemma extracts the two-step `G`-stability in column 0.
- `deux_end` records the single step `G:C → G:B` which is what `δ` does at the boundary when the right neighbour is `C`. Closed by `un_deux`.
- `trois_end` records the three-step `A → G → G` propagation in column 2 (one diagonal step away from the edge), required for the next staircase.
- `quatre_end` adds an `L:L` pair in column 3 (this is just the still-quiet zone past the front).
- `cinq_end` includes the *next* general spawning at `(t+1, x+3) = G` and the brick start `(t+2, x+3) = B`. This is the moment a new sub-synchronization begins.

**Closure lemmas.** `quatre_quatre` and `cinq_cinq` preserve the staircase under "two more `L`s in the trailing column"; `quatre_cinq` lifts to the next level when the leading column ends; `cinq_quatre` ([bord.v#L228-L271](external/firing-squad/bord.v)) is the *key recursion-driver*: a `cinq_end` plus two trailing `L`s produces a `C_basic (t+1) (x+3) 2` brick AND a `quatre_end (t+3) x`. This is exactly the inductive case `DD_C` of the `DD` predicate at the smallest scale.

In our Lean encoding with the explicit `Border` state, *the asymmetry disappears at the level of `δ`* — every cell uses the same 3-input rule. But the *content* of the staircase predicates remains identical because [`δ Border c1 c2 = MazoyerDelta L c1 c2`](CellularAutomatas/proofs/constructions/fssp_mazoyer_ca.lean#L177) by construction. So in Lean we will define `un_end`..`cinq_end` over the `Couleur` alphabet identically and reuse the same closure lemmas.

---

## 6. Roles of [double_diag.v](external/firing-squad/double_diag.v), [trapeze.v](external/firing-squad/trapeze.v), [vertical.v](external/firing-squad/vertical.v), [sommet.v](external/firing-squad/sommet.v)

These four files implement the proof's **central recursion**.

### `double_diag.v` — the recursive type `DD`

`DD t x cote` ([double_diag.v#L48-L72](external/firing-squad/double_diag.v)) is the proof's *backbone* inductive type. It says: at corner `(t, x)`, an entire wedge of side `cote` performs synchronization "correctly" — meaning that `(t+cote, x)` and `(t+cote+1, x)` are both `G` (`DD_GG`), AND the wedge is built recursively from a basic `A`/`B`/`C` brick on top of a smaller `DD`. The constructors:

```
DD_4 : quatre_end t x → DD t x 3
DD_5 : cinq_end   t x → DD t x 4
DD_A : 6 ≤ cote → cote ≡ 0 (mod 3) →
       A_basic t (x + pred(2 · tiers cote)) (S (tiers cote)) →
       DD (t + S (tiers cote)) x (pred(2 · tiers cote))    →   DD t x cote
DD_B : 7 ≤ cote → cote ≡ 1 (mod 3) →
       B_basic t (x + 2 · tiers cote) (S (tiers cote)) →
       DD (t + S (tiers cote)) x (2 · tiers cote)          →   DD t x cote
DD_C : 5 ≤ cote → cote ≡ 2 (mod 3) →
       C_basic t (x + S (2 · tiers cote)) (S (tiers cote)) →
       DD (t + S (tiers cote)) x (S (2 · tiers cote))      →   DD t x cote
```

In picture: the side-`cote` wedge has a brick of side `tiers cote + 1` sitting at the *upper right*, and a smaller `DD` of side roughly `2/3 · cote` sitting *below* it. `DD_hh` handles vertical extension (two L's on the right preserves `DD`); `DD_hddollar` handles diagonal extension (side grows by 1 with two L's on the right).

### `vertical.v` — DD bridges from a `Horizontale_t1` row

A `Horizontale_t1 t x cote G_Etat C_Etat L_Etat` row is exactly the input to a sub-synchronization (general at `x`, `C` to its right, then quiet `L`s for `cote` more cells). `Ht1_DD` ([vertical.v#L122](external/firing-squad/vertical.v)) says: such a row generates `DD (t+dx) x (S(S(S dx)))` for each `1 ≤ dx ≤ cote`. The base case `Ht1_End4` produces `quatre_end` (= `DD t x 3`), and the inductive case is `DD_hddollar` driven by the row's `L`-trail (provided by `Hor_tr_inf`).

`Ht1_VV` ([vertical.v#L138](external/firing-squad/vertical.v)) says the same row generates a vertical column of `G`s of height `S(2·cote)` directly under its first cell. This is the wall used as the "right phantom" for sub-synchronizations.

`Ht0_DD`/`Ht0_DDf` are the analogue for the *initial* row (with `Horizontale_t0`, no `C` after the general, just `G:L^*`) — which is the situation at `t=0` with the top general; by one step the row at `t=1` becomes `G:C:L^*` so it transitions through a quiet-row analysis ([vertical.v#L196 Ht0_End2/4](external/firing-squad/vertical.v)) to reach the same `DD` form.

### `trapeze.v` — A/B/C trapezoids

This file is the *induction step*. Given a brick of type `?` of side `S c`, plus a vertical wall of `G`s on its right of height `triple c` (or `S(triple c)`/`S(S(triple c))` for B/C), it produces:

1. A *new vertical wall on the left* (`Ha_Vg`/`Hb_Vg`/`Hc_Vg`) — this is what allows the recursion to start the next sub-step.
2. A *new `DD` underneath* (`Ha_DD`/`Hb_DD`/`Hc_DD`) — this is the smaller wedge created by the brick.

The proofs go via the `ZCB_*` machinery from `reflection.v`: `A_basic + G-wall = ZCB`, then `ZCB + G-wall = Horizontale_t1` (via `ZCB_Ht1`), then `Horizontale_t1 → Verticale` (via `Ht1_VV`) and `→ DD` (via `Ht1_DD`). The vertical-wall arithmetic is the most painful part: making sure the ranges line up for `inclus_vert`.

The smallest-side cases (`Ha3_Hg`, `Hb3_Hg`, `Hc3_Hg`, `Hc2_Hg`, `Hc2_Vg`) are handled by direct `δ`-computation rather than the general construction — the cases `cote = 3, 4, 5` are exactly `DD_4`, `DD_5`, `DD_C cote=5` respectively.

### `sommet.v` — the apex theorem `DD_Hg`

`DD_Hg t x cote : DD t x cote → Verticale (t+1) (x+cote+1) cote G_Etat → Horizontale (t+cote+1) x cote G_Etat` ([sommet.v#L266](external/firing-squad/sommet.v)).

This is *the theorem*: a side-`cote` `DD` wedge plus a `G`-wall on its right produces a fully `G` row at the bottom of the wedge. Proven by **strong induction on `cote`** via `recur2`.

- Base cases `cote = 3` (`DD_4`) and `cote = 4` (`DD_5`) are direct local-rule chains: `quatre_Hg` ([sommet.v#L66](external/firing-squad/sommet.v)) and `cinq_Hg` ([sommet.v#L161](external/firing-squad/sommet.v)).
- Inductive step (one of `DD_A`/`DD_B`/`DD_C`): use `Ha_Vg`/`Hb_Vg`/`Hc_Vg` to get a new G-wall on the left of the brick, then call the I.H. on the smaller `DD` underneath, then concatenate the two rows via `hh_hor`.

`Hg_Hf` ([sommet.v#L394](external/firing-squad/sommet.v)) is the *only place where `F` appears*: a horizontal `G`-row of length `long+1` plus a `G` at the far right yields a horizontal `F`-row of length `long+1` one step later — because `δ G G G = F`, `δ G G _ = G` for non-`G` middles, and `δ x G y` evaluates to `F` when `x = y = G`. Wait, actually inspecting [autom.v#L313-L324 Transition_G](external/firing-squad/autom.v) carefully: when the *middle* cell is `G`, the result depends on the right neighbor:
- `δ _ G A/B/C/F = G` (stays `G`)
- `δ c0 G L = TG_L c0` (which is `B`/`A` depending on left)
- `δ c0 G G = TG_G c0` (the firing trigger: `δ G G G = F`, `δ A G G = F`, `δ L G G = F`).

So `Hg_Hf` works because every cell has at least one `G` neighbour, and at column 0 the phantom `L` causes the rule `δ L G G = F`, while everywhere else `δ G G G = F`.

---

## 7. Structure of `final.v`: how everything composes

[final.v](external/firing-squad/final.v) glues all of the above into the final theorem. The chain has **5 named lemmas**:

```
diagonale  : DD (N − 2) 0 N
              ↑ from base1 : Horizontale_t0 0 0 (N−1) G_Etat L_Etat
              via Ht0_DDf

vert_droite : Verticale 1 (N+1) (2N − 1) G_Etat
              ↑ from base2 : Horizontale_t1 0 (N+1) (N−1) G_Etat C_Etat L_Etat
              via Ht1_VV
              [base2 is the "right phantom row" baked into Etat 0 by autom.v]

GN1        : G_Etat (2N−1) (N+1)              -- corollary of vert_droite at top
sommet_1   : Horizontale (2N − 1) 0 N G_Etat
              ↑ from diagonale + vert_droite  via DD_Hg

firing_squad : Horizontale (2N) 0 N F_Etat
              ↑ from sommet_1 + GN1           via Hg_Hf
```

Each transition is justified by exactly one theorem from the upstream pipeline. The arithmetic (`N_un`, `N_deux`, `N_trois`, `R1`) just shuffles `N = S(pred N) = S(S(pred(pred N)))` etc. so that side arguments line up — these become trivial in Lean if `n ≥ 4` is encoded as `n = m + 4` (an existence on `m`).

Big picture in space-time (with `n = N+1` cells = positions `0..N`, time growing downward):

```
                                       x = 0       x = N    x = N+1 (phantom)
              t = 0          G L L L L L L L L     L         G       (← base1 ⊕ base2)
                              \                           /
                  diagonale     \   ← DD wedge of side N /  vert_droite (G column)
                  (DD (N-2) 0 N) \                      /
                                  \                    /
              t = 2N-1            G G G G G G G G G    G    G         (← sommet_1)
              t = 2N              F F F F F F F F F    F    G         (← firing_squad)
                                  ←——— answer ————→
```

The *self-similarity* is internal to the wedge: each `DD` of side `c` contains, by recursion, a brick of side `tiers c + 1` and a sub-`DD` of side `~2c/3`, until the bottom-most level `DD_4`/`DD_5`/`DD_C(5)` triggers `quatre_end`/`cinq_end`. The first general at the bottom-left appears at time `2N − 1` because the recursion adds `cote/(cote in next iteration) ≈ 3/2` time per side reduction, and the geometric series bounds give exactly `cote` time steps for a side-`cote` wedge.

---

## 8. Recursion shape and time bound

**Self-similar split.** At each recursive step in `DD`, side `c` decomposes as

| `c mod 3` | Brick type | Brick side | Time advance | Sub-side |
|---|---|---|---|---|
| 0 | `A` | `tiers c + 1` | `tiers c + 1` | `pred(2 · tiers c) = 2c/3 − 1` |
| 1 | `B` | `tiers c + 1` | `tiers c + 1` | `2 · tiers c` |
| 2 | `C` | `tiers c + 1` | `tiers c + 1` | `2 · tiers c + 1` |

where `tiers c = ⌊c/3⌋`. In every case the sub-side is roughly `2c/3` and the time advance is roughly `c/3`. So one full recursion step kills *one third* of the side and pays *one third* of the side in time — and after a logarithmic number of recursions we reach the base case `c = 3` or `c = 4`.

But the **total time** is not logarithmic. It is precisely `cote`. The reason: at the *bottom* of each recursion level, the sub-`DD` produces a `G` at `(t' + sub_cote, x)` (by `DD_GG`), and this `G` is exactly the first `G` of the bottom row of the parent wedge. So the parent wedge produces `G` at column `x` at time `t + (tiers c + 1) + (sub_cote)`, which we want to equal `t + c`. Checking case 0:
$$ (\,t + (\mathrm{tiers}\,c + 1)\,) + (2 \cdot \mathrm{tiers}\,c - 1) = t + 3 \cdot \mathrm{tiers}\,c = t + c. $$
Cases 1 and 2 are similar. So `DD_GG` ([double_diag.v#L75](external/firing-squad/double_diag.v)) propagates exactly the right time-bound through the recursion.

**Where does the midpoint general first appear?** The diagonal `DD (N − 2) 0 N` contains, at its first recursion level, a brick at `(N − 2, x_brick)` of side `tiers N + 1`. That brick's *upper right vertex* is at `x = x_brick + tiers N + 1 ≈ N − 2 N/3 ≈ N/3` (cases 0, 1, 2). So the first sub-general appears about a third of the way down the array. Then *its* sub-recursion places another sub-general at about `(1/3 + 2/9) N = 5N/9` from the left, etc. After log_{3/2} N steps the sub-generals tile the array densely enough that every cell has a sub-general within distance 1 — and *then* the base cases `DD_4` / `DD_5` produce the local firing.

In particular: the *very first* midpoint general appears at time `N − 2 + tiers N + 1` (the bottom of the topmost brick) at position `0`. This is the first vertical `G` that begins the sub-synchronization on the left. (Mazoyer's original construction calls these "dividing signals".)

**Time bound.** The diagonal extends from `t = N − 2` to `t = N − 2 + N = 2N − 2`. Adding the one extra step from `Hg_Hf` (`G`-row → `F`-row) gives exactly `2N − 1` for the all-`G` row and `2N` for the all-`F` row — but `2N` in Coq's `N+1`-cell convention is `2(n−1) = 2n − 2` in our `n`-cell convention.

---

## 9. Lean 4 proof plan

We work in namespace `CellularAutomatas.FsspMazoyerCA`. The CA is the existing `C : LCellAutomaton Bool` (= `CellAutomaton Bool？ Bool`) defined in [CellularAutomatas/proofs/constructions/fssp_mazoyer_ca.lean#L185](CellularAutomatas/proofs/constructions/fssp_mazoyer_ca.lean). We use the `Couleur` alphabet (with extra `Border`) defined in the same file.

Throughout, `t : ℕ`, `x : ℤ`. We use `ℤ` for column index because the framework uses `ℤ`-indexed configurations. (See §10 for the indexing translation.) Where Coq writes `Etat t x`, we will write `cell n t x := C.nextt (⟬fssp_left_side n⟭) t x` (with `n` the squad size).

The plan is divided into 7 layers, mirroring the Coq dependency graph but compressed where Lean's tactic library obviates Coq's bookkeeping.

### Layer 0 — Local-rule case-analysis core (S each, ~15 lemmas)

These are the *only* lemmas that ever look inside the transition table. Everything above them is structural.

```lean
lemma Couleur.delta_LLL : C.δ.compute Border L L = L            -- (S, native_decide)
lemma Couleur.delta_LLA : C.δ.compute L L A = L
…  -- ~30 such lemmas covering every brick edge and apex case
```

In practice these will be *one* big `decide`/`native_decide` lookup table, plus a handful of named lemmas like `delta_GAG` (vertical G-wall preservation). **S each. ~30 lemmas total. Probably bundled as one big lemma `delta_table`.**

### Layer 1 — `Local_Prop`, geometric figures, induction principles (M, ~12 lemmas)

```lean
abbrev Spacetime  := ℕ → ℤ → Prop     -- analogue of Local_Prop

structure Horizontale (t : ℕ) (x : ℤ) (long : ℕ) (P : Spacetime) : Prop where
  pointwise : ∀ dx : ℕ, dx ≤ long → P t (x + dx)

structure Horizontale_t0 (t : ℕ) (x : ℤ) (long : ℕ) (P0 P : Spacetime) : Prop where
  head : P0 t x
  tail : Horizontale t (x + 1) long P

structure Horizontale_t1 (t : ℕ) (x : ℤ) (long : ℕ) (P0 P1 P : Spacetime) : Prop where
  head  : P0 t x
  next1 : P1 t (x + 1)
  tail  : Horizontale t (x + 2) long P

structure Verticale (t : ℕ) (x : ℤ) (haut : ℕ) (P : Spacetime) : Prop where
  pointwise : ∀ dt : ℕ, dt ≤ haut → P (t + dt) x

structure Triangle_inf (t : ℕ) (x : ℤ) (cote : ℕ) (P : Spacetime) : Prop where
  pointwise : ∀ dt dx : ℕ, dx ≤ cote → dt ≤ dx → P (t + dt) (x + dx)

structure Diag (t : ℕ) (x : ℤ) (cote : ℕ) (P Q R : Spacetime) : Prop where
  size_pos    : 1 < cote
  apex        : P t (x + cote)
  interior    : ∀ dt dx : ℕ, 0 < dt → 0 < dx → dt + dx = cote → Q (t + dt) (x + dx)
  bottomLeft  : R (t + cote) x

structure Diag' (t : ℕ) (x : ℤ) (cote : ℕ) (P Q' Q R : Spacetime) : Prop where
  size_pos    : 2 < cote
  apex        : P t (x + cote)
  topRow      : ∀ dx : ℕ, dx + 1 = cote → Q' (t + 1) (x + dx)
  interior    : ∀ dt dx : ℕ, 1 < dt → 0 < dx → dt + dx = cote → Q (t + dt) (x + dx)
  bottomLeft  : R (t + cote) x

structure Semi_Diag (t : ℕ) (x : ℤ) (cote : ℕ) (P Q : Spacetime) : Prop where
  size_pos : 0 < cote
  apex     : P t (x + cote)
  interior : ∀ dt dx : ℕ, 0 < dt → dt + dx = cote → Q (t + dt) (x + dx)
```

| # | Lemma | Difficulty |
|---|---|---|
| 1.1 | `Rec_Diag` | M |
| 1.2 | `Rec_Diag'` | M |
| 1.3 | `Rec_SemiDiag` | M |
| 1.4 | `inter` (2D induction filler) | M |
| 1.5 | `inclus_vert`, `vv_vert`, `rec_vert`, `vert_un/deux/trois` | S each |
| 1.6 | `hh_hor`, `hor_un/deux/trois/quatre` | S each |
| 1.7 | `rec_triangle_inf` | M |

**Total: ~12 lemmas, M aggregate.**

### Layer 2 — Construction calculus (`constr.v` in Lean) (M each, ~15 lemmas)

Define `loi`, `loi_droite` predicates over `Spacetime`. Then port the `Pas_*` and `D??_???`/`?D_??`/etc. combinators. These are mechanical — `intros; simpl; rewrite … `-style — but there are many of them.

```lean
abbrev loi (P Q R T : Spacetime) : Prop :=
  ∀ t x, P t x → Q t (x+1) → R t (x+2) → T (t+1) (x+1)
abbrev loi_droite (Q R T : Spacetime) : Prop :=
  ∀ t x, Q t x → R t (x+1) → T (t+1) x
```

| # | Lemma | Difficulty |
|---|---|---|
| 2.1 | `Pas_hh`, `Pas_hd`, `Pas_dh`, `Pas_hddollar`, `Pas_dhdollar`, `Pas_hb`, `Pas_bb` | S each |
| 2.2 | `demi_Pas_h`, `demi_Pas_ddollar` | S each |
| 2.3 | `DDD`, `D'DD`, `D'DD'`, `DD'D` | M each |
| 2.4 | `DD_D'`, `D_D'D`, `DD_Ddollar`, `D_DDdollar` | M each |
| 2.5 | `DD_D`, `D'D_D`, `D_DD`, `DDdollar_D` | M each |
| 2.6 | `DD_d`, `Dd_d`, `dd_d` (for `Semi_Diag`) | M each |

**Total: ~22 lemmas, all M, but very mechanical. Could be ~1 day of porting once Layer 1 is stable.**

### Layer 3 — Bricks `A_basic`, `B_basic`, `C_basic` and apex helpers (S/M, ~15 lemmas)

```lean
abbrev A_state : Spacetime := fun t x => C.nextt c₀ t x = .A    -- with c₀ the FSSP initial config
abbrev B_state : Spacetime := …
abbrev C_state : Spacetime := …
abbrev L_state : Spacetime := …
abbrev G_state : Spacetime := …
abbrev F_state : Spacetime := …

structure A_basic (n : ℕ) (t : ℕ) (x : ℤ) (cote : ℕ) : Prop where
  size : 2 < cote
  diag0 : Diag t x cote (L_state n) (A_state n) (L_state n)
  diag1 : Diag (t+1) x cote (L_state n) (A_state n) (L_state n)
-- analogously for B_basic, C_basic
```

| # | Lemma | Difficulty |
|---|---|---|
| 3.1 | `A_basic`/`B_basic`/`C_basic` definitions + decidability instances | S |
| 3.2 | `A_A`, `B_B`, `C_C` (vertical reuse) | M |
| 3.3 | `A_B`, `B_C`, `C_A` (rotation) | M |
| 3.4 | `GA_G`, `GB_G`, `GC_G`, `GA_dollarC`, `GBA_dollarC`, `GBG_dollarG`, `GBC_dollarB`, `GC_dollarB` | S each (just `δ`-cases) |

**Total: ~12 lemmas, mostly S/M.**

### Layer 4 — Reflection (`UA`, `UAB`, `ZCB`) and `*_Vg` walls (M, ~10 lemmas)

```lean
structure ZCB (n t : ℕ) (x : ℤ) (cote : ℕ) : Prop where
  size  : 1 < cote
  diag0 : Diag t x cote (G_state n) (C_state n) (G_state n)
  diag1 : Diag (t+1) x cote (G_state n) (B_state n) (G_state n)
-- UA, UAB analogous
```

| # | Lemma | Difficulty |
|---|---|---|
| 4.1 | `UA`/`UAB`/`ZCB` definitions | S |
| 4.2 | `B_UA`, `C_UAB`, `A_ZCB`, `B_ZCB`, `C_ZCB` | M each |
| 4.3 | `ZCB_GLC`, `ZCB_l`, `ZCB_ll`, `ZCB_lll` | M each (mostly `recur_nSn`) |
| 4.4 | `ZCB_Ht1` (apex translation) | M-L |
| 4.5 | `A_Vg`, `B_Vg`, `C_Vg` | S each |

**Total: ~10 lemmas, M aggregate.**

### Layer 5 — Border staircase (`un_end`..`cinq_end`) (M, ~12 lemmas)

```lean
structure un_end   (n t : ℕ) (x : ℤ) : Prop where
  g0 : G_state n t x
  g1 : G_state n (t+1) x

structure deux_end (n t : ℕ) (x : ℤ) : Prop where
  c1  : C_state n t (x+1)
  b1  : B_state n (t+1) (x+1)
  one : un_end n (t+1) x

structure trois_end (n t : ℕ) (x : ℤ) : Prop where
  a2 : A_state n t (x+2); g2 : G_state n (t+1) (x+2); two : deux_end n (t+1) x

structure quatre_end (n t : ℕ) (x : ℤ) : Prop where
  l3a : L_state n t (x+3); l3b : L_state n (t+1) (x+3); three : trois_end n (t+1) x

structure cinq_end (n t : ℕ) (x : ℤ) : Prop where
  l4a : L_state n t (x+4); l4b : L_state n (t+1) (x+4)
  g3  : G_state n (t+1) (x+3); b3 : B_state n (t+2) (x+3)
  three : trois_end n (t+2) x
```

| # | Lemma | Difficulty |
|---|---|---|
| 5.1 | All 5 staircase definitions | S |
| 5.2 | `un_GG`, `deux_GG`, `trois_GG`, `quatre_GG`, `cinq_GG` (extract `G:G` at column 0) | S each |
| 5.3 | `un_deux`, `deux_trois`, `deux_quatre`, `trois_quatre`, `trois_cinq` | M each |
| 5.4 | `quatre_quatre`, `cinq_cinq`, `quatre_cinq` | M each |
| 5.5 | `cinq_quatre` (the recursion driver) | L |

**Total: ~12 lemmas.** **`cinq_quatre` is the only L lemma in this layer.**

### Layer 6 — `DD` recursion and bridges (M-L, ~12 lemmas)

```lean
inductive DD (n : ℕ) : ℕ → ℤ → ℕ → Prop where
  | DD_4 : ∀ t x, quatre_end n t x → DD n t x 3
  | DD_5 : ∀ t x, cinq_end   n t x → DD n t x 4
  | DD_A : ∀ t x cote, 6 ≤ cote → cote % 3 = 0 →
           A_basic n t (x + (2 * (cote/3) - 1)) (cote/3 + 1) →
           DD n (t + cote/3 + 1) x (2 * (cote/3) - 1) →
           DD n t x cote
  | DD_B : ∀ t x cote, 7 ≤ cote → cote % 3 = 1 →
           B_basic n t (x + 2 * (cote/3)) (cote/3 + 1) →
           DD n (t + cote/3 + 1) x (2 * (cote/3)) →
           DD n t x cote
  | DD_C : ∀ t x cote, 5 ≤ cote → cote % 3 = 2 →
           C_basic n t (x + (2 * (cote/3) + 1)) (cote/3 + 1) →
           DD n (t + cote/3 + 1) x (2 * (cote/3) + 1) →
           DD n t x cote
```

| # | Lemma | Difficulty |
|---|---|---|
| 6.1 | `DD` inductive type | S |
| 6.2 | `DD_GG` (`DD t x cote → G_state (t+cote) x ∧ G_state (t+cote+1) x`) | M |
| 6.3 | `DD_hh`, `DD_hddollar` | L (case-by-case for each of `DD_4`, `DD_5`, `DD_A`, `DD_B`, `DD_C`) |
| 6.4 | `Hor_tr_inf`, `Ht1_End2`, `Ht1_End4` | M each |
| 6.5 | `Ht1_DD`, `Ht1_DDf` | M |
| 6.6 | `Ht1_VV` | M |
| 6.7 | `Ht0_End2`, `Ht0_End4`, `Ht0_DD`, `Ht0_DDf` | M each |

**Total: ~12 lemmas. `DD_hh`/`DD_hddollar` are the work-horses.** The Coq proofs are ~150 lines each.

### Layer 7 — Trapezoids and apex (`DD_Hg`) (L-XL, ~10 lemmas)

| # | Lemma | Difficulty |
|---|---|---|
| 7.1 | Arithmetic helpers `R1`/`R2`/`R3`/`R4`/`R5`/`R6` for `tiers`/`double` | S each |
| 7.2 | `Ha_Vg`, `Hb_Vg`, `Hc_Vg` | L each |
| 7.3 | `Ha3_Hg`, `Hb3_Hg`, `Hc3_Hg`, `Hc2_Hg`, `Hc2_Vg`, `H2_Vg`, `H2_Hh`, `H2_Hg` | M each |
| 7.4 | `Ha_DD`, `Hb_DD`, `Hc_DD` | L each |
| 7.5 | `quatre_Hg`, `cinq_Hg` (base cases of `DD_Hg`) | M-L |
| 7.6 | `DD_Hg` (strong-induction theorem) | **XL** |
| 7.7 | `Hg_Hf` | M |

**Total: ~10 lemmas. `DD_Hg` is the single most expensive lemma in the entire port (Coq ~70 lines, but using `recur2` strong induction over multiple arms).**

### Layer 8 — Final assembly and translation to `SolvesFSSPOptimal` (M-L, ~8 lemmas)

```lean
-- Bridge from CA-trace language to Coq's Etat:
def cell (n t : ℕ) (x : ℤ) : Couleur := C.nextt ⟬fssp_left_side n⟭ t x

-- Initial configuration matches Coq's Etat 0, given the Border ↔ phantom translation.
lemma cell_zero_general    (n : ℕ) (h : 4 ≤ n) : cell n 0 0 = G                                  -- S
lemma cell_zero_quiet      (n : ℕ) (h : 4 ≤ n) (x : ℤ) (hx : 1 ≤ x) (hxn : x < n) : cell n 0 x = L  -- S
lemma cell_zero_phantom_G  (n : ℕ) (h : 4 ≤ n) : cell n 0 (n : ℤ) = G                             -- M (Border=G via δ)

-- Step rules in CA framework
lemma cell_step (n t : ℕ) (x : ℤ) :
    cell n (t+1) x = MazoyerDelta (left_view n t x) (cell n t x) (right_view n t x) -- M

-- Initial-row predicates
lemma base1 (n : ℕ) (h : 4 ≤ n) : Horizontale_t0 0 0 (n - 2) (G_state n) (L_state n)              -- S
lemma base2 (n : ℕ) (h : 4 ≤ n) : Horizontale_t1 0 (n : ℤ) (n - 2) (G_state n) (C_state n) (L_state n)
                                                                                                  -- M (uses Border=C/L emergence)

lemma diagonale (n : ℕ) (h : 4 ≤ n) : DD n (n - 2) 0 n                                            -- S (just Ht0_DDf base1)
lemma vert_droite (n : ℕ) (h : 4 ≤ n) :                                                           -- M
    Verticale 1 (n : ℤ) (2 * n - 3) (G_state n)
lemma sommet_1 (n : ℕ) (h : 4 ≤ n) : Horizontale (2 * n - 3) 0 (n - 1) (G_state n)               -- M
lemma firing_squad_internal (n : ℕ) (h : 4 ≤ n) : Horizontale (2 * n - 2) 0 (n - 1) (F_state n)  -- M

theorem fssp_optimal_correct : SolvesFSSPOptimal C                                                -- L
```

| # | Lemma | Difficulty |
|---|---|---|
| 8.1 | `cell_zero_*` (initial config in `Couleur` language) | S each |
| 8.2 | `cell_step` (one CA step in `Couleur` language) | M |
| 8.3 | `base1`, `base2` | S, M |
| 8.4 | `diagonale` | S |
| 8.5 | `vert_droite` | M |
| 8.6 | `sommet_1` | M |
| 8.7 | `firing_squad_internal` | M |
| 8.8 | **`fssp_optimal_correct : SolvesFSSPOptimal C`** | **L** (must also prove the *non-firing-before* direction; see §10) |

The non-trivial part of 8.8 is the second half of `fire_iff`: every cell is **not** `F` at any `t < 2n − 2`. The Coq proof handles this via `cinq_end` / `quatre_end` showing the column-0 cell is `G` not `F` until time `2n − 2`, plus an analogous argument for interior cells via the staircase of brick interiors. *This direction is not in `final.v`* and will require new work in Lean (it needs an "F-freshness" lemma — see §10 risk #5).

**Estimated total: ~110 named lemmas, of which ~3 are XL (= `DD_Hg`, `cinq_quatre`, `fssp_optimal_correct`'s reverse direction), ~25 are L, ~40 are M, ~40 are S.**

---

## 10. Risks and unsoundness pitfalls

### Risk 1 — `nat` ↔ `ℤ` indexing

Coq uses `nat` for both `t` and `x`. Lean's framework uses `ℕ` for `t` but `ℤ` for `x`. Translation rules:

- A Coq `x : nat` becomes Lean `(x : ℤ)` with implicit nonneg side-condition `0 ≤ x`. In our staircase `un_end..cinq_end` and brick `*_basic` types, all `x + k` arithmetic is over `ℤ` and we never need nonneg facts about `x` itself — only about `x + k`. So we can simply lift everything to `ℤ` and forget about it.
- `S x` becomes `x + 1`.
- `pred x` becomes `x - 1` (only when we have `1 ≤ x`).
- `cote / 3` becomes `cote / 3` (Lean's `Nat.div` agrees with `tiers` on natural numbers).
- `cote % 3 = 0` corresponds to `Omod3`.

**Mitigation:** Write all `Diag`/`Verticale`/etc. with `x : ℤ` throughout. The integer arithmetic is mostly `omega`-trivial, while modular arithmetic (`cote % 3`) is `Nat.div_add_mod`-trivial. **No real obstruction.**

### Risk 2 — Coq `Etat` vs. Lean `cell` from `nextt`

Coq defines `Etat : nat → nat → Couleur` directly, with the right phantom hard-coded into `Etat 0 (S N)` and `Etat 0 (S (S N))`. In Lean, the configuration is `⟬fssp_left_side n⟭ : ℤ → Couleur？` and the CA expands `none` to `Border` then evolves under `δ`.

The translation requires proving that **for `t ≤ 2n − 2` and `0 ≤ x ≤ n`, `cell n t x` (in `Couleur`) equals the `Etat`-style trace** — i.e., that the *real* cells `0..n−1` plus the *single virtual right-G cell* `n` are unaffected by anything past column `n+1`.

In Coq, this is automatic because `Etat 0 x = L` for all `x ≥ N+2` ([autom.v#L451 basedollar_L](external/firing-squad/autom.v)) and the state `L` is preserved by `δ L L L = L`. In Lean, we need:

> **Lemma `right_phantom_lemma` (M).** For `0 ≤ t ≤ 2n − 2` and `x ≥ n + 1`, `cell n t x = L`. Equivalently, the only states that propagate past column `n+1` from the left are `L` and `Border`, and `δ L L Border = δ L L L = L`.

This requires proving that the rightmost real cell `n − 1` never fires anything to the right of column `n + 1`. In Coq this is implicit; in Lean it needs a one-shot induction on `t`. **M, but easy to forget. Include it explicitly.**

The mirror argument for the *left* boundary is symmetric: cells with `x < 0` are all `Border`, and `δ`'s `Border`-handling makes them stay `Border` while propagating `L`-substitutes inward.

### Risk 3 — Border state and `vert_droite`

Coq's `vert_droite` ([final.v#L101](external/firing-squad/final.v)) says cell `S N` is `G_Etat` for the entire interval `[1, 2N − 1]`. This is *not directly usable* in Lean: cell `n` (= Coq `S N`) in our setup is `Border`, not `G`.

**Translation.** What Coq `vert_droite` *means* operationally is: cell `n − 1` (the rightmost real cell) always sees the constant `G` to its right. In Lean, this is *encoded into `δ`* by the rule

```
δ c0 c1 Border = MazoyerDelta c0 c1 G
```

So the *Lean* `vert_droite` is **not** a proposition about a column at all; it's a definitional fact about `δ`. The Coq `vert_droite` is a *consequence* of how Coq's `Etat` is initialized (with `G` at column `S N`), while in Lean it's *built into the rule*.

**Therefore in Lean, `vert_droite` becomes a trivial `rfl`-ish lemma**:

```lean
lemma vert_droite_one_step (n t : ℕ) (h : 4 ≤ n) :
    cell n (t+1) (n-1) =
      MazoyerDelta (cell n t (n-2)) (cell n t (n-1)) G := by
  unfold cell ; simp [δ, …]  -- the Border on the right gets substituted to G

-- The `Verticale (G_state n) (1, n, …)` predicate is unused in Lean —
-- replace `Verticale 1 (n+1) k G_state` everywhere by the
-- "G at the right phantom" identity above.
```

A *cleaner* approach: change the Lean `Verticale` predicate target from `cell n t (n+1) = G` (which is not even well-defined since cell `n+1` is `Border`) to a *pseudo-cell* function `cell⁺ n t x : Couleur` defined as `G` for `x = n` and `cell n t x` otherwise. Then `vert_droite : Verticale 1 n (2n−3) (G_state⁺ n)` is provable by `decide`/`rfl` on the `x = n` case and otherwise reduces to the existing `cell` analysis.

**This is the largest *conceptual* gap.** Most lemmas in `trapeze.v`/`sommet.v` consume `Verticale (S t) (S(x + cote)) … G_Etat` walls — these walls in Lean must be proved with the `cell⁺` extension; the very rightmost wall (the one created by the global right phantom) is *built into the CA*, while *interior* walls (the ones `Ha_Vg` etc. produce) are real `cell n` facts. The two notions of "G-wall" need to be unified by a single predicate `g_wall n t x haut := ∀ dt ≤ haut, cell⁺ n (t + dt) x = G`.

**Mitigation.** Define `cell⁺` explicitly in Layer 0 and prove its boundary-extension property (`cell⁺ n t n = G ∀ t ≤ 2n − 2`) by a separate induction on `t` using only the `Border ↦ G` substitution. M-L.

### Risk 4 — Side `cote` arithmetic

Coq uses `pred (double (tiers cote))`, `S (double (tiers cote))` etc. These are *closed forms* that simplify to integer expressions but are stated using Coq's awkward `pred`. Lean has no `pred` issue but has its own awkwardness with `Nat` subtraction (truncated). All arithmetic should be either `omega`-able (linear) or rephrased on `ℤ` to avoid truncation. **Risk is low; just need to consistently use `ℤ` for the side arithmetic and `Nat.div_add_mod`.**

### Risk 5 — Non-firing-before direction (`SolvesFSSP.fire_iff` reverse)

The Coq `firing_squad` proves only the *forward* direction "`F` at time `2N`". `SolvesFSSPOptimal` requires `cell ↦ F ↔ t ≥ 2n − 2`, i.e., **also the *no-firing-before* direction**. Coq's `algo.v` ([algo.v#L186 nth_line_2N_is_fire](external/firing-squad/algo.v)) does not prove this either.

The "no firing before" property follows because:
- The brick interiors carry `A`, `B`, or `C`, never `F`.
- The brick edges carry `L`, never `F`.
- The right phantom is `G`, never `F`.
- `F` is a sink (`δ _ F _ = F` and `δ F _ _ → F` only for fixed combinations); so once a cell becomes `F`, it stays `F`. Therefore *first-firing-time* is well-defined.
- The diagonal `DD` only produces `G` at column 0 at time `2n − 2` (this is `DD_GG`); *not* `F`.

**Strategy.** Add a strict `cell-not-F` invariant on the entire `DD` wedge: for every `(t', x')` covered by `DD t x cote`, `cell n t' x' ∈ {A, B, C, L, G}`, never `F`. Prove by induction on the `DD` constructors. The base cases `DD_4`/`DD_5` need `cell-not-F` on the staircase `un_end..cinq_end`, which is immediate from their definitions. The inductive cases need it on bricks (immediate from the brick types) and on the smaller `DD` (induction hypothesis).

**Estimated effort: one new lemma `DD_not_F` (M), one `quatre_end_not_F` / `cinq_end_not_F` (S each), one `*_basic_not_F` (S each). Then the reverse direction of `fire_iff` follows for `0 ≤ t < 2n − 2`.**

### Risk 6 — `quiescent_set` requirement

`SolvesFSSP` ([CellularAutomatas/proofs/fssp.lean#L11](CellularAutomatas/proofs/fssp.lean)) requires
```
quiescent_set : C.quiescent_set { C.border, C.inner false }
```

`C.border = Border`, `C.inner false = L`. So we need: for any `a, b, c ∈ {Border, L}`, `δ a b c = b`. By cases:
- `b = Border`: `δ _ Border _ = Border = b`. ✓ (by definition)
- `b = L`: we need `δ a L c = L` for `a, c ∈ {Border, L}`. By the `δ` definition this becomes `MazoyerDelta a' L c'` where `a', c' ∈ {L}` (Border ↦ L on the left and Border ↦ G on the right). So we get `MazoyerDelta L L L` (when both Border) or `MazoyerDelta L L G` (when right is Border) or `MazoyerDelta L L L` (right is L) etc. Checking [autom.v#L260 MazoyerL](external/firing-squad/autom.v): `MazoyerL c0 c2 = TAL c2` if `c0 = A`, `… = L` if `c0 = L`, etc. The case `MazoyerL L _ = L` (when `c0 = L`). What about `MazoyerL L G`? `TAL G = C` (no good!), but `MazoyerL` for `c0 = L` returns `L` directly. ✓.

But what about right-Border = G? `MazoyerL c0' G` for `c0' = L`: from `TLL` (middle `L`, left `L`)… wait, `MazoyerL` is the *middle = L* case. So:
```
MazoyerL c0 c2:
  | c0 = L => L     (regardless of c2)
  | c0 = Border => transmuted to L => L
```

Inspecting [fssp_mazoyer_ca.lean#L137 MazoyerL](CellularAutomatas/proofs/constructions/fssp_mazoyer_ca.lean):
```
| L => L  -- on c0
```
So `MazoyerL L _ = L`. After our `δ`'s `Border ↦ L` substitution on the left, **`δ Border L _ = MazoyerDelta L L _' = L` always**. ✓

**Conclusion:** `quiescent_set {Border, L}` holds. **One trivial `decide` lemma. S.**

### Risk 7 — Empty input case

`SolvesFSSPOptimal` requires the `fire_iff` for *every* `n ≥ 1`. Mazoyer's solution requires `n ≥ 4`. For `n ∈ {1, 2, 3}` we must **either** (i) prove a separate small case by `native_decide`, or (ii) use a different small CA and assemble.

`fssp_left_side 1 = [true]`. The "general" alone fires at time `0` (or never, depending on how we encode it). Actually, `SolvesFSSPOptimal` says `time n = 2 * n - 2`, so:
- `n = 1`: time `= 0`. Cell 0 should already be `F` at time 0. But our `embed (some true) = G`, not `F`. **Incompatible.** So `SolvesFSSPOptimal` itself is unsatisfiable for `n = 1` with this CA unless we adjust.

Looking again at [fssp.lean#L13 fire_iff](CellularAutomatas/proofs/fssp.lean): "∀ n ≥ 1, ∀ t, … = true ↔ t ≥ time n". For `n = 1, time n = 0`, this requires the cell to be `true` at *every* time `t ≥ 0`. Since a singleton general should "fire immediately" (no synchronization needed), this is correct *if* we treat the general as already firing. But our `project G = false`, so cell 0 *never* fires unless it's `F`.

**This is an existing gap in the spec, not in our porting.** We will need to either:

(a) Adjust `time` for small `n` (special-case `n ≤ 3`), OR
(b) Prove `SolvesFSSPOptimal` only for `n ≥ 4` (i.e., reformulate `SolvesFSSP` to require `n ≥ 4`), OR
(c) Build a wrapper CA that immediately fires for `n ≤ 3` and runs Mazoyer for `n ≥ 4`.

**The cleanest path: amend `SolvesFSSPOptimal` (or use a new spec `SolvesFSSPOptimal_n_ge_4`) and prove only that.** The `n ≤ 3` cases are independently solvable (and are indeed solved by special construction in Mazoyer's original paper).

**This is more a spec-clarification issue than a proof-port issue.** Discuss with the user before committing.

### Risk 8 — `SolvesTwoSidedFSSPOptimal_of_SolvesFSSPOptimal`

This is *not* part of the Coq Mazoyer proof. It is a separate, well-known reduction (one-sided to two-sided FSSP) and is orthogonal to this work. Out of scope here.

### Summary of risks

| # | Risk | Severity | Plan |
|---|---|---|---|
| 1 | `nat` ↔ `ℤ` indexing | Low | Lift to `ℤ` throughout. |
| 2 | `Etat` vs `cell n t x` | Low-M | One `right_phantom_lemma` (M). |
| 3 | `Border` and `vert_droite` | **M-L** | Define `cell⁺` extension; restate `Verticale` against it. |
| 4 | `tiers`/`pred(double)` arithmetic | Low | Use `ℤ` and `omega`. |
| 5 | No-firing-before direction | M | Add `DD_not_F` invariant lemma. |
| 6 | `quiescent_set` | Trivial | One `decide` lemma. |
| 7 | `n ∈ {1, 2, 3}` cases | **Spec issue** | **Discuss with user; recommend restricting `SolvesFSSPOptimal` to `n ≥ 4`.** |
| 8 | Two-sided FSSP | Out of scope | Skip. |

---

## Appendix A — Recommended ordering for incremental builds

Lean compilation cost is dominated by `lake build` of the bottom layers. To keep the iteration loop fast:

1. **Phase 1 (1 file): `geom.lean`.** Layer 1. Builds in seconds; once stable, never touch.
2. **Phase 2 (1 file): `constr.lean`.** Layer 2. Builds in ~10 s.
3. **Phase 3 (1 file): `basic_bricks.lean`.** Layer 3. Builds in <30 s.
4. **Phase 4 (1 file): `reflection.lean`.** Layer 4. <30 s.
5. **Phase 5 (1 file): `border.lean`.** Layer 5. <30 s.
6. **Phase 6 (1 file): `double_diag.lean`.** Layer 6. **This will be the bottleneck — `DD_hh`/`DD_hddollar` may take a minute each.**
7. **Phase 7 (1 file): `trapeze.lean`** (Layer 7, parts 7.1–7.5).
8. **Phase 8 (1 file): `sommet.lean`** (Layer 7, part 7.6: `DD_Hg`). XL.
9. **Phase 9 (1 file): `final.lean`** (Layer 8). Glue.

Each file's build target is `lake build CellularAutomatas.proofs.constructions.fssp_mazoyer.<file>`. Add to `CellularAutomatas/all.lean` as files become stable.

---

## Appendix B — Suggested directory layout

```
CellularAutomatas/proofs/constructions/
├── fssp_mazoyer_ca.lean              ← (existing) the CA C, native_decide tests
└── fssp_mazoyer/
    ├── geom.lean                     ← Layer 1
    ├── constr.lean                   ← Layer 2
    ├── basic_bricks.lean             ← Layer 3
    ├── reflection.lean               ← Layer 4
    ├── border.lean                   ← Layer 5
    ├── double_diag.lean              ← Layer 6
    ├── trapeze.lean                  ← Layer 7.1–7.5
    ├── sommet.lean                   ← Layer 7.6 (DD_Hg)
    └── final.lean                    ← Layer 8: SolvesFSSPOptimal C
```

Single-file build target for the final theorem: `lake build CellularAutomatas.proofs.constructions.fssp_mazoyer.final`.

---

## Appendix C — Quick reference of the 16 critical Coq lemmas

For each, the Coq location and a one-line recap of *exactly* what to port:

| # | Coq lemma | Loc | Lean target |
|---|---|---|---|
| 1 | `Pas_hh` | [constr.v#L46](external/firing-squad/constr.v) | One-step `δ`-application (horizontal-horizontal) |
| 2 | `DDD` | [constr.v#L162](external/firing-squad/constr.v) | Compose two `Diag`s vertically into a third |
| 3 | `A_A` | [basic.v#L80](external/firing-squad/basic.v) | A-brick + 2 trailing L's ⇒ A-brick two steps later |
| 4 | `C_A` | [basic.v#L213](external/firing-squad/basic.v) | C-brick + 2 trailing L's ⇒ A-brick of side+1 |
| 5 | `A_ZCB` | [reflection.v#L130](external/firing-squad/reflection.v) | A-brick + G-wall ⇒ ZCB |
| 6 | `ZCB_Ht1` | [reflection.v#L420](external/firing-squad/reflection.v) | ZCB + G-wall ⇒ `Horizontale_t1 G C L^*` |
| 7 | `cinq_quatre` | [bord.v#L228](external/firing-squad/bord.v) | cinq_end + 2 L's ⇒ C-brick + quatre_end (recursion driver) |
| 8 | `Ht1_DD` | [vertical.v#L122](external/firing-squad/vertical.v) | `Horizontale_t1` row ⇒ `DD` |
| 9 | `Ht1_VV` | [vertical.v#L138](external/firing-squad/vertical.v) | `Horizontale_t1` row ⇒ vertical G-wall |
| 10 | `Ht0_DDf` | [vertical.v#L235](external/firing-squad/vertical.v) | Initial `Horizontale_t0` row ⇒ `DD` |
| 11 | `DD_hh` | [double_diag.v#L100](external/firing-squad/double_diag.v) | DD + 2 L's ⇒ DD two steps later |
| 12 | `DD_hddollar` | [double_diag.v#L156](external/firing-squad/double_diag.v) | DD + 2 L's ⇒ DD of side+1 (the recursion!) |
| 13 | `Ha_Vg`/`Hb_Vg`/`Hc_Vg` | [trapeze.v#L113](external/firing-squad/trapeze.v) | A/B/C-brick + G-wall right ⇒ G-wall left |
| 14 | `Ha_DD`/`Hb_DD`/`Hc_DD` | [trapeze.v#L165](external/firing-squad/trapeze.v) | A/B/C-brick + G-wall right ⇒ smaller DD below |
| 15 | `DD_Hg` | [sommet.v#L266](external/firing-squad/sommet.v) | **THE THEOREM**: DD + G-wall ⇒ all-G row at `t+cote+1` |
| 16 | `Hg_Hf` | [sommet.v#L394](external/firing-squad/sommet.v) | All-G row + G to its right ⇒ all-F row next step |

These 16 lemmas are the **load-bearing skeleton** of the proof. Everything else is plumbing.

---

End of report.