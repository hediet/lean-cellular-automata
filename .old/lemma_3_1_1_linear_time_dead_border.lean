import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca

variable [Alphabet]


def Neighborhood (Q: Type u) := Q × Q × Q

def neighborhood_at {Q: Type u} (c: Config Q) (i: ℤ): Neighborhood Q :=
  (c (i - 1), c i, c (i + 1))

def CellAutomaton.δnh {C: CellAutomaton} (nh: Neighborhood C.Q): C.Q :=
  let (q_left, q_center, q_right) := nh
  C.δ q_left q_center q_right



def LCellAutomaton.visible_by (t_end: ℕ) (i_end: ℤ) := fun (t: ℕ) (i: ℤ) => t_end ≥ t ∧ |i_end - i| ≤ (t_end - t)




-- We can take this as given for this proof
axiom tCellAutomaton.linear_time_dead_border (C: tCellAutomaton) (h: ∃ c, ∀ n, C.t n ≤ c * (n + 1)): ∃ C': tCellAutomaton,
    C'.L = C.L
    ∧ C'.t = C.t
    ∧ C'.dead C'.border








section Construction

class Foo where
  max_lane_abs: ℕ


class Env where
  C: tCellAutomaton
  C_passive_border: C.dead C.border

variable {u: Type u} [env: Env] [foo: Foo]

def max_lane_abs := foo.max_lane_abs
def C := env.C
instance : DecidableEq C.Q := C.inv_decidable_q
instance : Fintype C.Q := C.inv_fin_q
instance instFiniteCQ : Finite C.Q := Finite.of_fintype _

def Lane.contains (i: ℤ): Prop := -max_lane_abs ≤ i ∧ i ≤ max_lane_abs
abbrev Lane := { i: ℤ // Lane.contains i }

@[simp]
lemma Lane.contains_zero : Lane.contains 0 := by
  simp [Lane.contains, max_lane_abs]

def FoldedPos := ℕ × Lane

abbrev Lanes := Lane → C.Q




instance Lane.decidable_contains (lane: ℤ): Decidable (Lane.contains lane) := by
  dsimp [Lane.contains]
  infer_instance

instance instFiniteLane : Finite Lane :=
  have : Set.Finite { i | Lane.contains i } := by
    simp [Lane.contains]
    exact Set.finite_Icc _ _
  Set.Finite.to_subtype this

instance : DecidableEq Lane := inferInstance



def Lanes.atD {lanes: Lanes} (i: ℤ) (or: C.Q): C.Q :=
  if h: Lane.contains i then
    lanes ⟨i, h⟩
  else
    or







/-
...  #  # -6 -5 -4 -3 -2 -1 [ 0  1  2] 3  4  5  6  7  8  #  #
...
...                          -6 -5 -4
...                          -1 -2 -3
...                 #  #  # [ 0  1  2] #  #  #
...                           5  4  3
...                           6  7  8
-/

def map_coord (w_len: ℕ) (i: ℤ): Option FoldedPos :=
  if w_len = 0 then
    none
  else
    let w_len_z : ℤ := w_len
    let lane_idx := if i >= 0 then i / w_len_z else (i + 1) / w_len_z - 1
    if h_lane : Lane.contains lane_idx then
      let lane : Lane := ⟨lane_idx, h_lane⟩
      let rem := i % w_len_z
      let j_z := if lane_idx % 2 = 0 then rem else w_len_z - 1 - rem
      some (j_z.toNat, lane)
    else
      none

-- define instance of alphabet to be 0, 1

instance x: Alphabet := {
  α := Bool
  fin := by infer_instance
}

instance y: Env := {
  C := sorry,
  C_passive_border := sorry,
}

instance foo2: Foo := {
  max_lane_abs := 2
}

instance :  Repr FoldedPos where
  reprPrec p _ := "(j: " ++ repr p.1 ++ ", lane: " ++ repr p.2.val ++ ")"

#eval! [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun val => (val, (map_coord 3) val))


abbrev Q' := Option Lanes



def normalize_q (c: Q'): Lane → C.Q := c.getD fun _ => C.border

def unfold (c: Config Q') (w_len: ℕ): Config C.Q :=
  fun i =>
    match map_coord w_len i with
    | none => C.border
    | some (j, lane) => (normalize_q (c j)) lane





def get_lane_val_nat (lanes: Lanes) (lane: ℤ): C.Q :=
  if h: Lane.contains lane then
    lanes ⟨lane, h⟩
  else
    C.border

def get_relative (center: Lanes) (lane: Lane) (relative: Q') (relative_offset: ℤ): C.Q :=
  match relative with
  | some f => f lane
  | none => center.atD (lane.val + relative_offset) C.border

def get_local_neighborhood (q_left: Q') (q_center: Lanes) (q_right: Q') (lane: Lane) : Neighborhood C.Q :=
  let is_even := lane.val % 2 == 0
  let (l, r) := if is_even then (q_left, q_right) else (q_right, q_left)
  let a := get_relative q_center lane l (-1)
  let b := q_center lane
  let c := get_relative q_center lane r 1

  (a, b, c)

def F_pos' (q: Q'): Prop :=
  match q with
  | none => false
  | some lanes => lanes ⟨0, by simp⟩ ∈ C.F_pos

def embed' (a: α): Q' :=
  some (fun lane => if lane.val = 0 then C.embed a else C.border)

def C': tCellAutomaton :=
  {
    Q := Q'
    inv_decidable_q := sorry
    inv_fin_q := sorry
    border := none
    δ := fun q_left q_center q_right =>
      match q_center with
      | none => none
      | some q_center_lanes =>
        let new_lane := fun (lane: Lane) =>
          let n' := get_local_neighborhood q_left q_center_lanes q_right lane
          C.δnh n'
        some new_lane
    embed := embed'

    t := C.t
    F_pos := F_pos'
  }


-- I believe we can relate get_local_neighborhood and map_coord

-- For small enough t, C' performs a folded simulation of C
lemma C'_spec (w: Word) (t: ℕ) (h: t ≤ w.length * max_lane_abs):
  C.comp w t = unfold (C'.comp w t) w.length := by

  induction t



end Construction
