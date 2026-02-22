# Particle Framework Design

## Goal

Define CAs by composing **particles** — point-like entities that move and interact.
The framework should:
1. Make CA definitions declarative and short
2. Automatically construct the CA transition function
3. Provide generic proofs that the CA matches particle trajectories

---

## Example: Exponential Time CA

The exp_core CA has two particles: **mirror** and **signal**.

### Desired Usage

```lean
-- Define the mirror particle
def mirror : Particle where
  State := MirrorPhase  -- M1 | M2 | M3
  init := (0, .M1)      -- starts at position 0!
  step := fun state _ =>
    match state with
    | .M1 => (.stay,  .M2)   -- stay, become M2
    | .M2 => (.stay,  .M3)   -- stay, become M3
    | .M3 => (.right, .M1)   -- move right, become M1

-- Define the signal particle
-- It needs to see: (1) is mirror at M2 here? (2) is this position 0?
def signal (mirror : Particle) : Particle where
  State := SignalDir  -- SR | SL
  init := (0, .SR)    -- starts at position 0, going right
  step := fun state env =>
    match state with
    | .SR => if env.mirror_is_M2 then (.right, .SL) else (.right, .SR)
    | .SL => if env.is_origin    then (.left,  .SR) else (.left,  .SL)

-- Combine into a CA
def exp_core := particleCA [mirror, signal]
  where signal.env := fun t p => {
    mirror_is_M2 := mirror.at t p == some .M2
    is_origin := p == 0
  }
```

### What the Framework Provides

```lean
-- Automatically derived:
theorem exp_core_trajectory (t : ℕ) (p : ℤ) :
    exp_core.nextt init t p = 
      (mirror.stateAt t p, signal.stateAt t p)

-- Where stateAt is:
--   some s  if particle is at position p at time t with state s
--   none    if particle is not at position p at time t
```

---

## Key Insight: Consensus on Movement

You noted: "all 3 neighbors must agree on how the particle moves."

This is the **local-to-global** bridge:
- A particle's trajectory is a **global** concept (one position per time)
- The CA transition is **local** (each cell sees only neighbors)

For these to match, whenever a particle is involved in a transition:
- The cell the particle **leaves** must know it's leaving
- The cell the particle **enters** must know it's entering
- (For staying: same cell, still needs to know)

This works because:
1. Movement depends only on **state**, not position
2. State is stored in the cell
3. Neighbors can see the state

So if cell `p` contains particle in state `s`:
- Cell `p` knows: "I have state s, velocity(s) = +1, so particle leaves rightward"
- Cell `p+1` knows: "Left neighbor has state s, velocity(s) = +1, so particle arrives"

**Both cells compute the same velocity from the same state.**

---

## Framework Sketch

### Particle Definition

```lean
structure Particle where
  State : Type
  init_pos : ℤ
  init_state : State
  velocity : State → ℤ  -- must be in {-1, 0, +1}
  transition : State → Env → State  -- or Option State for death
```

### Trajectory (Abstract)

```lean
def Particle.trajectory (env : ℕ → ℤ → Env) : ℕ → ℤ × State
  | 0 => (init_pos, init_state)
  | t + 1 =>
    let (pos, state) := trajectory env t
    let new_pos := pos + velocity state
    let new_state := transition state (env (t+1) new_pos)
    (new_pos, new_state)
```

### CA Cell State

For a system with particles `P₁, ..., Pₙ`:
```lean
CellState := Option P₁.State × ... × Option Pₙ.State
```

Each component is `some s` if that particle is here with state `s`, else `none`.

### CA Transition

```lean
def δ (left center right : CellState) : CellState :=
  -- For each particle i:
  --   Check if particle arrives from left (velocity = +1)
  --   Check if particle stays from center (velocity = 0)
  --   Check if particle arrives from right (velocity = -1)
  --   At most one of these is true (particle uniqueness)
  --   If arriving: compute new state via transition
  ...
```

### Main Theorem (Generic)

```lean
theorem particle_ca_correct (t : ℕ) (p : ℤ) :
    ca.nextt init t p = expectedCell trajectories t p
```

Where `expectedCell` puts each particle's state in the cell if the particle is there.

---

## Open Questions

1. **Environment computation**: How does the signal know if mirror is at M2?
   - Option A: Environment is computed from the CA state (circular?)
   - Option B: Particles are ordered; later particles see earlier particles' trajectories
   - Option C: Environment is computed from abstract trajectories, proven to match CA

2. **Multiple particles at same position**: What if two particles collide?
   - Current exp_core: mirror and signal can be at the same position (they're independent)
   - Some CAs have particles that interact on collision

3. **Spawning/death**: Can particles create new particles or die?
   - Death: `transition` returns `Option State`
   - Spawning: More complex, maybe out of scope

---

## Next Steps

1. Implement the framework for the simple case (independent particles, no collision interaction)
2. Reprove exp_core using the framework
3. Measure proof length reduction
4. Extend if needed
