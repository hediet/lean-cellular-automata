# Proof: Lx(L) ∈ OCA(2n) ⟹ L ∈ OCA(2n)

## Definition

```
Lx(L) := { x^m w | w ∈ L, m = 2^ceil(log₂|w|) }
```

Note: m is always a power of 2, so 4 | m for |w| ≥ 4.

## Goal

Given: OCA C that recognizes Lx(L) in time 2n (i.e., OCA-2n).
Show: L ∈ OCA(2n).

**OCA-2n acceptance:** For input of length N, acceptance is at position -(N-1), time 2N.

---

## Space-Time Diagram: Original OCA C on x^m w

Example: w = "abc" (n = 3), so m = 2^ceil(log₂3) = 2² = 4.
Input to C: x x x x a b c (length N = m + n = 7)
Positions:  0 1 2 3 4 5 6

**OCA-2n acceptance:** position -(7-1) = -6, time 2(7-1) = 12.

**Original execution of OCA C on "xxxxabc":**

```
pos:  -6   -5   -4   -3   -2   -1  │  0    1    2    3  │  4    5    6
     ───────────────────────────────┼────────────────────┼─────────────────
t=0:  #₀   #₀   #₀   #₀   #₀   #₀  │  x₀   x₀   x₀   x₀ │  a₀   b₀   c₀
t=1:  #₁   #₁   #₁   #₁   #₁   #₁  │  x₁   x₁   x₁   x₁ │  a₁   b₁   ·
t=2:  #₂   #₂   #₂   #₂   #₂   #₂  │  x₂   x₂   x₂   x₂ │  a₂   ·    ·
t=3:  #₃   #₃   #₃   #₃   #₃   #₃  │  x₃   x₃   x₃   x₃ │  ·    ·    ·
t=4:  #₄   #₄   #₄   #₄   #₄   #₄  │  x₄   x₄   x₄   ·  │  ·    ·    ·
t=5:  #₅   #₅   #₅   #₅   #₅   #₅  │  x₅   x₅   ·    ·  │  ·    ·    ·
t=6:  #₆   #₆   #₆   #₆   #₆   #₆  │  x₆   ·    ·    ·  │  ·    ·    ·
t=7:  #₇   #₇   #₇   #₇   #₇   #₇  │  ·    ·    ·    ·  │  ·    ·    ·
t=8:  #₈   #₈   #₈   #₈   #₈   ·   │  ·    ·    ·    ·  │  ·    ·    ·
t=9:  #₉   #₉   #₉   #₉   ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·
t=10: #₁₀  #₁₀  #₁₀  ·    ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·
t=11: #₁₁  #₁₁  ·    ·    ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·
t=12: #₁₂★ ·    ·    ·    ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·
      ↑
      ACCEPT at (pos=-6, t=12) = (pos=-(N-1), t=2(N-1)) where N=7
```

**Goal for L:** Accept w="abc" at position -(n-1) = -2, time 2(n-1) = 4.

Via compression: 12 / 4 = 3 steps saved per compressed cell. Acceptance moves from (pos=-6, t=12) to (pos=3, t=4).

---

## Compressed Execution Diagram

With k=5 compression, the # and x cells are compressed and shifted right so that a stays at position 4:
- `#####` = compressed cell containing (#, #, #, #, #)
- `#xxxx` = compressed cell containing (#, x, x, x, x) — only 4 x's since m=4

**Regimes:**
- Spatial: t < d (distance from boundary at pos 4), all components at original time 5t
- Diagonal: t ≥ d, component j at original time t + 4d - j

Distances: pos 3 → d=1, pos 2 → d=2, pos 1 → d=3

```
pos:               1                  2                  3          │  4    5    6
            ───────────────────────────────────────────────────────────┼─────────────────
t=0:        #₀ #₀ #₀ #₀ #₀    #₀ #₀ #₀ #₀ #₀    #₀ x₀ x₀ x₀ x₀     │  a₀   b₀   c₀
            [spatial]         [spatial]         [spatial]           │
                                                                    │
t=1:        #₅ #₅ #₅ #₅ #₅    #₅ #₅ #₅ #₅ #₅    #₅ x₄ x₃ x₂ x₁     │  a₁   b₁   ·
            [spatial]         [spatial]         [diagonal]          │
                                                                    │
t=2:       #₁₀#₁₀#₁₀#₁₀#₁₀   #₁₀ #₉ #₈ #₇ #₆    #₆ x₅ x₄ x₃ x₂     │  a₂   ·    ·
            [spatial]         [diagonal]        [diagonal]          │
                                                                    │
t=3:       #₁₅#₁₄#₁₃#₁₂#₁₁   #₁₁#₁₀ #₉ #₈ #₇    #₇ x₆ x₅ x₄ x₃     │  ·    ·    ·
            [diagonal]        [diagonal]        [diagonal]          │
                                                                    │
t=4:            ·            #₁₂#₁₁#₁₀ #₉ #₈ ★  #₈ x₇ x₆ x₅ x₄     │  ·    ·    ·
                              [diagonal]        [diagonal]          │
                                          ↑
                               ACCEPT at (pos=2, t=4)
                               Component 0 = #₁₂ = original (pos=-6, t=12) ✓
```

Position 2, time 4, component 0 has original time: t + 4d - j = 4 + 4·2 - 0 = 12 ✓

This is exactly the OCA-2n acceptance position for L on input "abc"!

---

## Original Execution Diagram (n=4)

Example: w = "abcd" (n = 4), so m = 2^ceil(log₂4) = 2² = 4.
Input to C: x x x x a b c d (length N = m + n = 8)
Positions:  0 1 2 3 4 5 6 7

**OCA-2n acceptance:** position -(8-1) = -7, time 2(8-1) = 14.

**Original execution of OCA C on "xxxxabcd":**

```
pos:  -7   -6   -5   -4   -3   -2   -1  │  0    1    2    3  │  4    5    6    7
     ────────────────────────────────────┼────────────────────┼─────────────────────
t=0:  #₀   #₀   #₀   #₀   #₀   #₀   #₀  │  x₀   x₀   x₀   x₀ │  a₀   b₀   c₀   d₀
t=1:  #₁   #₁   #₁   #₁   #₁   #₁   #₁  │  x₁   x₁   x₁   x₁ │  a₁   b₁   c₁   ·
t=2:  #₂   #₂   #₂   #₂   #₂   #₂   #₂  │  x₂   x₂   x₂   x₂ │  a₂   b₂   ·    ·
t=3:  #₃   #₃   #₃   #₃   #₃   #₃   #₃  │  x₃   x₃   x₃   x₃ │  a₃   ·    ·    ·
t=4:  #₄   #₄   #₄   #₄   #₄   #₄   #₄  │  x₄   x₄   x₄   x₄ │  ·    ·    ·    ·
t=5:  #₅   #₅   #₅   #₅   #₅   #₅   #₅  │  x₅   x₅   x₅   ·  │  ·    ·    ·    ·
t=6:  #₆   #₆   #₆   #₆   #₆   #₆   #₆  │  x₆   x₆   ·    ·  │  ·    ·    ·    ·
t=7:  #₇   #₇   #₇   #₇   #₇   #₇   #₇  │  x₇   ·    ·    ·  │  ·    ·    ·    ·
t=8:  #₈   #₈   #₈   #₈   #₈   #₈   #₈  │  ·    ·    ·    ·  │  ·    ·    ·    ·
t=9:  #₉   #₉   #₉   #₉   #₉   #₉   ·   │  ·    ·    ·    ·  │  ·    ·    ·    ·
t=10: #₁₀  #₁₀  #₁₀  #₁₀  #₁₀  ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·    ·
t=11: #₁₁  #₁₁  #₁₁  #₁₁  ·    ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·    ·
t=12: #₁₂  #₁₂  #₁₂  ·    ·    ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·    ·
t=13: #₁₃  #₁₃  ·    ·    ·    ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·    ·
t=14: #₁₄★ ·    ·    ·    ·    ·    ·   │  ·    ·    ·    ·  │  ·    ·    ·    ·
      ↑
      ACCEPT at (pos=-7, t=14) = (pos=-(N-1), t=2(N-1)) where N=8
```

**Goal for L:** Accept w="abcd" at position -(n-1) = -3, time 2(n-1) = 6.

---

## Compressed Execution Diagram (n=4)

With k=5 compression, input "abcd" at positions 4-7:
- `#####` = compressed cell containing (#, #, #, #, #)
- `#xxxx` = compressed cell containing (#, x, x, x, x) — exactly 4 x's since m=4

Total x's: 4 = m ✓

Distances from boundary at pos 4: pos 3 → d=1, pos 2 → d=2, pos 1 → d=3

```
pos:               1                  2                  3          │  4    5    6    7
            ───────────────────────────────────────────────────────────┼─────────────────────
t=0:        #₀ #₀ #₀ #₀ #₀    #₀ #₀ #₀ #₀ #₀    #₀ x₀ x₀ x₀ x₀     │  a₀   b₀   c₀   d₀
            [spatial]         [spatial]         [spatial]           │
                                                                    │
t=1:        #₅ #₅ #₅ #₅ #₅    #₅ #₅ #₅ #₅ #₅    #₅ x₄ x₃ x₂ x₁     │  a₁   b₁   c₁   ·
            [spatial]         [spatial]         [diagonal]          │
                                                                    │
t=2:       #₁₀#₁₀#₁₀#₁₀#₁₀   #₁₀ #₉ #₈ #₇ #₆    #₆ x₅ x₄ x₃ x₂     │  a₂   b₂   ·    ·
            [spatial]         [diagonal]        [diagonal]          │
                                                                    │
t=3:       #₁₅#₁₄#₁₃#₁₂#₁₁   #₁₁#₁₀ #₉ #₈ #₇    #₇ x₆ x₅ x₄ x₃     │  a₃   ·    ·    ·
            [diagonal]        [diagonal]        [diagonal]          │
                                                                    │
t=4:       #₁₆#₁₅#₁₄#₁₃#₁₂   #₁₂#₁₁#₁₀ #₉ #₈    .  .  .  .  .      │  ·    ·    ·    ·
            [diagonal]        [diagonal]                            │
                                                                    │
t=5:       #₁₇#₁₆#₁₅#₁₄#₁₃   #₁₃#₁₂#₁₁#₁₀ #₉    .  .  .  .  .      │  ·    ·    ·    ·
            [diagonal]        [diagonal]                            │
                                                                    │
t=6:       #₁₈#₁₇#₁₆#₁₅#₁₄★   .  .  .  .  .     .  .  .  .  .      │  ·    ·    ·    ·
            [diagonal]                                              │
                          ↑
                ACCEPT at (pos=1, t=6)
                Component 0 = #₁₈ has time: 6 + 4·3 = 18
```

Position 1 = -(n-1) = -3 relative to input "abcd" starting at position 4.
Time 6 = 2(n-1) for n=4.

---

## Original Execution Diagram (n=5)

Example: w = "abcde" (n = 5), so m = 2^ceil(log₂5) = 2³ = 8.
Input to C: x x x x x x x x a b c d e (length N = m + n = 13)

**OCA-2n acceptance:** position -(13-1) = -12, time 2·13 = 26.

**Original execution of OCA C on "xxxxxxxxabcde":**

```
pos: -12  -11  -10  -9   -8   -7   -6   -5   -4   -3   -2   -1  │  0    1    2    3    4    5    6    7  │  8    9   10   11   12
     ────────────────────────────────────────────────────────────┼─────────────────────────────────────────┼────────────────────────
t=0:  #₀   #₀   #₀   #₀   #₀   #₀   #₀   #₀   #₀   #₀   #₀   #₀ │  x₀   x₀   x₀   x₀   x₀   x₀   x₀   x₀ │  a₀   b₀   c₀   d₀   e₀
t=1:  #₁   #₁   #₁   #₁   #₁   #₁   #₁   #₁   #₁   #₁   #₁   #₁ │  x₁   x₁   x₁   x₁   x₁   x₁   x₁   x₁ │  a₁   b₁   c₁   d₁   ·
t=2:  #₂   #₂   #₂   #₂   #₂   #₂   #₂   #₂   #₂   #₂   #₂   #₂ │  x₂   x₂   x₂   x₂   x₂   x₂   x₂   x₂ │  a₂   b₂   c₂   ·    ·
t=3:  #₃   #₃   #₃   #₃   #₃   #₃   #₃   #₃   #₃   #₃   #₃   #₃ │  x₃   x₃   x₃   x₃   x₃   x₃   x₃   x₃ │  a₃   b₃   ·    ·    ·
t=4:  #₄   #₄   #₄   #₄   #₄   #₄   #₄   #₄   #₄   #₄   #₄   #₄ │  x₄   x₄   x₄   x₄   x₄   x₄   x₄   x₄ │  a₄   ·    ·    ·    ·
t=5:  #₅   #₅   #₅   #₅   #₅   #₅   #₅   #₅   #₅   #₅   #₅   #₅ │  x₅   x₅   x₅   x₅   x₅   x₅   x₅   x₅ │  ·    ·    ·    ·    ·
t=6:  #₆   #₆   #₆   #₆   #₆   #₆   #₆   #₆   #₆   #₆   #₆   #₆ │  x₆   x₆   x₆   x₆   x₆   x₆   x₆   ·  │  ·    ·    ·    ·    ·
t=7:  #₇   #₇   #₇   #₇   #₇   #₇   #₇   #₇   #₇   #₇   #₇   #₇ │  x₇   x₇   x₇   x₇   x₇   x₇   ·    ·  │  ·    ·    ·    ·    ·
t=8:  #₈   #₈   #₈   #₈   #₈   #₈   #₈   #₈   #₈   #₈   #₈   #₈ │  x₈   x₈   x₈   x₈   x₈   ·    ·    ·  │  ·    ·    ·    ·    ·
t=9:  #₉   #₉   #₉   #₉   #₉   #₉   #₉   #₉   #₉   #₉   #₉   #₉ │  x₉   x₉   x₉   x₉   ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=10: #₁₀  #₁₀  #₁₀  #₁₀  #₁₀  #₁₀  #₁₀  #₁₀  #₁₀  #₁₀  #₁₀  #₁₀│  x₁₀  x₁₀  x₁₀  ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=11: #₁₁  #₁₁  #₁₁  #₁₁  #₁₁  #₁₁  #₁₁  #₁₁  #₁₁  #₁₁  #₁₁  #₁₁│  x₁₁  x₁₁  ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=12: #₁₂  #₁₂  #₁₂  #₁₂  #₁₂  #₁₂  #₁₂  #₁₂  #₁₂  #₁₂  #₁₂  #₁₂│  x₁₂  ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=13: #₁₃  #₁₃  #₁₃  #₁₃  #₁₃  #₁₃  #₁₃  #₁₃  #₁₃  #₁₃  #₁₃  #₁₃│  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=14: #₁₄  #₁₄  #₁₄  #₁₄  #₁₄  #₁₄  #₁₄  #₁₄  #₁₄  #₁₄  #₁₄  ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=15: #₁₅  #₁₅  #₁₅  #₁₅  #₁₅  #₁₅  #₁₅  #₁₅  #₁₅  #₁₅  ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=16: #₁₆  #₁₆  #₁₆  #₁₆  #₁₆  #₁₆  #₁₆  #₁₆  #₁₆  ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=17: #₁₇  #₁₇  #₁₇  #₁₇  #₁₇  #₁₇  #₁₇  #₁₇  ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=18: #₁₈  #₁₈  #₁₈  #₁₈  #₁₈  #₁₈  #₁₈  ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=19: #₁₉  #₁₉  #₁₉  #₁₉  #₁₉  #₁₉  ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=20: #₂₀  #₂₀  #₂₀  #₂₀  #₂₀  ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=21: #₂₁  #₂₁  #₂₁  #₂₁  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=22: #₂₂  #₂₂  #₂₂  ·    ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=23: #₂₃  #₂₃  ·    ·    ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=24: #₂₄★ ·    ·    ·    ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=25: ·    ·    ·    ·    ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·
t=26: .    ·    ·    ·    ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·    ·    ·    ·  │  ·    ·    ·    ·    ·

```

**Goal for L:** Accept w="abcde" at position -(n-1) = -4, time 2n = 10.

---

## Compressed Execution Diagram (n=5)

With k=5 compression, shifted so a stays at position 8:
- `#####` = compressed cell containing (#, #, #, #, #)
- `##xxx` = compressed cell containing (#, #, x, x, x) — only 3 x's here
- `xxxxx` = compressed cell containing (x, x, x, x, x)

Total x's: 3 + 5 = 8 = m ✓

Distances from boundary at pos 8: pos 7 → d=1, pos 6 → d=2, pos 5 → d=3, pos 4 → d=4

```
pos:          4                  5                  6                  7          │ 8  9  10 11 12
         ──────────────────────────────────────────────────────────────────────────┼─────────────────
t=0:    #₀ #₀ #₀ #₀ #₀    #₀ #₀ #₀ #₀ #₀    #₀ #₀ x₀ x₀ x₀    x₀ x₀ x₀ x₀ x₀   │ a₀  b₀  c₀  d₀  e₀
        [spatial]         [spatial]         [spatial]         [spatial]          │
                                                                                 │
t=1:    #₅ #₅ #₅ #₅ #₅    #₅ #₅ #₅ #₅ #₅    #₅ #₅ x₅ x₅ x₅    x₅ x₄ x₃ x₂ x₁   │ a₁  b₁  c₁  d₁  ·
        [spatial]         [spatial]         [spatial]         [diagonal]         │
                                                                                 │
t=2:   #₁₀#₁₀#₁₀#₁₀#₁₀   #₁₀#₁₀#₁₀#₁₀#₁₀   #₁₀ #₉ x₈ x₇ x₆    x₆ x₅ x₄ x₃ x₂   │ a₂  b₂  c₂  ·   ·
        [spatial]         [spatial]         [diagonal]        [diagonal]         │
                                                                                 │
t=3:   #₁₅#₁₅#₁₅#₁₅#₁₅   #₁₅#₁₄#₁₃#₁₂#₁₁   #₁₁#₁₀ x₉ x₈ x₇    x₇ x₆ x₅ x₄ x₃   │ a₃  b₃  ·   ·   ·
        [spatial]         [diagonal]        [diagonal]        [diagonal]         │
                                                                                 │
t=4:   #₂₀#₁₉#₁₈#₁₇#₁₆   #₁₆#₁₅#₁₄#₁₃#₁₂   #₁₂#₁₁x₁₀ x₉ x₈    x₈ x₇ x₆ x₅ x₄   │ a₄  ·   ·   ·   ·
        [diagonal]        [diagonal]        [diagonal]        [diagonal]         │
                                                                                 │
t=5:   #₂₁#₂₀#₁₉#₁₈#₁₇   #₁₇#₁₆#₁₅#₁₄#₁₃   #₁₃#₁₂x₁₁x₁₀ x₉    x₉ x₈ x₇ x₆ x₅   │ .   .   .   .   .
        [diagonal]        [diagonal]        [diagonal]        [diagonal]         │
                                                                                 │
t=6:   #₂₂#₂₁#₂₀#₁₉#₁₈   #₁₈#₁₇#₁₆#₁₅#₁₄   #₁₄#₁₃x₁₂x₁₁x₁₀    .  .  .  .  .    │ .   .   .   .   .
        [diagonal]        [diagonal]        [diagonal]                           │
                                                                                 │
t=7:   #₂₃#₂₂#₂₁#₂₀#₁₉   #₁₉#₁₈#₁₇#₁₆#₁₅    .  .  .  .  .     .  .  .  .  .    │ .   .   .   .   .
        [diagonal]        [diagonal]                                             │
                                                                                 │
t=8:   #₂₄#₂₃#₂₂#₂₁#₂₀★   .  .  .  .  .     .  .  .  .  .     .  .  .  .  .    │ .   .   .   .   .
        [diagonal]                                                               │
                     ↑
          ACCEPT at (pos=4, t=8)
          Component 0 = #₂₄ has time: 8 + 4·4 = 24 ✓
          = original (pos=-12, t=24) ✓
```

Position 4 = -(n-1) = -4 relative to input "abcde" starting at position 8.
Time 8 = 2(n-1) for n=5.

This is exactly the OCA-2(n-1) acceptance position for L on input "abcde"!

---

## Step 1: Folding CA

The folding CA maps negative positions onto positive positions:
- Cell i (for i ≥ 0) holds a tuple: (value at pos i, value at pos -(i+1), isNegative flag)
- Position -1 folds to cell 0
- Position -2 folds to cell 1
- Position -k folds to cell k-1

**Folded layout for w = "abcde":**
```
cell:     0           1           2           3           4         │ border
        ──────────────────────────────────────────────────────────────┼────────
pos:     0 / -1      1 / -2      2 / -3      3 / -4      4 / -5     │  ...
        (a, a', ⊤)  (b, b', ⊤)  (c, c', ⊥)  (d, d', ⊥)  (e, e', ⊥) │ (#, #, ⊥)
              │           │           │           │           │
              └── marked ─┘           └────── unmarked ───────┘
```

Where a', b', c', d', e' are the mirrored copies of w (same content, but on negative side).

**Advice:** Marks positions 0..2^(ceil(log₂|w|) - 2) - 1
- For n=5: ceil(log₂5) = 3, so mark positions 0..2^(3-2)-1 = 0..1 (2 positions)
- These 2 marked cells × 4 = 8 = m x's ✓

---

## Step 2: Interpretation for Compression

On the **negative side** (the folded part):
- **Marked cell** (isNegative=⊤) → represents (x x x x) — 4 x's packed into one
- **Unmarked cell** (isNegative=⊥) → represents (# # # #) — 4 #'s packed into one  
- **Border** (beyond |w|) → represents (# # # #)

So the negative side of the folded configuration looks like:
```
folded cell:   0         1         2         3         4       │ border
              ─────────────────────────────────────────────────┼─────────
neg side:    (xxxx)    (xxxx)    (####)    (####)    (####)   │ (####)
              marked    marked   unmarked  unmarked  unmarked │
```

This is exactly the compressed configuration for `spec`!
- m/4 = 8/4 = 2 compressed cells of (x x x x)
- Rest are (# # # #)

---

## Step 3: Relating to the Original Execution

The original CA C accepts x^m w at position 0, time m+n.

In the folded+compressed view:
- The positive side runs the CA on w directly
- The negative side (folded onto positive) runs the compressed version

The spec theorem tells us:
```
C'.comp(compress c, t, i)[j] = C_orig.comp(c, τ(t,i,j), ψ(i,j))
```
where ψ(i,j) = 4i + j and τ(t,i,j) = t + 3|i| - j (in diagonal regime)

**Key insight:** At the fold boundary (cell 0), the negative side at time t=n contains information from original time τ(n, -1, 0) = n + 3 - 0 = n + 3... 

Wait, let me think about this more carefully. The folded cell 0 contains position -1 on the negative side. In compressed coordinates, this is i' = 0 for the first compressed cell (since -1 to -4 map to compressed cell -1, but we fold differently).

Actually, with the folding:
- Folded cell 0 holds position -1 → compressed cell ⌈-1/4⌉ = -1 (first x-cell)
- Folded cell 1 holds position -2 → compressed cell ⌈-2/4⌉ = -1 (same x-cell)
- ...
- Folded cell 3 holds position -4 → compressed cell ⌈-4/4⌉ = -1
- Folded cell 4 holds position -5 → compressed cell ⌈-5/4⌉ = -2

Hmm, this doesn't quite line up. Let me reconsider...

Actually, I think the folding + advice marking directly gives us the compressed spatial cells:
- Folded cell i on negative side = compressed spatial cell at position -(i+1)
- Each such cell holds 4 values (the Fin 4 → Q tuple)

But with the folding, we only have 1 slot per folded cell, not 4. So perhaps the compression happens differently...

