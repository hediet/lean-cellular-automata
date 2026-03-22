# LT-Closed Advices and the L(lt) = L(rt) Question

## Definitions

### Reverse advice

```
Advice.rev : Advice α α
Advice.rev.f w = w.reverse
```

### LT-closed (by analogy with RT-closed)

```
Advice.weak_lt_closed f := ℒ(CA_lt(α × Γ) + f) = ℒ(CA_lt(α))
Advice.lt_closed f := ∀ S [Alphabet S], (f.lift S).weak_lt_closed
```

### L(rt-rev)

The language class of real-time CAs reading reversed input:

```
CA_rt_rev α := { L^R | L ∈ ℒ(CA_rt α) }
```

Equivalently, `ℒ(CAr_rt α)` (right-reading real-time CAs).

## Main Result

The following three conditions are equivalent:

**(A)** `ℒ(CA_lt α) = ℒ(CA_rt α)`

**(B)** `ℒ(CA_rt α) = CA_rt_rev α` (i.e., ℒ(CA_rt) is closed under reversal)

**(C)** `Advice.rev.weak_rt_closed` (the reverse advice is weak-RT-closed)

### Proof sketch: (A) ⟹ (B)

ℒ(CA_lt) is closed under reversal: given C ∈ CA_lt, flipping the
transition function spatially gives C' ∈ CA_lt with L(C') = L(C)^R.
If ℒ(lt) = ℒ(rt), then ℒ(rt) inherits closure under reversal.

### Proof sketch: (B) ⟹ (A)

This is the classical hard direction.

1. If ℒ(CA_rt) is closed under reversal, then ℒ(CAr_rt) = ℒ(CA_rt).
2. Given C ∈ CA_2n (a 2n-time CA reading at position 0), we can decompose
   its computation: the first n steps depend on w[0..n] (left-to-right),
   and the next n steps integrate information from w[n..2n] (right-to-left).
3. Build C₁ ∈ CA_rt that computes the left-to-right phase, and
   C₂ ∈ CAr_rt that computes the right-to-left phase.
4. By step 1, C₂ ∈ ℒ(CA_rt). Combining C₁ and C₂ as a product CA
   (which is still real-time with the reverse advice), we get
   ℒ(CA_2n) ⊆ ℒ(CA_rt + rev).
5. But rev is RT-closed (by assumption via (B) ⟹ (C) ⟹ weak_rt_closed),
   so ℒ(CA_rt + rev) = ℒ(CA_rt).
6. Together with ℒ(CA_lt) = ℒ(CA_2n) (linear-time speed-up theorem), we
   get ℒ(CA_lt) = ℒ(CA_rt).

### Proof sketch: (B) ⟺ (C)

**(C) ⟹ (B):** Given L ∈ ℒ(CA_rt) via C, build C' ∈ CA_rt(α × α) that
ignores the first component of its input and runs C on the second
component (which is rev(w)). Then {w | C' accepts w ⊗ rev(w)} = L^R.
By weak_rt_closed of rev, L^R ∈ ℒ(CA_rt).

**(B) ⟹ (C):** Given C ∈ CA_rt(α × α), the language
{w | C accepts w ⊗ rev(w)} is recognized by a CA that reads both forward
and backward. The forward part is real-time; the backward part is a
right-reading real-time CA. By (B), the backward component belongs to
ℒ(CA_rt). Their product CA_2n can be simulated in linear time, and
by (B) ⟹ (A), ℒ(CA_lt) = ℒ(CA_rt), so the result is in ℒ(CA_rt).

## Other LT-Closed Advices

### Compress-by-k advice

```
Advice.compress (k : ℕ) : Advice α (Fin k → α)
(Advice.compress k).f w i = (w[k*i], w[k*i+1], ..., w[k*i+k-1])
```

This packs k consecutive symbols into one. A CA_rt on the compressed word
of length ⌊n/k⌋ simulates k steps per original step, giving effective
time ~kn. So compress-by-k is lt-closed.

If compress-by-k were rt-closed for any k ≥ 2, then ℒ(kn) ⊆ ℒ(rt),
giving ℒ(lt) = ℒ(rt).

## Dependencies

The (B) ⟹ (A) direction depends on:
- `ca_linear_time_eq_2n : ℒ(CA_lt α) = ℒ(CA_2n α)` (currently sorry)
- Spatial flip preserves ℒ(CA_lt) (straightforward construction)
- Product CA construction for combining left/right reading CAs

## Formalization Plan

### Provable now (no sorry dependencies)

1. Define `Advice.rev`, `Advice.weak_lt_closed`, `Advice.lt_closed`
2. Prove (C) ⟹ (B): `Advice.rev.weak_rt_closed → ℒ(CA_rt) = CA_rt_rev`
3. Prove (A) ⟹ (B): `ℒ(CA_lt) = ℒ(CA_rt) → ℒ(CA_rt) = CA_rt_rev`
   (via spatial flip construction)

### Requires `ca_linear_time_eq_2n`

4. Prove (B) ⟹ (A): The hard classical direction
5. State the full equivalence (A) ⟺ (B) ⟺ (C)

### Open questions (reformulated)

```
open_question_rev_rt_closed : Advice.rev.rt_closed
-- Equivalent to: ℒ(CA_lt) = ℒ(CA_rt)
```
