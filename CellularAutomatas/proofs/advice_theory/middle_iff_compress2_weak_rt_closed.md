# Human Proof: middle weak-rt-closed ↔ compress2 weak-rt-closed (unary alphabet)

## Core observation

Both `middle` and `compress2` over a unary word of length $n$ encode exactly one piece of
information: the value $\lfloor n/2 \rfloor$.

- **middle** encodes it as a single marker at position $\lfloor n/2 \rfloor - 1$.
- **compress2** encodes it as a step pattern: positions $i < \lfloor n/2 \rfloor$ get $(•,•)$,
  position $\lfloor n/2 \rfloor$ gets $(•,\varnothing)$ or $(\varnothing,\varnothing)$ depending
  on parity, and the rest get $(\varnothing,\varnothing)$.

## Key lemma (composition)

If $f_1$ is weak-rt-closed and $f_2$ is rt-closed, then $f_1 \circ f_2$ is weak-rt-closed.

## Two conversions

**$g$ : compress2-output → middle-output.**
Scan once right-to-left: mark the last position whose right neighbor is not $(•,•)$.
This is a one-pass FST (state = previous symbol), hence rt-closed.

**$h$ : middle-output → compress2-output.**
Given the marker position $m$ and the parity of $n$ (a uniform bit, also rt-computable),
produce the step pattern: $(•,•)$ for $i \le m$, $(•,\varnothing)$ at $i = m+1$ if $n$ is
odd, $(\varnothing,\varnothing)$ otherwise.
Again a one-pass right-to-left FST, hence rt-closed.

## Two factorizations

By direct inspection of the definitions:

$$\text{middle} = \text{compress2} \circ g$$

$$\text{compress2} = \text{middle} \circ (\text{id} \times \text{parity}) \circ h$$

## Conclusion

- **compress2 weak $\Rightarrow$ middle weak:**
  $\text{middle} = \text{compress2} \circ g$, $g$ is rt-closed → apply key lemma.

- **middle weak $\Rightarrow$ compress2 weak:**
  Composing `middle` with `parity` (rt-closed) is still weak-rt-closed by key lemma;
  composing further with $h$ (rt-closed) gives `compress2`, again by key lemma. $\square$
