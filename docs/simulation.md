# Local Simulation of Cellular Automata

## Setup

Let $C_\mathrm{sim} = (Q_\mathrm{sim}, \delta_\mathrm{sim})$ and $C = (Q, \delta)$ be cellular automata of radius $1$, with transition functions $\delta_\mathrm{sim} : Q_\mathrm{sim}^{3} \to Q_\mathrm{sim}$ and $\delta : Q^{3} \to Q$.

For an input $w \in \alpha^{*}$ (with some initialisation $\alpha \to Q_\mathrm{sim}$) and an input $v \in \beta^{*}$ (with some initialisation $\beta \to Q$), define the spacetime diagrams
$$D_\mathrm{sim} := D(C_\mathrm{sim}, w) : \mathbb{Z} \times \mathbb{N} \to Q_\mathrm{sim} \qquad \text{and} \qquad D := D(C, v) : \mathbb{Z} \times \mathbb{N} \to Q.$$

Coordinates in $D_\mathrm{sim}$ use subscript $\mathrm{s}$: $(x_\mathrm{s}, t_\mathrm{s})$; coordinates in $D$ are plain: $(x, t)$.

## Local-past relation

On triples $(x_\mathrm{s}, t_\mathrm{s}, j) \in \mathbb{Z} \times \mathbb{N} \times \mathrm{Fin}\,J$, define
$$(x_\mathrm{s}', t_\mathrm{s}', j') \;\prec\; (x_\mathrm{s}, t_\mathrm{s}, j) \quad :\Longleftrightarrow\quad \Bigl[\,(x_\mathrm{s}', t_\mathrm{s}') = (x_\mathrm{s}, t_\mathrm{s})\ \text{and}\ j' < j\,\Bigr] \;\;\lor\;\; \Bigl[\,t_\mathrm{s}' = t_\mathrm{s} - 1\ \text{and}\ |x_\mathrm{s}' - x_\mathrm{s}| \le 1\,\Bigr].$$

This relation is well-founded (lexicographic on $(t_\mathrm{s}, j)$) and has a natural interpretation: $(x_\mathrm{s}', t_\mathrm{s}', j')$ is reachable from $(x_\mathrm{s}, t_\mathrm{s}, j)$ via a single step into either an earlier slot of the same $C_\mathrm{sim}$-cell or one of its three $C_\mathrm{sim}$-parents.

## Definition

$C_\mathrm{sim}$ *locally simulates* $C$ on inputs $(w, v)$ at target $(p_\mathrm{s}, p) \in (\mathbb{Z} \times \mathbb{N})^{2}$ if there exist constants $K, J \in \mathbb{N}_{\ge 1}$, a **decoder palette**
$$\Pi \;=\; \bigl\{\, \pi_k : Q_\mathrm{sim}^{3} \to Q \,\bigr\}_{k \in \mathrm{Fin}\,K},$$
and a **locator**
$$\mathcal{L} \;:\; \alpha^{*} \,\times\, \mathbb{Z} \,\times\, \mathbb{N} \,\times\, \mathrm{Fin}\,J \;\longrightarrow\; \mathrm{Option}\!\bigl(\mathbb{Z} \,\times\, \mathbb{N} \,\times\, \mathrm{Fin}\,K\bigr),$$
such that the following three conditions hold.

### (S) Soundness

For every $(x_\mathrm{s}, t_\mathrm{s}, j)$ with $\mathcal{L}(w,\, x_\mathrm{s},\, t_\mathrm{s},\, j) = \mathrm{some}\,(x, t, k)$,
$$\pi_k\!\bigl(D(C_\mathrm{sim}, w)(x_\mathrm{s} - 1,\, t_\mathrm{s} - 1),\; D(C_\mathrm{sim}, w)(x_\mathrm{s},\, t_\mathrm{s} - 1),\; D(C_\mathrm{sim}, w)(x_\mathrm{s} + 1,\, t_\mathrm{s} - 1)\bigr) \;=\; D(C, v)(x,\, t).$$

### (P) Pointed coverage

$$\mathcal{L}(w,\, p_\mathrm{s},\, J - 1) \;=\; \mathrm{some}\,(p,\, k_\mathrm{out}) \qquad \text{for some } k_\mathrm{out} \in \mathrm{Fin}\,K.$$

### (L) Past-cone locality

For every $(x_\mathrm{s}, t_\mathrm{s}, j)$ with $\mathcal{L}(w,\, x_\mathrm{s},\, t_\mathrm{s},\, j) = \mathrm{some}\,(x, t, k)$ and $t \ge 1$, at least one of the following holds:

**(L1)** For every $x'$ with $|x' - x| \le 1$, there exist $(x_\mathrm{s}', t_\mathrm{s}', j') \prec (x_\mathrm{s}, t_\mathrm{s}, j)$ and $k' \in \mathrm{Fin}\,K$ such that
$$\mathcal{L}(w,\, x_\mathrm{s}',\, t_\mathrm{s}',\, j') \;=\; \mathrm{some}\,(x',\, t - 1,\, k').$$

**(L2)** There exist $(x_\mathrm{s}', t_\mathrm{s}', j') \prec (x_\mathrm{s}, t_\mathrm{s}, j)$ and $k' \in \mathrm{Fin}\,K$ such that
$$\mathcal{L}(w,\, x_\mathrm{s}',\, t_\mathrm{s}',\, j') \;=\; \mathrm{some}\,(x,\, t,\, k').$$

## Remarks

- The locator is a partial function (via `Option`); each $C_\mathrm{sim}$-cell has up to $J$ independent decoding slots.
- **(S)** says every realised slot correctly decodes the $C$-cell it points to.
- **(P)** fixes a single obligation — the target — from which the recursion starts.
- **(L)** propagates the obligation: every $C$-parent of a located $C$-cell must be located somewhere in the local past (same cell, earlier slot; or $C_\mathrm{sim}$-parent cell, any slot). Well-foundedness of $\prec$ terminates the recursion at the $C_\mathrm{sim}$-initial row.
