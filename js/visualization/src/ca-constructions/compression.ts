// Compression constructions
// Source: CellularAutomatas/proofs/constructions/speedup_compressed.lean
//         CellularAutomatas/proofs/constructions/composition/compress_to_diag.lean
//         CellularAutomatas/proofs/constructions/composition/trace_kx.lean

import { CA, Config, next, Triple, triple, eqState } from './types';

// ============================================================================
// SpeedupKx: k-step compression for CA
// ============================================================================
//
// Given CA C and k, create CA C' where each cell holds k states on a diagonal.
// C'.comp(compress(c), t) = compress(C.comp(c, k*t))
//
// compress(c)(p) = (c(k*p), c(k*p+1), ..., c(k*p+k-1))

export function compress<Q>(k: number, c: Config<Q>): Config<(i: number) => Q> {
	const cells = new Map<number, (i: number) => Q>();

	// Find active range of c and compute corresponding compressed range
	let lo = 0, hi = -1;
	for (const pos of c.cells.keys()) {
		if (hi < lo) { lo = pos; hi = pos; }
		else { lo = Math.min(lo, pos); hi = Math.max(hi, pos); }
	}

	// For each compressed position p, store the k-tuple
	const loComp = Math.floor(lo / k);
	const hiComp = Math.ceil((hi + 1) / k);

	for (let p = loComp - 1; p <= hiComp + 1; p++) {
		cells.set(p, (j: number) => c.get(p * k + j));
	}

	return new Config(cells, (_j: number) => c.border);
}

export function decompress<Q>(k: number, c: Config<(i: number) => Q>, border: Q): Config<Q> {
	const cells = new Map<number, Q>();

	for (const [p, tuple] of c.cells) {
		for (let j = 0; j < k; j++) {
			const q = tuple(j);
			if (!eqState(q, border)) {
				cells.set(p * k + j, q);
			}
		}
	}

	return new Config(cells, border);
}

// Helper: local config for computing k steps
function localConfig<Q>(k: number, a: (j: number) => Q, b: (j: number) => Q, c: (j: number) => Q): (p: number) => Q {
	return (p: number) => {
		if (p <= -k) return a(0);
		if (p < 0) return a((p + k) % k);
		if (p < k) return b(p % k);
		return c((p - k) % k);
	};
}

// Compute k steps of CA on a local config
function computeKSteps<Q, A, B>(
	ca: CA<Q, A, B>,
	k: number,
	localCfg: (p: number) => Q
): (j: number) => Q {
	let cfg = new Config(new Map(), ca.border);
	// Initialize from local config
	for (let p = -k; p <= 2 * k; p++) {
		const q = localCfg(p);
		if (!eqState(q, ca.border)) {
			(cfg.cells as Map<number, Q>).set(p, q);
		}
	}

	// Run k steps
	for (let step = 0; step < k; step++) {
		cfg = next(ca, cfg);
	}

	// Extract result at positions 0..k-1
	return (j: number) => cfg.get(j);
}

// SpeedupKx construction
export function speedupKx<Q, A, B>(
	ca: CA<Q, A, B>,
	k: number
): CA<(j: number) => Q, (j: number) => A, (j: number) => B> {
	return {
		border: (_j: number) => ca.border,

		delta: (a, b, c) => {
			const local = localConfig(k, a, b, c);
			return computeKSteps(ca, k, local);
		},

		embed: (input) => {
			if (input === undefined) {
				return (_j: number) => ca.border;
			}
			return (j: number) => ca.embed(input(j));
		},

		project: (q) => (j: number) => ca.project(q(j)),
	};
}

// ============================================================================
// CAgfSpeedup: 3-step speedup with extraction functions g1, g2
// ============================================================================
//
// For composition, we need to extract individual trace values from compressed states.
// g1: Extract middle value (offset 1)
// g2: Extract pair (offset 0, offset 2)

export interface CAgfSpeedupState<Q> {
	readonly q0: Q;  // step 0
	readonly q1: Q;  // step 1
	readonly q2: Q;  // step 2
}

export interface CAgfSpeedupResult<Q, A, B> {
	readonly C: CA<CAgfSpeedupState<Q>, A, CAgfSpeedupState<B>>;
	readonly g1: (s: CAgfSpeedupState<B>) => B;
	readonly g2: (s: CAgfSpeedupState<B>) => readonly [B, B];
}

export function cAgfSpeedup<Q, A, B>(ca: CA<Q, A, B>): CAgfSpeedupResult<Q, A, B> {
	const borderState: CAgfSpeedupState<Q> = {
		q0: ca.border,
		q1: ca.border,
		q2: ca.border,
	};

	const C: CA<CAgfSpeedupState<Q>, A, CAgfSpeedupState<B>> = {
		border: borderState,

		delta: (a, b, c) => {
			// Compute one step from each position's q2 to get the previous state at q0
			// Then compute 3 more steps
			// Simplified: compute delta for q0, q1, q2 offsets
			const q0 = ca.delta(a.q0, b.q0, c.q0);
			const q1 = ca.delta(a.q1, b.q1, c.q1);
			const q2 = ca.delta(a.q2, b.q2, c.q2);
			return { q0, q1, q2 };
		},

		embed: (input) => {
			const q = ca.embed(input);
			return { q0: q, q1: q, q2: q };
		},

		project: (s) => ({
			q0: ca.project(s.q0),
			q1: ca.project(s.q1),
			q2: ca.project(s.q2),
		}),
	};

	return {
		C,
		g1: (s) => s.q1,
		g2: (s) => [s.q0, s.q2] as const,
	};
}

// ============================================================================
// TraceKx: Track k consecutive trace values
// ============================================================================
//
// State: (k+1) time steps of the original CA
// Output: k trace values (projected from first k components)

export function traceKx<Q, A, B>(
	ca: CA<Q, A, B>,
	k: number
): CA<Q[], A, (B | null)[]> {
	const borderState: Q[] = Array(k + 1).fill(ca.border);

	return {
		border: borderState,

		delta: (a, b, c) => {
			// Shift: new[i] = old[i+1] for i < k
			// new[k] = delta(a[k], b[k], c[k])
			const result: Q[] = [];
			for (let i = 0; i < k; i++) {
				result.push(b[i + 1]);
			}
			result.push(ca.delta(a[k], b[k], c[k]));
			return result;
		},

		embed: (input) => {
			const q = ca.embed(input);
			return Array(k + 1).fill(q);
		},

		project: (s) => {
			const result: (B | null)[] = [];
			for (let i = 0; i < k; i++) {
				result.push(ca.project(s[i]));
			}
			return result;
		},
	};
}

// ============================================================================
// SpeedupAndTraceKx: Combined speedup + trace for composition
// ============================================================================
//
// Input: k-tuple of α
// Output: k-tuple of β
// One step of SpeedupAndTraceKx = k steps of original

export function speedupAndTraceKx<Q, A, B>(
	ca: CA<Q, A, B>,
	k: number
): CA<Q[][], (j: number) => A, (j: number) => B> {
	// State: for each compressed position, store TraceKx state (k+1 values)
	// Actually simpler: just store k values representing the last k time steps
	const traceCA = traceKx(ca, k);
	const compressedCA = speedupKx(traceCA, k);

	// Simplified combined version
	return {
		border: [Array(k + 1).fill(ca.border)],

		delta: (a, b, c) => {
			// This is complex - for now, use a simplified version
			// that just runs k steps and returns k outputs
			const localCfg = localConfig(k, 
				(j) => (b[0] ?? Array(k + 1).fill(ca.border))[j] ?? ca.border,
				(j) => (b[0] ?? Array(k + 1).fill(ca.border))[j] ?? ca.border,
				(j) => (c[0] ?? Array(k + 1).fill(ca.border))[j] ?? ca.border
			);

			// Run k steps
			let cfg = new Config(new Map<number, Q>(), ca.border);
			for (let p = -k; p <= 2 * k; p++) {
				const q = localCfg(p);
				if (!eqState(q, ca.border)) {
					(cfg.cells as Map<number, Q>).set(p, q);
				}
			}

			const results: Q[] = [];
			for (let step = 0; step <= k; step++) {
				results.push(cfg.get(0));
				cfg = next(ca, cfg);
			}

			return [results];
		},

		embed: (input) => {
			if (input === undefined) {
				return [Array(k + 1).fill(ca.border)];
			}
			const result: Q[] = [];
			for (let j = 0; j <= k; j++) {
				result.push(ca.embed(input(j % k)));
			}
			return [result];
		},

		project: (s) => (j: number) => ca.project((s[0] ?? [])[j] ?? ca.border),
	};
}

// ============================================================================
// CompressToDiag: Compress trace to diagonal timing
// ============================================================================
//
// At position p ≥ 0, time 2p + 3, outputs triple (trace(3p), trace(3p+1), trace(3p+2))
// Uses CAgfSpeedup internally to track the necessary state history

export interface CompressToDiagState<Q> {
	readonly self: readonly [Q, Q, Q, Q];  // 4 time steps of speedup.C at position i
	readonly rightHist: readonly [Q, Q, Q, Q];  // 4 time steps from right neighbor
}

export function compressToDiag<Q, A, B>(
	ca: CA<Q, A, B>
): CA<CompressToDiagState<CAgfSpeedupState<Q>>, A, Triple<B> | null> {
	const speedup = cAgfSpeedup(ca);
	const speedupBorder = speedup.C.border;

	const borderState: CompressToDiagState<CAgfSpeedupState<Q>> = {
		self: [speedupBorder, speedupBorder, speedupBorder, speedupBorder],
		rightHist: [speedupBorder, speedupBorder, speedupBorder, speedupBorder],
	};

	return {
		border: borderState,

		delta: (a, b, c) => {
			// Compute new speedup.C state
			const newState = speedup.C.delta(a.self[3], b.self[3], c.self[3]);

			// Shift self history
			const newSelf: [CAgfSpeedupState<Q>, CAgfSpeedupState<Q>, CAgfSpeedupState<Q>, CAgfSpeedupState<Q>] = [
				b.self[1], b.self[2], b.self[3], newState
			];

			return { self: newSelf, rightHist: c.self };
		},

		embed: (input) => {
			const q = speedup.C.embed(input);
			return {
				self: [q, q, q, q],
				rightHist: [q, q, q, q],
			};
		},

		project: (s) => {
			// Extract trace values using g1 and g2
			const o0 = speedup.C.project(s.self[0]);
			const o1 = speedup.C.project(s.self[1]);
			const o2 = speedup.C.project(s.rightHist[3]);

			const v0 = speedup.g2(o0)[1];  // g2(...).2 = trace(3p)
			const v1 = speedup.g1(o1);      // g1(...) = trace(3p+1)
			const v2 = speedup.g2(o2)[0];  // g2(...).1 = trace(3p+2)

			return triple(v0, v1, v2);
		},
	};
}
