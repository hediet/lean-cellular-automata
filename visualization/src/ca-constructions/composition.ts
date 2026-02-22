// Composition pipeline constructions
// Source: CellularAutomatas/proofs/constructions/composition/compose_cart.lean
//         CellularAutomatas/proofs/constructions/composition/sim_from_lambda.lean
//         CellularAutomatas/proofs/constructions/composition/decompress_triple.lean

import { CA, Config, Triple, triple, eqState, next } from './types';
import { product, mapProject } from './basic';
import { makeDiagLeftGeneric, makeDiagRightGeneric, DiagState } from './diagonal';
import { compressToDiag, CompressToDiagState, CAgfSpeedupState } from './compression';

// ============================================================================
// AddBorder: Mark border cells explicitly
// ============================================================================
//
// Runs original CA in parallel with a border marker.
// Output: some(v) for non-border cells, null for border cells

export interface AddBorderState<Q> {
	readonly q: Q;
	readonly isBorder: boolean;
}

export function addBorder<Q, A, B>(
	ca: CA<Q, A, B>
): CA<AddBorderState<Q>, A, B | null> {
	return {
		border: { q: ca.border, isBorder: true },

		delta: (a, b, c) => ({
			q: ca.delta(a.q, b.q, c.q),
			isBorder: c.isBorder,  // Border propagates from right
		}),

		embed: (input) => ({
			q: ca.embed(input),
			isBorder: input === undefined,
		}),

		project: (s) => s.isBorder ? null : ca.project(s.q),
	};
}

// ============================================================================
// CompressToΛ: Full compression to control signal
// ============================================================================
//
// Combines:
// - CompressToDiag (data source)
// - DiagRight (fires at p ≥ 0)
// - DiagLeft (fires at p < 0)
//
// Output at time 3 + 2|p|:
// - For p ≥ 0: (trace(3p), trace(3p+1), trace(3p+2)) from data source
// - For p < 0: (null, null, null) placeholder

export interface CompressToLambdaState<Q> {
	readonly dataSource: CompressToDiagState<CAgfSpeedupState<Q>>;
	readonly diagRight: DiagState;
	readonly diagLeft: DiagState;
}

export function compressToLambda<Q, A, B>(
	ca: CA<Q, A, B | null>  // CA with nullable output (from addBorder)
): CA<CompressToLambdaState<Q>, A, Triple<B | null> | null> {
	const dataCA = compressToDiag(ca as CA<Q, A, B>);
	const diagRightCA = makeDiagRightGeneric<A>();
	const diagLeftCA = makeDiagLeftGeneric<A>();

	return {
		border: {
			dataSource: dataCA.border,
			diagRight: diagRightCA.border,
			diagLeft: diagLeftCA.border,
		},

		delta: (a, b, c) => ({
			dataSource: dataCA.delta(a.dataSource, b.dataSource, c.dataSource),
			diagRight: diagRightCA.delta(a.diagRight, b.diagRight, c.diagRight),
			diagLeft: diagLeftCA.delta(a.diagLeft, b.diagLeft, c.diagLeft),
		}),

		embed: (input) => ({
			dataSource: dataCA.embed(input),
			diagRight: diagRightCA.embed(input),
			diagLeft: diagLeftCA.embed(input),
		}),

		project: (s): Triple<B | null> | null => {
			const signalRight = diagRightCA.project(s.diagRight);
			const signalLeft = diagLeftCA.project(s.diagLeft);

			if (signalRight) {
				// p ≥ 0 on diagonal: use computed triple
				return dataCA.project(s.dataSource) as Triple<B | null> | null;
			} else if (signalLeft) {
				// p < 0 on diagonal: placeholder
				return triple(null, null, null);
			}
			// Not on diagonal
			return null;
		},
	};
}

// ============================================================================
// SimFromΛ: Simulation from Lambda Control Signal
// ============================================================================
//
// The core of the composition construction!
//
// C_ctl: Control CA that outputs triggers (from CompressToΛ)
// C_inr: Inner CA to simulate (from SpeedupAndTraceKx)
//
// State:
// - state: current control CA state
// - counter: 0, 1, 2 (phase counter)
// - sim: (current, previous) inner CA states, or null if not triggered yet

export interface SimFromLambdaState<Q_ctl, Q_inr> {
	readonly state: Q_ctl;
	readonly counter: 0 | 1 | 2;
	readonly sim: { readonly cur: Q_inr; readonly prev: Q_inr } | null;
}

// Default value for neighbors that aren't triggered yet
function getNeighborVal<Q_inr>(
	s: SimFromLambdaState<unknown, Q_inr>,
	defaultVal: Q_inr
): Q_inr {
	if (s.sim === null) return defaultVal;
	// At counter=1, use previous; otherwise use current
	return s.counter === 1 ? s.sim.prev : s.sim.cur;
}

export function simFromLambda<Q_ctl, Q_inr, A, B, C>(
	C_ctl: CA<Q_ctl, A, B | null>,  // Control CA (outputs trigger values)
	C_inr: CA<Q_inr, B, C>           // Inner CA to simulate
): CA<SimFromLambdaState<Q_ctl, Q_inr>, A, C | null> {
	const borderState: SimFromLambdaState<Q_ctl, Q_inr> = {
		state: C_ctl.border,
		counter: 0,
		sim: null,
	};

	return {
		border: borderState,

		delta: (a, b, c): SimFromLambdaState<Q_ctl, Q_inr> => {
			// Compute next control state
			const nextCtl = C_ctl.delta(a.state, b.state, c.state);
			const trigger = C_ctl.project(nextCtl);

			// Case 1: Trigger fires - initialize inner simulation
			if (trigger !== null) {
				const initState = C_inr.embed(trigger);
				return {
					state: nextCtl,
					counter: 0,
					sim: { cur: initState, prev: initState },
				};
			}

			// Case 2: No trigger and no active simulation
			if (b.sim === null) {
				return {
					state: nextCtl,
					counter: 0,
					sim: null,
				};
			}

			// Case 3: Active simulation - check if it's compute time
			if (b.counter === 2) {
				// Time to compute next inner CA step
				const valA = getNeighborVal(a, C_inr.border);
				const valC = getNeighborVal(c, C_inr.border);
				const nextVal = C_inr.delta(valA, b.sim.cur, valC);
				return {
					state: nextCtl,
					counter: 0,
					sim: { cur: nextVal, prev: b.sim.cur },
				};
			}

			// Case 4: Just increment counter
			return {
				state: nextCtl,
				counter: (b.counter + 1) as 0 | 1 | 2,
				sim: b.sim,
			};
		},

		embed: (input) => ({
			state: C_ctl.embed(input),
			counter: 0,
			sim: null,
		}),

		project: (s): C | null => {
			// Only output when counter = 0 and simulation is active
			if (s.counter === 0 && s.sim !== null) {
				return C_inr.project(s.sim.cur);
			}
			return null;
		},
	};
}

// ============================================================================
// DecompressTriple: Unpack triples to individual values
// ============================================================================
//
// Takes a CA outputting Triple<B> | null every 3rd step.
// At time 3t₁ + t₂ + k, outputs element t₂ from the triple at time 3t₁ + k.

export interface DecompressTripleState<Q, B> {
	readonly q: Q;
	readonly counter: 0 | 1 | 2;
	readonly stored: Triple<B>;
}

export function decompressTriple<Q, A, B>(
	ca: CA<Q, A, Triple<B> | null>,
	defaultB: B
): CA<DecompressTripleState<Q, B>, A, B> {
	const defaultTriple: Triple<B> = triple(defaultB, defaultB, defaultB);

	return {
		border: {
			q: ca.border,
			counter: 0,
			stored: defaultTriple,
		},

		delta: (a, b, c): DecompressTripleState<Q, B> => {
			const nextQ = ca.delta(a.q, b.q, c.q);
			const output = ca.project(nextQ);

			if (output !== null) {
				// New triple arrived - reset counter and store it
				return {
					q: nextQ,
					counter: 0,
					stored: output,
				};
			}

			// No new triple - increment counter
			return {
				q: nextQ,
				counter: ((b.counter + 1) % 3) as 0 | 1 | 2,
				stored: b.stored,
			};
		},

		embed: (input) => ({
			q: ca.embed(input),
			counter: 0,
			stored: defaultTriple,
		}),

		project: (s): B => {
			// Return element at current counter position
			return s.stored[s.counter];
		},
	};
}

// ============================================================================
// Helper: Simple inner CA for testing (rule 1 + (l + c + r) % 7)
// ============================================================================

export const simpleInnerCA: CA<number, number, number> = {
	border: 0,
	delta: (l, c, r) => {
		if (l === 0 && c === 0 && r === 0) return 0;
		return 1 + ((l + c + r) % 7);
	},
	embed: (a) => a ?? 0,
	project: (q) => q,
};

// Speedup version: runs 3 steps per step, outputs triple
// Input: Triple<number | null> (3 input values)
// Output: Triple<number> (3 output values)
export function simpleInnerCA3x(): CA<number[], Triple<number | null>, Triple<number>> {
	return {
		border: [0, 0, 0, 0],  // Store last 4 states for computing 3 steps

		delta: (a, b, c) => {
			// Compute 3 steps
			const delta3 = simpleInnerCA.delta;
			const q0 = delta3(a[3], b[3], c[3]);
			const q1 = delta3(a[2], b[2], c[2]);  // Actually need to track properly
			const q2 = delta3(a[1], b[1], c[1]);
			// Shift and add
			return [b[1], b[2], b[3], q0];
		},

		embed: (input) => {
			if (input === undefined) return [0, 0, 0, 0];
			// input is a Triple<number | null>
			const q = input[1] ?? 0;  // Get middle element as init
			return [q, q, q, q];
		},

		project: (s) => triple(s[1], s[2], s[3]),
	};
}
