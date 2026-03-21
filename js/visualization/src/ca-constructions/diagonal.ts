// Diagonal signal constructions
// Source: CellularAutomatas/proofs/constructions/composition/diag.lean
//
// DiagLeft: Fires at p ≤ 0 at time t = 3 + 2*|p|
// DiagRight: Fires at p ≥ 0 at time t = 3 + 2*p
//
// These are used as control signals in the composition pipeline.

import { CA, Unit, unit } from './types';

// ============================================================================
// DiagLeft: Diagonal signal propagating to the left
// ============================================================================
//
// States:
// - idle: waiting
// - fire: firing this step (output = true)
// - hold: fired, now holding to signal left neighbor
//
// Execution (for input [()]):
//   Time   Position
//   (t)    -3 -2 -1  0  1
//   ----------------------
//    0      .  .  .  F  .   <- Cell 0 fires (input)
//    1      .  .  .  H  .   <- Cell 0 holds
//    2      .  .  F  .  .   <- Cell -1 fires
//    3      .  .  H  .  .
//    4      .  F  .  .  .   <- Cell -2 fires
//    ...
//    t=2|p| fires at position p

export type DiagQ = 'idle' | 'fire' | 'hold';

export const diagLeftCore: CA<DiagQ, Unit, boolean> = {
	border: 'idle',

	delta: (_l, c, r): DiagQ => {
		switch (c) {
			case 'fire': return 'hold';
			case 'hold': return 'idle';
			case 'idle': return r === 'hold' ? 'fire' : 'idle';
		}
	},

	embed: (a) => a !== undefined ? 'fire' : 'idle',

	project: (q) => q === 'fire',
};

// DiagRight is the flip of DiagLeft (swap left/right in delta)
export const diagRightCore: CA<DiagQ, Unit, boolean> = {
	border: 'idle',

	delta: (l, c, _r): DiagQ => {
		switch (c) {
			case 'fire': return 'hold';
			case 'hold': return 'idle';
			case 'idle': return l === 'hold' ? 'fire' : 'idle';
		}
	},

	embed: (a) => a !== undefined ? 'fire' : 'idle',

	project: (q) => q === 'fire',
};

// ============================================================================
// Full diagonal signals with proper timing (fires at t = 3 + 2*|p|)
// ============================================================================
//
// The full diag_left/diag_right combine:
// 1. leftEdgeCA: Marks the left edge (position 0) for 1 step
// 2. idCA: Identity for 2 steps (delay)
// 3. diagLeftCore/diagRightCore: The actual diagonal signal
//
// Result: fires at position p, time 3 + 2*|p|

// State for the full diagonal signal CA
export interface DiagState {
	readonly phase: 'init' | 'delay1' | 'delay2' | 'running';
	readonly q: DiagQ;
}

function makeDiagSignal(direction: 'left' | 'right'): CA<DiagState, Unit, boolean> {
	const core = direction === 'left' ? diagLeftCore : diagRightCore;

	return {
		border: { phase: 'init', q: 'idle' },

		delta: (l, c, r): DiagState => {
			// Phases:
			// init → delay1 → delay2 → running
			// This adds 3 steps of delay before the diagonal starts

			switch (c.phase) {
				case 'init':
					// At t=0, embed sets phase='init'. After step 1, enter delay1.
					return { phase: 'delay1', q: c.q };

				case 'delay1':
					return { phase: 'delay2', q: c.q };

				case 'delay2':
					// Transition to running, start the diagonal logic
					return { phase: 'running', q: c.q };

				case 'running':
					// Apply the core diagonal transition
					const newQ = core.delta(l.q, c.q, r.q);
					return { phase: 'running', q: newQ };
			}
		},

		embed: (a): DiagState => {
			// Only position 0 gets the trigger
			if (a !== undefined) {
				return { phase: 'init', q: 'fire' };
			}
			return { phase: 'init', q: 'idle' };
		},

		project: (s): boolean => {
			// Only output during running phase when firing
			return s.phase === 'running' && s.q === 'fire';
		},
	};
}

export const diagLeft = makeDiagSignal('left');
export const diagRight = makeDiagSignal('right');

// ============================================================================
// Generic diagonal signal for any input type
// ============================================================================
// Ignores the actual input values, only cares about presence at position 0

export function makeDiagLeftGeneric<A>(): CA<DiagState, A, boolean> {
	return {
		border: diagLeft.border,
		delta: diagLeft.delta,
		embed: (a) => diagLeft.embed(a !== undefined ? unit : undefined),
		project: diagLeft.project,
	};
}

export function makeDiagRightGeneric<A>(): CA<DiagState, A, boolean> {
	return {
		border: diagRight.border,
		delta: diagRight.delta,
		embed: (a) => diagRight.embed(a !== undefined ? unit : undefined),
		project: diagRight.project,
	};
}

// ============================================================================
// Spec verification: check that fires at correct times
// ============================================================================

export function diagFiringTime(p: number, direction: 'left' | 'right'): number | null {
	// diagLeft fires at p ≤ 0
	// diagRight fires at p ≥ 0
	// Both fire at t = 3 + 2*|p|

	if (direction === 'left' && p > 0) return null;
	if (direction === 'right' && p < 0) return null;

	return 3 + 2 * Math.abs(p);
}
