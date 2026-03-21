// Conversion constructions: RegularToLeftIndep, LeftIndepToRegular
// Source: CellularAutomatas/proofs/constructions/left_indep_from_regular.lean
//         CellularAutomatas/proofs/constructions/left_indep_to_regular.lean

import { CA, eqState } from './types';

// ============================================================================
// RegularToLeftIndep: Regular CA → Left-Independent CA
// ============================================================================
//
// Given any CA C, construct left-independent C' where:
//   Δ^t_{C'}(c)_i = Δ^{t/2}_C(c)_{i+t/2}     (if t even)
//                 = (Δ^{(t-1)/2}_C, Δ^{(t-1)/2}_C)_{i+(t-1)/2, i+(t+1)/2}  (if t odd)
//
// Q' = single(q) | pair(q₁, q₂) | dead
// δ'(_, b, c) = pair(b, c)           when b, c are singles
// δ'(_, pair(b₁,b₂), pair(_,c₂)) = single(δ(b₁, b₂, c₂))  when inputs are pairs

export type RegularToLeftIndepState<Q> =
	| { readonly type: 'single'; readonly q: Q }
	| { readonly type: 'pair'; readonly q1: Q; readonly q2: Q }
	| { readonly type: 'dead' };

function single<Q>(q: Q): RegularToLeftIndepState<Q> {
	return { type: 'single', q };
}

function pair<Q>(q1: Q, q2: Q): RegularToLeftIndepState<Q> {
	return { type: 'pair', q1, q2 };
}

const dead: RegularToLeftIndepState<never> = { type: 'dead' };

// Output type: matches BetaUnionSq in Lean
export type BetaUnionSq<B> =
	| { readonly type: 'single'; readonly b: B }
	| { readonly type: 'pair'; readonly b1: B; readonly b2: B };

export function regularToLeftIndep<Q, A, B>(
	ca: CA<Q, A, B>,
	defaultB: B  // Default output for dead state
): CA<RegularToLeftIndepState<Q>, A, BetaUnionSq<B>> {
	const borderState: RegularToLeftIndepState<Q> = dead;

	return {
		border: borderState,

		delta: (_l, c, r): RegularToLeftIndepState<Q> => {
			// Quiescent border: δ'(_, dead, dead) = dead
			if (c.type === 'dead' && r.type === 'dead') {
				return dead;
			}
			// single, single → pair
			if (c.type === 'single' && r.type === 'single') {
				return pair(c.q, r.q);
			}
			// pair, pair → single(δ(b₁, b₂, c₂))
			if (c.type === 'pair' && r.type === 'pair') {
				return single(ca.delta(c.q1, c.q2, r.q2));
			}
			// Invalid transitions go to dead state
			return dead;
		},

		embed: (a) => single(ca.embed(a)),

		project: (q): BetaUnionSq<B> => {
			switch (q.type) {
				case 'single':
					return { type: 'single', b: ca.project(q.q) };
				case 'pair':
					return { type: 'pair', b1: ca.project(q.q1), b2: ca.project(q.q2) };
				case 'dead':
					return { type: 'single', b: defaultB };
			}
		},
	};
}

// ============================================================================
// LeftIndepToRegular: Left-Independent CA → Regular CA
// ============================================================================
//
// Given left-independent CA C, construct C' such that:
//   Δ^t_{C'}(c)_i = Δ^{2t}_C(c)_{i-t}
//
// Key idea: Since C is left-independent, δ(a,b,c) = δ(q,b,c) for any q.
// Define δ'(a,b,c) := δ(_, δ(_, a, b), δ(_, b, c))
// This computes TWO steps of C in ONE step of C', shifting right by 1.

export function leftIndepToRegular<Q, A, B>(
	ca: CA<Q, A, B>
): CA<Q, A, B> {
	// δ'(a,b,c) = δ(a, δ(a, a, b), δ(a, b, c))
	// Since CA is left-independent, the first argument to δ doesn't matter,
	// so we use 'a' consistently (could be any value)
	const deltaPrime = (a: Q, b: Q, c: Q): Q => {
		const left = ca.delta(a, a, b);  // δ(_, a, b)
		const right = ca.delta(a, b, c); // δ(_, b, c)
		return ca.delta(a, left, right); // δ(_, left, right)
	};

	return {
		border: ca.border,
		delta: deltaPrime,
		embed: ca.embed,
		project: ca.project,
	};
}

// ============================================================================
// Helper: check if a CA appears left-independent (runtime check)
// ============================================================================

export function checkLeftIndependent<Q, A, B>(
	ca: CA<Q, A, B>,
	sampleStates: Q[]
): boolean {
	// Check δ(a, b, c) = δ(a', b, c) for all combinations from sample
	for (const b of sampleStates) {
		for (const c of sampleStates) {
			let firstResult: Q | null = null;
			for (const a of sampleStates) {
				const result = ca.delta(a, b, c);
				if (firstResult === null) {
					firstResult = result;
				} else if (!eqState(result, firstResult)) {
					return false;
				}
			}
		}
	}
	return true;
}
