// Basic CA combinators: flip, product, mapProject

import { CA } from './types';

// Flip: swap left and right neighbors
export function flip<Q, A, B>(ca: CA<Q, A, B>): CA<Q, A, B> {
	return {
		border: ca.border,
		delta: (l, c, r) => ca.delta(r, c, l),
		embed: ca.embed,
		project: ca.project,
	};
}

// Product: run two CAs in parallel on the same input
export interface ProdState<Q1, Q2> {
	readonly fst: Q1;
	readonly snd: Q2;
}

export function product<Q1, Q2, A, B1, B2>(
	ca1: CA<Q1, A, B1>,
	ca2: CA<Q2, A, B2>
): CA<ProdState<Q1, Q2>, A, readonly [B1, B2]> {
	return {
		border: { fst: ca1.border, snd: ca2.border },
		delta: (l, c, r) => ({
			fst: ca1.delta(l.fst, c.fst, r.fst),
			snd: ca2.delta(l.snd, c.snd, r.snd),
		}),
		embed: (a) => ({
			fst: ca1.embed(a),
			snd: ca2.embed(a),
		}),
		project: (q) => [ca1.project(q.fst), ca2.project(q.snd)] as const,
	};
}

// Triple product (for 3 CAs)
export interface TripleProdState<Q1, Q2, Q3> {
	readonly fst: Q1;
	readonly snd: Q2;
	readonly thd: Q3;
}

export function product3<Q1, Q2, Q3, A, B1, B2, B3>(
	ca1: CA<Q1, A, B1>,
	ca2: CA<Q2, A, B2>,
	ca3: CA<Q3, A, B3>
): CA<TripleProdState<Q1, Q2, Q3>, A, readonly [B1, B2, B3]> {
	return {
		border: { fst: ca1.border, snd: ca2.border, thd: ca3.border },
		delta: (l, c, r) => ({
			fst: ca1.delta(l.fst, c.fst, r.fst),
			snd: ca2.delta(l.snd, c.snd, r.snd),
			thd: ca3.delta(l.thd, c.thd, r.thd),
		}),
		embed: (a) => ({
			fst: ca1.embed(a),
			snd: ca2.embed(a),
			thd: ca3.embed(a),
		}),
		project: (q) => [ca1.project(q.fst), ca2.project(q.snd), ca3.project(q.thd)] as const,
	};
}

// Map project: transform output type
export function mapProject<Q, A, B, C>(
	ca: CA<Q, A, B>,
	f: (b: B) => C
): CA<Q, A, C> {
	return {
		border: ca.border,
		delta: ca.delta,
		embed: ca.embed,
		project: (q) => f(ca.project(q)),
	};
}

// Identity CA: just passes through the input
export function idCA<A>(): CA<A | undefined, A, A | undefined> {
	return {
		border: undefined,
		delta: (_l, c, _r) => c,
		embed: (a) => a,
		project: (q) => q,
	};
}
