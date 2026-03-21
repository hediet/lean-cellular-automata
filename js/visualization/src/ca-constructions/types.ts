// Core CA types matching Lean definitions

export interface CellAutomaton<Q, Alpha, Beta> {
	readonly border: Q;
	readonly embed: (a: Alpha | undefined) => Q;
	readonly delta: (left: Q, center: Q, right: Q) => Q;
	readonly project: (q: Q) => Beta;
}

export type CA<Q, A, B> = CellAutomaton<Q, A, B>;

// Unit type (matching Lean's Unit?)
export type Unit = null;
export const unit: Unit = null;

// Option type (matching Lean's Option)
export type Option<T> = T | null;

// Triple (Fin 3 → T)
export type Triple<T> = readonly [T, T, T];

export function triple<T>(a: T, b: T, c: T): Triple<T> {
	return [a, b, c];
}

// Configuration: maps integer positions to states
export class Config<Q> {
	constructor(
		readonly cells: ReadonlyMap<number, Q>,
		readonly border: Q
	) {}

	get(i: number): Q {
		return this.cells.get(i) ?? this.border;
	}

	static fromWord<Q, Alpha>(
		ca: CA<Q, Alpha, unknown>,
		word: Alpha[]
	): Config<Q> {
		const cells = new Map<number, Q>();
		for (let i = 0; i < word.length; i++) {
			cells.set(i, ca.embed(word[i]));
		}
		return new Config(cells, ca.border);
	}
}

// Compute next configuration
export function next<Q, A, B>(
	ca: CA<Q, A, B>,
	config: Config<Q>
): Config<Q> {
	const cells = new Map<number, Q>();
	const [lo, hi] = activeBounds(config);
	for (let i = lo - 1; i <= hi + 1; i++) {
		const q = ca.delta(config.get(i - 1), config.get(i), config.get(i + 1));
		if (!eqState(q, ca.border)) {
			cells.set(i, q);
		}
	}
	return new Config(cells, ca.border);
}

function activeBounds<Q>(config: Config<Q>): [number, number] {
	let lo = 0;
	let hi = -1;
	for (const k of config.cells.keys()) {
		if (hi < lo) {
			lo = k;
			hi = k;
		} else {
			if (k < lo) lo = k;
			if (k > hi) hi = k;
		}
	}
	return [lo, hi];
}

// Simple equality for states (works for primitives and objects with type tags)
export function eqState<Q>(a: Q, b: Q): boolean {
	if (a === b) return true;
	if (typeof a === 'object' && typeof b === 'object' && a !== null && b !== null) {
		return JSON.stringify(a) === JSON.stringify(b);
	}
	return false;
}

// Run CA for t steps, returning all configurations
export function runCA<Q, A, B>(
	ca: CA<Q, A, B>,
	word: A[],
	steps: number
): Config<Q>[] {
	const configs: Config<Q>[] = [];
	let c = Config.fromWord(ca, word);
	configs.push(c);
	for (let t = 0; t < steps; t++) {
		c = next(ca, c);
		configs.push(c);
	}
	return configs;
}

// Compute trace at position 0 (real-time output sequence)
export function trace<Q, A, B>(
	ca: CA<Q, A, B>,
	word: A[],
	maxT: number
): B[] {
	const result: B[] = [];
	let c = Config.fromWord(ca, word);
	for (let t = 0; t <= maxT; t++) {
		result.push(ca.project(c.get(0)));
		c = next(ca, c);
	}
	return result;
}

// Real-time trace: outputs for t = 0, 1, ..., |w|-1
export function traceRt<Q, A, B>(
	ca: CA<Q, A, B>,
	word: A[]
): B[] {
	return trace(ca, word, word.length - 1);
}

// Space-time diagram: compute state at (position, time)
export function comp<Q, A, B>(
	ca: CA<Q, A, B>,
	word: A[],
	t: number,
	p: number
): B {
	let config = Config.fromWord(ca, word);
	for (let step = 0; step < t; step++) {
		config = next(ca, config);
	}
	return ca.project(config.get(p));
}

// Get internal state (not projected) at (position, time)
export function nextt<Q, A, B>(
	ca: CA<Q, A, B>,
	word: A[],
	t: number,
	p: number
): Q {
	let config = Config.fromWord(ca, word);
	for (let step = 0; step < t; step++) {
		config = next(ca, config);
	}
	return config.get(p);
}
