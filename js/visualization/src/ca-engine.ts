// A 1D cellular automaton over a finite state type Q.
// δ(left, center, right) → new state.
// embed maps input symbols to Q, project maps Q to output symbols.
// border is the quiescent boundary state.
export interface CellAutomaton<Q, Alpha, Beta> {
	readonly border: Q;
	readonly delta: (left: Q, center: Q, right: Q) => Q;
	readonly embed: (a: Alpha | undefined) => Q;
	readonly project: (q: Q) => Beta;
}

// A configuration is a function from integer positions to states.
// We represent it as a finite map with a default border value.
export class Config<Q> {
	constructor(
		readonly cells: ReadonlyMap<number, Q>,
		readonly border: Q
	) {}

	get(i: number): Q {
		return this.cells.get(i) ?? this.border;
	}

	static fromWord<Q, Alpha>(
		ca: CellAutomaton<Q, Alpha, unknown>,
		word: Alpha[]
	): Config<Q> {
		const cells = new Map<number, Q>();
		for (let i = 0; i < word.length; i++) {
			cells.set(i, ca.embed(word[i]));
		}
		return new Config(cells, ca.border);
	}
}

// Compute the next configuration by applying δ to every active cell.
// We expand the active range by 1 in each direction per step.
export function next<Q, A, B>(
	ca: CellAutomaton<Q, A, B>,
	config: Config<Q>
): Config<Q> {
	const cells = new Map<number, Q>();
	const [lo, hi] = activeBounds(config);
	for (let i = lo - 1; i <= hi + 1; i++) {
		const q = ca.delta(config.get(i - 1), config.get(i), config.get(i + 1));
		if (q !== ca.border) {
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

// Run the automaton for t steps, returning all t+1 configurations.
export function runCA<Q, A, B>(
	ca: CellAutomaton<Q, A, B>,
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
