import { CellAutomaton, Config, runCA } from "./ca-engine";

// Build the compressed CA (C') from a left-independent CA (C_orig) with factor k.
//
// State space Q' = { single(q) | q ∈ Q } ∪ { compr(w) | w : k-tuple of Q }
// δ'(_, single(q), c) = single(δ₂(q, asQ(c)))
// δ'(_, compr(w), c) = compr(fold(w, asQ(c)))
//
// where δ₂(b,c) = δ(border, b, c)  (left-independence means left arg doesn't matter)

export type CompressedState<Q> =
	| { readonly tag: "single"; readonly q: Q }
	| { readonly tag: "compr"; readonly w: readonly Q[] };

function single<Q>(q: Q): CompressedState<Q> {
	return { tag: "single", q };
}

function compr<Q>(w: readonly Q[]): CompressedState<Q> {
	return { tag: "compr", w };
}

function asQ<Q>(border: Q, s: CompressedState<Q>): Q {
	return s.tag === "single" ? s.q : s.w[0];
}

// fold: given k-tuple w and accumulator q, produce k-tuple result
// fold(w, q)[k-1] = δ₂(w[k-1], q)
// fold(w, q)[j]   = δ₂(w[j], fold(w, q)[j+1])   for j < k-1
function fold<Q>(delta2: (b: Q, c: Q) => Q, w: readonly Q[], q: Q): Q[] {
	const k = w.length;
	const result = new Array<Q>(k);
	let acc = q;
	for (let j = k - 1; j >= 0; j--) {
		result[j] = delta2(w[j], acc);
		acc = result[j];
	}
	return result;
}

export function buildCompressedCA<Q, Alpha, Beta>(
	orig: CellAutomaton<Q, Alpha, Beta>,
	k: number
): {
	ca: CellAutomaton<CompressedState<Q>, Alpha, Beta[]>;
	// ψ(i, j) = k*i + j: maps compressed position i + component j → original position
	ψ: (i: number, j: number) => number;
	// φ(t, i, j) = t - (k-1)*i - j: maps time → original time
	φ: (t: number, i: number, j: number) => number;
} {
	const border = orig.border;
	const delta2 = (b: Q, c: Q) => orig.delta(border, b, c);

	const borderCompr = compr<Q>(Array.from({ length: k }, () => border));

	const ca: CellAutomaton<CompressedState<Q>, Alpha, Beta[]> = {
		border: borderCompr,
		delta(_a, b, c) {
			if (b.tag === "single") {
				return single(delta2(b.q, asQ(border, c)));
			}
			return compr(fold(delta2, b.w, asQ(border, c)));
		},
		embed(a) {
			if (a === undefined) return borderCompr;
			return single(orig.embed(a));
		},
		project(q) {
			if (q.tag === "single") {
				const v = orig.project(q.q);
				return Array.from({ length: k }, () => v);
			}
			return q.w.map((qi) => orig.project(qi));
		},
	};

	return {
		ca,
		ψ: (i, j) => k * i + j,
		φ: (t, i, j) => t - (k - 1) * i - j,
	};
}

// Run both the original and compressed CAs and return aligned traces for visualization
export interface DualTrace<Q, Beta> {
	readonly origConfigs: Config<Q>[];
	readonly compressedConfigs: Config<CompressedState<Q>>[];
	readonly k: number;
	readonly wordLength: number;
	readonly origProject: (q: Q) => Beta;
	readonly ψ: (i: number, j: number) => number;
	readonly φ: (t: number, i: number, j: number) => number;
}

export function runDual<Q, Alpha, Beta>(
	orig: CellAutomaton<Q, Alpha, Beta>,
	word: Alpha[],
	k: number,
	steps: number
): DualTrace<Q, Beta> {
	const { ca, ψ, φ } = buildCompressedCA(orig, k);

	// The original needs enough steps to cover all φ values
	// max φ ≈ steps + (k-1)*steps = k*steps
	const origSteps = k * steps + k;
	const origConfigs = runCA(orig, word, origSteps);
	const compressedConfigs = runCA(ca, word, steps);

	return {
		origConfigs,
		compressedConfigs,
		k,
		wordLength: word.length,
		origProject: orig.project,
		ψ,
		φ,
	};
}
