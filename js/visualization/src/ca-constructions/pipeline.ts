// Full composition pipeline
// Source: CellularAutomatas/proofs/constructions/composition/compose_cart.lean
//
// Given C1: α? → β and C2: β? → γ
// Compose to get C: α? → γ such that C.trace_rt = C2.trace_rt ∘ C1.trace_rt
//
// Pipeline (excluding k-step speedup):
// 1. C1' = addBorder(C1)                    : α? → β?
// 2. C1_Λ = compressToLambda(C1')          : α? → (β?³)?
// 3. C2_3x = speedupAndTraceKx(3, C2)      : β?³ → γ³
// 4. C_sim = simFromLambda(C1_Λ, C2_3x)    : α? → (γ³)?
// 5. C_decomp = decompressTriple(C_sim)    : α? → γ

import { CA, Triple, triple, traceRt } from './types';
import { SimFromLambdaState } from './composition';

// ============================================================================
// Simplified Composition (for visualization / testing)
// ============================================================================
//
// Rather than full type-level composition, we provide a simulation function
// that shows how the construction works step by step.

export interface CompositionParams<A, B, C> {
	readonly C1: CA<unknown, A, B>;  // First CA
	readonly C2: CA<unknown, B, C>;  // Second CA
}

// Result of running the composition construction
export interface CompositionResult<B, C> {
	// C1 trace (first CA output)
	readonly c1Trace: B[];

	// C2 trace (second CA run on C1's output)
	readonly c2Trace: C[];

	// Construction intermediate states at each time step
	readonly constructionStates: ConstructionState<B, C>[];
}

export interface ConstructionState<B, C> {
	readonly time: number;
	readonly position: number;
	readonly phase: 'before_trigger' | 'triggered' | 'running';
	readonly counter: 0 | 1 | 2;
	readonly triggerValue: Triple<B | null> | null;
	readonly innerState: C | null;
	readonly output: C | null;
}

// ============================================================================
// True Simulation of the Composition Construction
// ============================================================================

// State for the SimFromΛ portion of the construction
interface SimState<B, C> {
	triggered: boolean;
	counter: 0 | 1 | 2;
	innerCur: C;      // Current inner CA state
	innerPrev: C;     // Previous inner CA state
	innerStep: number; // How many inner steps computed
	triggerTriple: Triple<B | null>;  // The triple that triggered this cell
}

function defaultSimState<B, C>(defaultC: C): SimState<B, C> {
	return {
		triggered: false,
		counter: 0,
		innerCur: defaultC,
		innerPrev: defaultC,
		innerStep: 0,
		triggerTriple: triple(null, null, null),
	};
}

// Get the inner value to share with neighbors
function getNeighborVal<B, C>(s: SimState<B, C>, defaultC: C): C {
	if (!s.triggered) return defaultC;
	return s.counter === 1 ? s.innerPrev : s.innerCur;
}

// One step of SimFromΛ transition
function simStep<B, C>(
	left: SimState<B, C>,
	center: SimState<B, C>,
	right: SimState<B, C>,
	triggerValue: Triple<B | null> | null,  // From C1_Λ
	innerDelta: (l: C, c: C, r: C) => C,
	innerEmbed: (b: B | null) => C,
	defaultC: C
): SimState<B, C> {
	// Case 1: Trigger fires
	if (triggerValue !== null) {
		// Use middle element of triple as initial state
		const initState = innerEmbed(triggerValue[1]);
		return {
			triggered: true,
			counter: 0,
			innerCur: initState,
			innerPrev: initState,
			innerStep: 0,
			triggerTriple: triggerValue,
		};
	}

	// Case 2: Not triggered yet
	if (!center.triggered) {
		return defaultSimState(defaultC);
	}

	// Case 3: Computing inner step (counter = 2)
	if (center.counter === 2) {
		const valL = getNeighborVal(left, defaultC);
		const valR = getNeighborVal(right, defaultC);
		const nextVal = innerDelta(valL, center.innerCur, valR);
		return {
			triggered: true,
			counter: 0,
			innerCur: nextVal,
			innerPrev: center.innerCur,
			innerStep: center.innerStep + 1,
			triggerTriple: center.triggerTriple,
		};
	}

	// Case 4: Just increment counter
	return {
		...center,
		counter: ((center.counter + 1) % 3) as 0 | 1 | 2,
	};
}

// Simulate the full composition construction
export function simulateComposition<A, B, C>(
	C1: CA<unknown, A, B>,
	C2: CA<unknown, B, C>,
	word: A[],
	maxSteps: number
): CompositionResult<B, C> {
	// Step 1: Run C1 to get trace
	const c1Trace = traceRt(C1 as CA<unknown, A, B>, word);

	// Step 2: Run C2 on C1's trace to get expected result
	const c2Trace = traceRt(C2 as CA<unknown, B, C>, c1Trace);

	// Step 3: Simulate the construction
	const constructionStates: ConstructionState<B, C>[] = [];

	// For SimFromΛ, the trigger fires at time 3 + 2|p| for position p
	// After trigger, inner CA runs at 1/3 speed

	// Grid of SimState at each (position, time)
	const gridKey = (p: number, t: number) => `${p},${t}`;
	const grid = new Map<string, SimState<B, C>>();

	const minP = -maxSteps - 1;
	const maxP = maxSteps + word.length;
	const maxT = 3 * maxSteps + 10;

	const defaultC = C2.border as C;

	// Initialize at t=0
	for (let p = minP; p <= maxP; p++) {
		grid.set(gridKey(p, 0), defaultSimState(defaultC as C));
	}

	// Helper: get trigger value from C1's trace at diagonal time
	function getTrigger(t: number, p: number): Triple<B | null> | null {
		const diagTime = 3 + 2 * Math.abs(p);
		if (t !== diagTime) return null;

		if (p >= 0) {
			// Real data from C1 trace
			const base = 3 * p;
			const v0 = base < c1Trace.length ? c1Trace[base] : null;
			const v1 = base + 1 < c1Trace.length ? c1Trace[base + 1] : null;
			const v2 = base + 2 < c1Trace.length ? c1Trace[base + 2] : null;
			return triple(v0 as B | null, v1 as B | null, v2 as B | null);
		} else {
			// Placeholder for p < 0
			return triple(null, null, null);
		}
	}

	// Simulate step by step
	for (let t = 1; t <= maxT; t++) {
		for (let p = minP; p <= maxP; p++) {
			const left = grid.get(gridKey(p - 1, t - 1)) ?? defaultSimState(defaultC);
			const center = grid.get(gridKey(p, t - 1)) ?? defaultSimState(defaultC);
			const right = grid.get(gridKey(p + 1, t - 1)) ?? defaultSimState(defaultC);

			const triggerValue = getTrigger(t, p);

			const nextState = simStep(
				left, center, right,
				triggerValue,
				(l, c, r) => C2.delta(l as unknown, c as unknown, r as unknown) as C,
				(b) => C2.embed(b as B | undefined) as C,
				defaultC
			);

			grid.set(gridKey(p, t), nextState);

			// Record state for visualization
			if (p >= minP && p <= maxP) {
				const diagTime = 3 + 2 * Math.abs(p);
				let phase: 'before_trigger' | 'triggered' | 'running';
				if (t < diagTime) {
					phase = 'before_trigger';
				} else if (t === diagTime) {
					phase = 'triggered';
				} else {
					phase = 'running';
				}

				constructionStates.push({
					time: t,
					position: p,
					phase,
					counter: nextState.counter,
					triggerValue: triggerValue,
					innerState: nextState.triggered ? nextState.innerCur : null,
					output: (nextState.triggered && nextState.counter === 0)
						? C2.project(nextState.innerCur as unknown) as C
						: null,
				});
			}
		}
	}

	return {
		c1Trace: c1Trace as B[],
		c2Trace: c2Trace as C[],
		constructionStates,
	};
}

// ============================================================================
// Full compose function (type-level composition)
// ============================================================================
//
// This creates a new CA that computes the composition C2 ∘ C1

// Simplified state type for composed CA
export interface ComposedState<Q1, Q2, B> {
	readonly c1State: unknown;  // AddBorder state
	readonly compressState: unknown;  // CompressToΛ state
	readonly simState: SimFromLambdaState<unknown, unknown>;
	readonly decompState: unknown;  // DecompressTriple state
}

// For a simpler simulation-based approach, we just run both CAs
export function compose<A, B, C>(
	C1: CA<unknown, A, B>,
	C2: CA<unknown, B, C>,
	defaultC: C
): CA<unknown, A, C> {
	// This is a simplified version that just runs both CAs
	// A full implementation would compose the actual state machines

	// For now, return a CA that:
	// 1. Embeds input using C1
	// 2. Runs the full simulation

	return {
		border: { c1: C1.border, c2: C2.border },

		delta: (_l, c, _r) => c,  // Placeholder - full simulation needed

		embed: (input) => ({
			c1: C1.embed(input),
			c2: C2.border,
		}),

		project: (_s) => defaultC,  // Placeholder
	};
}

// ============================================================================
// Example CAs for testing
// ============================================================================

// Simple counter CA: increments state, outputs state value
export const counterCA: CA<number, number, number> = {
	border: 0,
	delta: (l, c, r) => {
		if (l === 0 && c === 0 && r === 0) return 0;
		return 1 + ((l + c + r) % 7);
	},
	embed: (a) => a ?? 0,
	project: (q) => q,
};

// Identity-ish CA: passes through with modification
export const incrementCA: CA<number, number, number> = {
	border: 0,
	delta: (l, c, r) => (c + 1) % 10,
	embed: (a) => a ?? 0,
	project: (q) => q,
};
