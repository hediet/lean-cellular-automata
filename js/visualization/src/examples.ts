import { CellAutomaton } from "./ca-engine";

// Elementary CA Rule 110 — a well-known left-independent-ish CA.
// For a clean left-independent example, we use a simple addition mod-3 CA:
// δ(left, center, right) = (center + right) mod 3
// This is left-independent by construction.

export const addMod3CA: CellAutomaton<number, number, number> = {
	border: 0,
	delta: (_left, center, right) => (center + right) % 3,
	embed: (a) => (a === undefined ? 0 : a % 3),
	project: (q) => q,
};

// A binary left-independent CA: δ(_, b, c) = b XOR c
export const xorCA: CellAutomaton<number, number, number> = {
	border: 0,
	delta: (_left, center, right) => center ^ right,
	embed: (a) => (a === undefined ? 0 : a & 1),
	project: (q) => q,
};

// Color palette for states (up to 8 states)
export const STATE_COLORS: readonly string[] = [
	"#f0f0f0", // 0 — light gray (border/quiescent)
	"#2196F3", // 1 — blue
	"#F44336", // 2 — red
	"#4CAF50", // 3 — green
	"#FF9800", // 4 — orange
	"#9C27B0", // 5 — purple
	"#00BCD4", // 6 — cyan
	"#795548", // 7 — brown
];

export function stateColor(q: number): string {
	return STATE_COLORS[q % STATE_COLORS.length];
}
