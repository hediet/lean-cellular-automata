import React from "react";
import { simulateCAWithWord } from "./App";

// ============================================================================
// CONSTRUCTION INTERFACE
// ============================================================================

export type HoverState = {
	origP: number;
	origT: number;
	// Dependencies in original-space
	deps?: { origP: number; origT: number }[];
	// Transformed-space coordinates (set when hovering in transformed diagram)
	transI?: number;
	transT?: number;
	// Dependencies in transformed-space
	transDeps?: { i: number; t: number }[];
} | null;

// Check if a cell is a dependency of the hovered cell (original-space)
export function isDependency(hover: HoverState, p: number, t: number): boolean {
	if (!hover || !hover.deps) return false;
	return hover.deps.some((d) => d.origP === p && d.origT === t);
}

// Check if a transformed cell is a dependency of the hovered cell (transformed-space)
export function isTransformedDependency(hover: HoverState, i: number, t: number): boolean {
	if (!hover || !hover.transDeps) return false;
	return hover.transDeps.some((d) => d.i === i && d.t === t);
}

// Get dependencies for a cell at position p, time t
// isLeftIndep: true = 2 deps (center, right), false = 3 deps (left, center, right)
export function getDependencies(p: number, t: number, isLeftIndep: boolean): { origP: number; origT: number }[] {
	if (t <= 0) return [];
	if (isLeftIndep) {
		return [
			{ origP: p, origT: t - 1 },
			{ origP: p + 1, origT: t - 1 },
		];
	}
	return [
		{ origP: p - 1, origT: t - 1 },
		{ origP: p, origT: t - 1 },
		{ origP: p + 1, origT: t - 1 },
	];
}

export interface ConstructionParams {
	k: number;
	steps: number;
	wordLen: number;
}

export interface OriginalCell {
	origP: number;
	origT: number;
}

export interface TransformedCellContent {
	type: "single" | "multi";
	components: OriginalCell[];
}

export interface IntermediateState {
	origP: number;
	origT: number;
	column: number; // fractional column position (e.g. 0.5 = between column 0 and 1)
}

export interface SimStateInfo {
	triggered: boolean;
	counter: number;
	innerCur: number;
	innerPrev: number;
	innerStep: number;
	triggerTriple: [number, number, number];
}

export interface SecondSimulation {
	grid: Map<string, number>;
	wordLen: number;
	maxT: number;
	constructionGrid?: Map<string, number>;
	constructionMaxT?: number;
	constructionStates?: Map<string, SimStateInfo>;
	c1Trace?: number[];
	fullConstructionStates?: Map<string, FullSimStateInfo>;
}

export interface Construction {
	readonly id: string;
	readonly name: string;
	readonly description: string;
	readonly hasKParam: boolean;
	readonly isOriginalLeftIndep: boolean;
	readonly isTransformedLeftIndep: boolean;

	computeOrigSteps(params: ConstructionParams): number;
	getTransformedRange(params: ConstructionParams): { posLo: number; posHi: number };
	getCellContent(params: ConstructionParams, i: number, t: number): TransformedCellContent;
	getIntermediateStates(params: ConstructionParams, t: number): IntermediateState[];

	computeSecondSim?(
		originalGrid: Map<string, number>,
		params: ConstructionParams,
		origSteps: number,
	): SecondSimulation;

	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode;
	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode;
}

export interface OriginalCellRenderContext {
	cx: number;
	cy: number;
	p: number;
	t: number;
	circleR: number;
	color: string;
	isBorder: boolean;
	isHighlighted: boolean;
	isDependency: boolean;
	onHover: (h: HoverState) => void;
}

export interface TransformedCellRenderContext {
	cx: number;
	cy: number;
	i: number;
	t: number;
	cellSize: number;
	content: TransformedCellContent;
	getColor: (origP: number, origT: number) => { color: string; isBorder: boolean };
	hover: HoverState;
	onHover: (h: HoverState) => void;
}

// ============================================================================
// GENERIC STATE CIRCLE COMPONENT
// ============================================================================

export function StateCircle({
	cx,
	cy,
	r,
	comp,
	getColor,
	hover,
	onHover,
	isExternalHighlight = false,
	showLabel = true,
	labelSize,
}: {
	cx: number;
	cy: number;
	r: number;
	comp: OriginalCell;
	getColor: (origP: number, origT: number) => { color: string; isBorder: boolean };
	hover: HoverState;
	onHover: (h: HoverState) => void;
	isExternalHighlight?: boolean;
	showLabel?: boolean;
	labelSize?: number;
}): React.ReactNode {
	const { color, isBorder } = getColor(comp.origP, comp.origT);
	const isHovered = hover !== null && hover.origP === comp.origP && hover.origT === comp.origT;
	const isOrigDep = isDependency(hover, comp.origP, comp.origT);
	const highlighted = isHovered || isExternalHighlight || isOrigDep;
	const actualR = isHovered ? r + 2 : r;
	const stroke = highlighted ? "#000" : isBorder ? "#999" : "#555";
	const strokeWidth = isHovered ? 2.5 : highlighted ? 1.5 : isBorder ? 0.3 : 0.6;
	const fontSize = labelSize ?? Math.max(r - 1, 5);

	return (
		<>
			<circle
				cx={cx} cy={cy} r={actualR}
				fill={color} stroke={stroke} strokeWidth={strokeWidth}
				opacity={isBorder ? 0.4 : 1}
				style={{ cursor: "pointer" }}
				onMouseEnter={() => onHover({ origP: comp.origP, origT: comp.origT })}
				onMouseLeave={() => onHover(null)}
			/>
			{showLabel && (
				<text
					x={cx} y={cy + fontSize * 0.35}
					textAnchor="middle" fontSize={fontSize}
					fill="#fff" pointerEvents="none"
					fontWeight={isHovered ? "bold" : "normal"}
				>
					{comp.origT}
				</text>
			)}
		</>
	);
}

function defaultRenderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode {
	return (
		<StateCircle
			cx={ctx.cx} cy={ctx.cy} r={ctx.circleR}
			comp={{ origP: ctx.p, origT: ctx.t }}
			getColor={() => ({ color: ctx.color, isBorder: ctx.isBorder })}
			hover={null}
			onHover={ctx.onHover}
			isExternalHighlight={ctx.isHighlighted || ctx.isDependency}
		/>
	);
}

// ============================================================================
// LEFT-INDEP SPEEDUP CONSTRUCTION
// ============================================================================

export class LeftIndepSpeedupConstruction implements Construction {
	readonly id = "left_indep_speedup";
	readonly name = "Left-Indep Speedup";
	readonly description = `
		<strong>Left-indep speedup:</strong> For i ≥ 0: <em>single(q)</em> tracks one state.
		For i &lt; 0: <em>compr(w₀...w<sub>k-1</sub>)</em> stores k states on a diagonal.
		ψ(i,j) = k·i + j, φ(t,i,j) = t − (k−1)·i − j.
	`;
	readonly hasKParam = true;
	readonly isOriginalLeftIndep = true;
	readonly isTransformedLeftIndep = true;

	computeOrigSteps({ k, steps }: ConstructionParams): number {
		return steps * k + 1;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return {
			posLo: -Math.min(steps, 3),
			posHi: wordLen + Math.min(steps, 2) - 1,
		};
	}

	getCellContent({ k }: ConstructionParams, i: number, t: number): TransformedCellContent {
		if (i >= 0) {
			return { type: "single", components: [{ origP: i, origT: t }] };
		} else {
			const components: OriginalCell[] = [];
			for (let j = 0; j < k; j++) {
				const origP = k * i + j;
				const origT = t - (k - 1) * i - j;
				components.push({ origP, origT });
			}
			return { type: "multi", components };
		}
	}

	getIntermediateStates(): IntermediateState[] {
		return [];
	}

	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode {
		return (
			<StateCircle
				cx={ctx.cx} cy={ctx.cy} r={ctx.circleR}
				comp={{ origP: ctx.p, origT: ctx.t }}
				getColor={() => ({ color: ctx.color, isBorder: ctx.isBorder })}
				hover={null}
				onHover={ctx.onHover}
				isExternalHighlight={ctx.isHighlighted || ctx.isDependency}
			/>
		);
	}

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, cellSize, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);

		if (content.type === "single") {
			return (
				<StateCircle
					cx={cx} cy={cy} r={8}
					comp={content.components[0]}
					getColor={getColor} hover={hover} onHover={onHover}
					isExternalHighlight={isTransDep}
				/>
			);
		}

		const k = content.components.length;
		const getSmallCirclePos = (j: number) => {
			const spacing = (cellSize - 12) / (k - 1 || 1);
			return {
				dx: -((k - 1) * spacing) / 2 + j * spacing,
				dy: ((k - 1) * spacing) / 2 - j * spacing,
			};
		};
		const allBorder = content.components.every((c) => getColor(c.origP, c.origT).isBorder);

		return (
			<>
				<rect
					x={cx - cellSize / 2 + 2} y={cy - cellSize / 2 + 2}
					width={cellSize - 4} height={cellSize - 4}
					fill={allBorder ? "#f0f0f0" : "#fff"}
					stroke={allBorder ? "#ccc" : "#888"}
					strokeWidth={0.5} rx={3}
				/>
				{content.components.map((comp, j) => {
					const pos = getSmallCirclePos(j);
					const prevPos = j > 0 ? getSmallCirclePos(j - 1) : null;
					return (
						<React.Fragment key={j}>
							{prevPos && (
								<line
									x1={cx + prevPos.dx} y1={cy + prevPos.dy}
									x2={cx + pos.dx} y2={cy + pos.dy}
									stroke="#e0e0e0" strokeWidth={0.5}
								/>
							)}
							<StateCircle
								cx={cx + pos.dx} cy={cy + pos.dy} r={4}
								comp={comp}
								getColor={getColor} hover={hover} onHover={onHover}
								isExternalHighlight={isTransDep}
							/>
						</React.Fragment>
					);
				})}
			</>
		);
	}
}

// ============================================================================
// REGULAR TO LEFT-INDEP CONSTRUCTION
// ============================================================================

export class RegularToLeftIndepConstruction implements Construction {
	readonly id = "regular_to_left_indep";
	readonly name = "Regular → Left-Indep";
	readonly description = `
		<strong>Regular → Left-Indep:</strong> Q' = single(q) | pair(q₁,q₂) | dead.
		At even t: single at position i + t/2. At odd t: pair at positions i + t/2, i + t/2 + 1.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = true;

	computeOrigSteps({ steps }: ConstructionParams): number {
		return Math.floor(steps / 2) + 1;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return {
			posLo: -Math.floor(steps / 2) - 1,
			posHi: wordLen + 1,
		};
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		const tHalf = Math.floor(t / 2);
		if (t % 2 === 0) {
			return { type: "single", components: [{ origP: i + tHalf, origT: tHalf }] };
		} else {
			return {
				type: "multi",
				components: [
					{ origP: i + tHalf, origT: tHalf },
					{ origP: i + tHalf + 1, origT: tHalf },
				],
			};
		}
	}

	getIntermediateStates(): IntermediateState[] {
		return [];
	}

	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode {
		return defaultRenderOriginalCell(ctx);
	}

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, cellSize, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);

		if (content.type === "single") {
			return (
				<StateCircle
					cx={cx} cy={cy} r={8}
					comp={content.components[0]}
					getColor={getColor} hover={hover} onHover={onHover}
					isExternalHighlight={isTransDep}
				/>
			);
		}

		const allBorder = content.components.every((c) => getColor(c.origP, c.origT).isBorder);
		return (
			<>
				<rect
					x={cx - cellSize / 2 + 2} y={cy - cellSize / 2 + 2}
					width={cellSize - 4} height={cellSize - 4}
					fill={allBorder ? "#f0f0f0" : "#fff"}
					stroke={allBorder ? "#ccc" : "#888"}
					strokeWidth={0.5} rx={3}
				/>
				{content.components.map((comp, j) => (
					<StateCircle
						key={j}
						cx={cx + (j - 0.5) * 10} cy={cy} r={5}
						comp={comp}
						getColor={getColor} hover={hover} onHover={onHover}
						isExternalHighlight={isTransDep}
					/>
				))}
			</>
		);
	}
}

// ============================================================================
// LEFT-INDEP TO REGULAR CONSTRUCTION
// ============================================================================

export class LeftIndepToRegularConstruction implements Construction {
	readonly id = "left_indep_to_regular";
	readonly name = "Left-Indep → Regular";
	readonly description = `
		<strong>Left-Indep → Regular:</strong> One step of C' = two steps of C, shifted right.
		C'.comp(c, t, i) = C.comp(c, 2t, i − t). Same state space, double-speed execution.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = true;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ steps }: ConstructionParams): number {
		return steps * 2 + 1;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return {
			posLo: -1,
			posHi: wordLen + steps,
		};
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		if (t === 0) {
			return { type: "single", components: [{ origP: i, origT: 0 }] };
		}
		// For t > 0, cell contains: two intermediates at time 2t-1, then result at time 2t.
		// Result: orig(i-t, 2t)
		// Intermediates that produce it: orig(i-t, 2t-1) and orig(i-t+1, 2t-1)
		return {
			type: "multi",
			components: [
				{ origP: i - t, origT: 2 * t - 1 },
				{ origP: i - t + 1, origT: 2 * t - 1 },
				{ origP: i - t, origT: 2 * t },
			],
		};
	}

	getIntermediateStates(): IntermediateState[] {
		return [];
	}

	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode {
		return defaultRenderOriginalCell(ctx);
	}

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, cellSize, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);

		if (content.type === "single") {
			return (
				<StateCircle
					cx={cx} cy={cy} r={8}
					comp={content.components[0]}
					getColor={getColor} hover={hover} onHover={onHover}
					isExternalHighlight={isTransDep}
				/>
			);
		}

		// 3 components: [intermediate1, intermediate2, result]
		const allBorder = content.components.every((c) => getColor(c.origP, c.origT).isBorder);
		const topY = -cellSize / 4;
		const bottomY = cellSize / 8;
		const positions = [
			{ dx: -cellSize / 5, dy: topY },
			{ dx: cellSize / 5, dy: topY },
			{ dx: 0, dy: bottomY },
		];

		return (
			<>
				<rect
					x={cx - cellSize / 2 + 2} y={cy - cellSize / 2 + 2}
					width={cellSize - 4} height={cellSize - 4}
					fill={allBorder ? "#f0f0f0" : "#fff"}
					stroke={allBorder ? "#ccc" : "#888"}
					strokeWidth={0.5} rx={3}
				/>
				<line
					x1={cx + positions[0].dx} y1={cy + positions[0].dy}
					x2={cx + positions[2].dx} y2={cy + positions[2].dy}
					stroke="#e0e0e0" strokeWidth={0.5}
				/>
				<line
					x1={cx + positions[1].dx} y1={cy + positions[1].dy}
					x2={cx + positions[2].dx} y2={cy + positions[2].dy}
					stroke="#e0e0e0" strokeWidth={0.5}
				/>
				{content.components.map((comp, j) => (
					<StateCircle
						key={j}
						cx={cx + positions[j].dx} cy={cy + positions[j].dy}
						r={j === 2 ? 7 : 5}
						comp={comp}
						getColor={getColor} hover={hover} onHover={onHover}
						isExternalHighlight={isTransDep}
					/>
				))}
			</>
		);
	}
}

// ============================================================================
// FULL PIPELINE: REGULAR → LEFT-INDEP → SPEEDUP(k) → REGULAR
// ============================================================================

// Trace a speedup position through LeftIndepSpeedup → RegToLeftIndep → original
function traceToOriginal(p: number, s: number, k: number): OriginalCell[] {
	// Through LeftIndepSpeedup
	const liCells: OriginalCell[] = [];
	if (p >= 0) {
		liCells.push({ origP: p, origT: s });
	} else {
		for (let j = 0; j < k; j++) {
			liCells.push({ origP: k * p + j, origT: s - (k - 1) * p - j });
		}
	}
	// Through RegToLeftIndep → original
	const origCells: OriginalCell[] = [];
	for (const li of liCells) {
		const half = Math.floor(li.origT / 2);
		if (li.origT % 2 === 0) {
			origCells.push({ origP: li.origP + half, origT: half });
		} else {
			origCells.push({ origP: li.origP + half, origT: half });
			origCells.push({ origP: li.origP + half + 1, origT: half });
		}
	}
	// Deduplicate
	const seen = new Set<string>();
	return origCells.filter((c) => {
		const key = `${c.origP},${c.origT}`;
		if (seen.has(key)) return false;
		seen.add(key);
		return true;
	});
}

export class FullPipelineConstruction implements Construction {
	readonly id = "full_pipeline";
	readonly name = "Full Pipeline (k-Speedup)";
	readonly description = `
		<strong>Full k-step speedup pipeline:</strong> Regular → Left-Indep → Speedup(k) → Regular.<br>
		T steps of the pipeline ≈ k·T steps of the original. Each compressed cell stores k combined states on a diagonal.
	`;
	readonly hasKParam = true;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ k, steps }: ConstructionParams): number {
		return k * steps + 1;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return { posLo: -1, posHi: wordLen + steps };
	}

	getCellContent({ k }: ConstructionParams, i: number, t: number): TransformedCellContent {
		if (t === 0) {
			return { type: "single", components: [{ origP: i, origT: 0 }] };
		}
		// LeftIndepToRegular result: speedup(i-t, 2t)
		const resultCells = traceToOriginal(i - t, 2 * t, k);
		if (resultCells.length === 1) {
			return { type: "single", components: resultCells };
		}
		return { type: "multi", components: resultCells };
	}

	getIntermediateStates(): IntermediateState[] {
		return [];
	}

	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode {
		return defaultRenderOriginalCell(ctx);
	}

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, cellSize, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);

		if (content.type === "single") {
			return (
				<StateCircle
					cx={cx} cy={cy} r={8}
					comp={content.components[0]}
					getColor={getColor} hover={hover} onHover={onHover}
					isExternalHighlight={isTransDep}
				/>
			);
		}

		const sorted = [...content.components].sort((a, b) => b.origT - a.origT);
		const allBorder = sorted.every((c) => getColor(c.origP, c.origT).isBorder);

		const timeGroups = new Map<number, typeof sorted>();
		for (const c of sorted) {
			const group = timeGroups.get(c.origT) ?? [];
			group.push(c);
			timeGroups.set(c.origT, group);
		}
		const times = [...timeGroups.keys()].sort((a, b) => b - a);
		const layerCount = times.length;
		const layerSpacing = (cellSize - 8) / Math.max(layerCount - 1, 1);

		return (
			<>
				<rect
					x={cx - cellSize / 2 + 2} y={cy - cellSize / 2 + 2}
					width={cellSize - 4} height={cellSize - 4}
					fill={allBorder ? "#f0f0f0" : "#fff"}
					stroke={allBorder ? "#ccc" : "#888"}
					strokeWidth={0.5} rx={3}
				/>
				{times.map((time, layerIdx) => {
					const group = timeGroups.get(time)!;
					const dy = -((layerCount - 1) * layerSpacing) / 2 + layerIdx * layerSpacing;
					const groupSpacing = group.length > 1 ? (cellSize - 14) / (group.length - 1) : 0;
					const isResult = layerIdx === 0;

					return group.map((comp, j) => (
						<StateCircle
							key={`${comp.origP}-${comp.origT}`}
							cx={cx + (-((group.length - 1) * groupSpacing) / 2 + j * groupSpacing)}
							cy={cy + dy}
							r={isResult ? 5 : 4}
							comp={comp}
							getColor={getColor} hover={hover} onHover={onHover}
							isExternalHighlight={isTransDep}
						/>
					));
				})}
			</>
		);
	}
}

// ============================================================================
// DIAGONAL SIGNAL CONSTRUCTION
// ============================================================================

export class DiagSignalConstruction implements Construction {
	readonly id = "diag_signal";
	readonly name = "Diagonal Signal";
	readonly description = `
		<strong>Diagonal signal:</strong> Fires at position p, time 3 + 2|p|.
		Used as a trigger/control signal in the composition pipeline.
		Output is <em>true</em> on the diagonal, <em>none</em> elsewhere.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ steps }: ConstructionParams): number {
		return steps;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		const maxP = Math.floor((steps - 3) / 2);
		return { posLo: -maxP, posHi: wordLen + maxP };
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		const diagTime = 3 + 2 * Math.abs(i);
		if (t === diagTime) {
			return { type: "single", components: [{ origP: 0, origT: diagTime }] };
		}
		return { type: "single", components: [{ origP: i, origT: t }] };
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, getColor, hover, onHover } = ctx;
		const diagTime = 3 + 2 * Math.abs(i);
		const onDiag = t === diagTime;
		const comp = { origP: i, origT: t };

		return (
			<>
				<StateCircle
					cx={cx} cy={cy} r={onDiag ? 10 : 6}
					comp={comp}
					getColor={onDiag ? () => ({ color: "#e74c3c", isBorder: false }) : getColor}
					hover={hover} onHover={onHover}
					showLabel={onDiag}
				/>
			</>
		);
	}
}

// ============================================================================
// COMPRESS TO DIAGONAL CONSTRUCTION
// ============================================================================

export class CompressToDiagConstruction implements Construction {
	readonly id = "compress_to_diag";
	readonly name = "Compress to Diagonal";
	readonly description = `
		<strong>Compress to Diagonal:</strong> At position p (≥0), time 2p+3, outputs a triple
		(trace(3p), trace(3p+1), trace(3p+2)) — three consecutive original trace values packed into one cell.
		Outputs <em>none</em> off the diagonal.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ steps }: ConstructionParams): number {
		// We need trace values up to 3*maxP+2 where maxP ~ steps/2
		return 3 * Math.floor(steps / 2) + 3;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return { posLo: -1, posHi: Math.floor(steps / 2) + 1 };
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		const diagTime = 2 * i + 3;
		if (i >= 0 && t === diagTime) {
			// Triple of trace values at origin: (3i, 3i+1, 3i+2)
			return {
				type: "multi",
				components: [
					{ origP: 0, origT: 3 * i },
					{ origP: 0, origT: 3 * i + 1 },
					{ origP: 0, origT: 3 * i + 2 },
				],
			};
		}
		return { type: "single", components: [{ origP: i, origT: t }] };
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, cellSize, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);
		const diagTime = 2 * i + 3;
		const onDiag = i >= 0 && t === diagTime;

		if (content.type === "single" && !onDiag) {
			return (
				<StateCircle
					cx={cx} cy={cy} r={6}
					comp={content.components[0]}
					getColor={() => ({ color: "#ddd", isBorder: true })}
					hover={hover} onHover={onHover}
					showLabel={false}
				/>
			);
		}

		const allBorder = content.components.every((c) => getColor(c.origP, c.origT).isBorder);
		return (
			<>
				<rect
					x={cx - cellSize / 2 + 2} y={cy - cellSize / 2 + 2}
					width={cellSize - 4} height={cellSize - 4}
					fill={allBorder ? "#f0f0f0" : "#fff"}
					stroke={onDiag ? "#e74c3c" : allBorder ? "#ccc" : "#888"}
					strokeWidth={onDiag ? 1.5 : 0.5} rx={3}
				/>
				{content.components.map((comp, j) => {
					const dy = (j - 1) * (cellSize - 8) / 2;
					return (
						<StateCircle
							key={j}
							cx={cx} cy={cy + dy} r={5}
							comp={comp}
							getColor={getColor} hover={hover} onHover={onHover}
							isExternalHighlight={isTransDep}
						/>
					);
				})}
			</>
		);
	}
}

// ============================================================================
// DECOMPRESS TRIPLE CONSTRUCTION
// ============================================================================

export class DecompressTripleConstruction implements Construction {
	readonly id = "decompress_triple";
	readonly name = "Decompress Triple";
	readonly description = `
		<strong>Decompress Triple:</strong> Takes a CA outputting (β³)? triples every 3rd step and
		unpacks them into one value per step. At time 3t₁+t₂+k, outputs the t₂-th element of the triple from time 3t₁+k.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ steps }: ConstructionParams): number {
		return steps + 3;
	}

	getTransformedRange({ wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return { posLo: -1, posHi: wordLen + 1 };
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		// At origin (position 0), time t maps to original triple at time 3*floor(t/3)
		// extracting element t%3
		if (i === 0 && t >= 0) {
			const tripleTime = 3 * Math.floor(t / 3);
			const offset = t % 3;
			return {
				type: "single",
				components: [{ origP: 0, origT: tripleTime + offset }],
			};
		}
		return { type: "single", components: [{ origP: i, origT: t }] };
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);
		const isAtOrigin = i === 0 && t >= 0;
		const offset = t % 3;
		const isTripleBoundary = offset === 0;

		return (
			<StateCircle
				cx={cx} cy={cy} r={isAtOrigin ? 8 : 6}
				comp={content.components[0]}
				getColor={isAtOrigin ? getColor : () => ({ color: "#ddd", isBorder: true })}
				hover={hover} onHover={onHover}
				isExternalHighlight={isTransDep || (isAtOrigin && isTripleBoundary)}
				showLabel={isAtOrigin}
			/>
		);
	}
}

// ============================================================================
// SIM FROM LAMBDA CONSTRUCTION
// ============================================================================

export class SimFromLambdaConstruction implements Construction {
	readonly id = "sim_from_lambda";
	readonly name = "Sim from Λ";
	readonly description = `
		<strong>Sim from Λ:</strong> A control CA fires on the diagonal (at time 3+2|p|), initializing a local
		simulation of an inner CA. The inner CA runs at 1/3 speed (one compute step per 3 real steps).
		At origin, inner step t appears at real time 3t+3.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ steps }: ConstructionParams): number {
		// Inner CA steps map to real time 3t+3; need original trace up to steps
		return steps;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		const maxP = Math.floor((steps - 3) / 2);
		return { posLo: -Math.max(maxP, 1), posHi: wordLen + Math.max(maxP, 1) };
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		const diagTime = 3 + 2 * Math.abs(i);
		if (t >= diagTime) {
			const elapsed = t - diagTime;
			if (elapsed % 3 === 0) {
				const innerStep = elapsed / 3;
				// This cell's inner CA is at step innerStep
				// In composition context this maps to the inner CA's state
				return { type: "single", components: [{ origP: i, origT: innerStep }] };
			}
			// In between steps — phase counter cycling
			return { type: "single", components: [{ origP: i, origT: t }] };
		}
		// Before trigger
		return { type: "single", components: [{ origP: i, origT: t }] };
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);
		const diagTime = 3 + 2 * Math.abs(i);
		const active = t >= diagTime;
		const elapsed = active ? t - diagTime : -1;
		const isOutputStep = active && elapsed % 3 === 0;

		return (
			<StateCircle
				cx={cx} cy={cy} r={isOutputStep ? 8 : active ? 6 : 4}
				comp={content.components[0]}
				getColor={isOutputStep ? getColor : active ? () => ({ color: "#aaa", isBorder: false }) : () => ({ color: "#ddd", isBorder: true })}
				hover={hover} onHover={onHover}
				isExternalHighlight={isTransDep}
				showLabel={isOutputStep}
			/>
		);
	}
}

// ============================================================================
// FULL COMPOSITION (C2 ∘ C1, NO K-STEP SPEEDUP)
// ============================================================================
// TRUE SIMFROMLAMBDA SIMULATION
// ============================================================================

// State of SimFromΛ at each cell
interface SimState {
	triggered: boolean;
	counter: number; // 0, 1, 2
	innerCur: number; // current inner CA state (C2 state)
	innerPrev: number; // previous inner CA state
	innerStep: number; // which C2 time step this corresponds to
	triggerTriple: [number, number, number]; // C1 trace values that triggered this cell
}

function delta3(left: number, center: number, right: number): number {
	if (left === 0 && center === 0 && right === 0) return 0;
	return 1 + ((left + center + right) % 7);
}

// Read the inner value from a neighbor for the synchronization step
function getNeighborVal(q: SimState): number {
	if (!q.triggered) return 0;
	return q.counter === 1 ? q.innerPrev : q.innerCur;
}

function simStep(left: SimState, center: SimState, right: SimState, triggerValue: number | null, triggerTriple: [number, number, number]): SimState {
	if (triggerValue !== null) {
		return { triggered: true, counter: 0, innerCur: triggerValue, innerPrev: triggerValue, innerStep: 0, triggerTriple };
	}

	if (!center.triggered) {
		return { triggered: false, counter: 0, innerCur: 0, innerPrev: 0, innerStep: 0, triggerTriple: [0, 0, 0] };
	}

	if (center.counter === 2) {
		const valA = getNeighborVal(left);
		const valC = getNeighborVal(right);
		const next = delta3(valA, center.innerCur, valC);
		return { triggered: true, counter: 0, innerCur: next, innerPrev: center.innerCur, innerStep: center.innerStep + 1, triggerTriple: center.triggerTriple };
	}

	return { triggered: true, counter: center.counter + 1, innerCur: center.innerCur, innerPrev: center.innerPrev, innerStep: center.innerStep, triggerTriple: center.triggerTriple };
}

// Output at a cell: the inner state when counter = 0 and triggered
function simOutput(q: SimState): number | null {
	if (!q.triggered) return null;
	if (q.counter === 0) return q.innerCur;
	return null;
}

function simulateCompositionConstruction(
	c1Grid: Map<string, number>,
	wordLen: number,
	steps: number,
): { grid: Map<string, number>; maxT: number; states: Map<string, SimStateInfo>; c1Trace: number[] } {
	const c1Trace: number[] = [];
	for (let t = 0; t < wordLen; t++) {
		c1Trace.push(c1Grid.get(`0,${t}`) ?? 0);
	}

	const overhead = 6;
	const maxT = 3 * steps + overhead + 3;
	const minP = -Math.floor(maxT / 2) - 1;
	const maxP = Math.floor(maxT / 2) + 1;

	const defaultState: SimState = { triggered: false, counter: 0, innerCur: 0, innerPrev: 0, innerStep: 0, triggerTriple: [0, 0, 0] };

	const stateGrid: Map<string, SimState> = new Map();
	const key = (p: number, t: number) => `${p},${t}`;

	const getState = (p: number, t: number): SimState =>
		stateGrid.get(key(p, t)) ?? defaultState;

	for (let p = minP; p <= maxP; p++) {
		stateGrid.set(key(p, 0), defaultState);
	}

	for (let t = 1; t <= maxT; t++) {
		for (let p = minP; p <= maxP; p++) {
			const left = getState(p - 1, t - 1);
			const center = getState(p, t - 1);
			const right = getState(p + 1, t - 1);

			const diagTime = 3 + 2 * Math.abs(p);
			let triggerValue: number | null = null;
			let triple: [number, number, number] = [0, 0, 0];
			if (t === diagTime && p >= 0) {
				const base = 3 * p;
				triple = [
					base < c1Trace.length ? c1Trace[base] : 0,
					base + 1 < c1Trace.length ? c1Trace[base + 1] : 0,
					base + 2 < c1Trace.length ? c1Trace[base + 2] : 0,
				];
				triggerValue = triple[1]; // middle of triple as init
			} else if (t === diagTime && p < 0) {
				triggerValue = 0;
			}

			stateGrid.set(key(p, t), simStep(left, center, right, triggerValue, triple));
		}
	}

	const grid = new Map<string, number>();
	const states = new Map<string, SimStateInfo>();
	for (let t = 0; t <= maxT; t++) {
		for (let p = minP; p <= maxP; p++) {
			const s = getState(p, t);
			states.set(key(p, t), {
				triggered: s.triggered, counter: s.counter,
				innerCur: s.innerCur, innerPrev: s.innerPrev,
				innerStep: s.innerStep, triggerTriple: s.triggerTriple,
			});
			const out = simOutput(s);
			if (out !== null) {
				grid.set(key(p, t), out);
			} else if (s.triggered) {
				grid.set(key(p, t), -1 - s.counter);
			}
		}
	}

	return { grid, maxT, states, c1Trace };
}

export class CompositionConstruction implements Construction {
	readonly id = "composition";
	readonly name = "Composition (C2 ∘ C1)";
	readonly description = `
		<strong>True composition (C2 ∘ C1):</strong> Left: C1 simulation.
		Right: C2 simulation on C1's trace (green palette).
		The construction internally packs C1's trace into triples on a diagonal,
		triggers C2 simulation at 1/3 speed via SimFromΛ, then decompresses.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ wordLen }: ConstructionParams): number {
		return wordLen;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return { posLo: -steps - 1, posHi: wordLen + steps + 1 };
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		return { type: "single", components: [{ origP: i, origT: t }] };
	}

	computeSecondSim(
		originalGrid: Map<string, number>,
		params: ConstructionParams,
	): SecondSimulation {
		const trace: number[] = [];
		for (let t = 0; t < params.wordLen; t++) {
			trace.push(originalGrid.get(`0,${t}`) ?? 0);
		}
		const sim = simulateCAWithWord(trace, params.steps);
		const constr = simulateCompositionConstruction(originalGrid, params.wordLen, params.steps);
		return {
			grid: sim.grid,
			wordLen: trace.length,
			maxT: params.steps,
			constructionGrid: constr.grid,
			constructionMaxT: constr.maxT,
			constructionStates: constr.states,
			c1Trace: constr.c1Trace,
		};
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);
		return (
			<StateCircle
				cx={cx} cy={cy} r={8}
				comp={content.components[0]}
				getColor={getColor} hover={hover} onHover={onHover}
				isExternalHighlight={isTransDep}
			/>
		);
	}
}

// ============================================================================
// TRUE FULL COMPOSITION (C2 ∘ C1, NO K-STEP SPEEDUP)
// ============================================================================
// Pipeline: AddBorder(C1) → CompressToΛ → SimFromΛ(_, C2_3x) → DecompressTriple
//
// The inner CA in SimFromΛ is C2_3x = SpeedupAndTraceKx(3, C2).
// C2_3x state: 3 compressed spatial positions × 4 temporal states = number[3][4]
// Each C2_3x step = 3 spatial steps of TraceKx(3, C2)
// Each TraceKx step = shift temporal + compute 1 new C2 state
// Net: 1 C2_3x step = 3 C2 time steps across 3 compressed spatial positions

// C2_3x state: [spatial][temporal] where spatial ∈ {0,1,2}, temporal ∈ {0,1,2,3}
// state[j][i] tracks C2's state history at compressed spatial position j
type C2_3xState = number[][];

const c2_3xBorder: C2_3xState = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]];

function c2_3xEmbed(tripleInput: [number | null, number | null, number | null]): C2_3xState {
	// Each spatial position j gets tripleInput[j], all temporal slots initialized the same
	return tripleInput.map(v => {
		const q = v ?? 0;
		return [q, q, q, q];
	});
}

function c2_3xDelta(left: C2_3xState, center: C2_3xState, right: C2_3xState): C2_3xState {
	// SpeedupKx(3, TraceKx(3, C2)):
	// Build local spatial config from 3 compressed neighbors (9 TraceKx states at positions -3..5)
	// Then run 3 steps of TraceKx(3, C2) on it, extract positions 0..2

	// Working grid: spatial position → temporal array [4 values]
	const grid = new Map<number, number[]>();
	for (let j = 0; j < 3; j++) {
		grid.set(j - 3, [...left[j]]);    // positions -3, -2, -1
		grid.set(j, [...center[j]]);      // positions 0, 1, 2
		grid.set(j + 3, [...right[j]]);   // positions 3, 4, 5
	}
	// Clamp boundaries
	grid.set(-4, [...(left[0])]);
	grid.set(6, [...(right[2])]);

	// Apply 3 steps of TraceKx(3, delta3)
	// TraceKx delta at position p:
	//   new = [center[1], center[2], center[3], delta3(left[3], center[3], right[3])]
	//   (Fin.snoc (Fin.tail b) (C.δ a[last] b[last] c[last]))
	for (let step = 0; step < 3; step++) {
		const next = new Map<number, number[]>();
		for (let p = -3; p <= 5; p++) {
			const lp = grid.get(p - 1) ?? [0, 0, 0, 0];
			const cp = grid.get(p) ?? [0, 0, 0, 0];
			const rp = grid.get(p + 1) ?? [0, 0, 0, 0];
			next.set(p, [cp[1], cp[2], cp[3], delta3(lp[3], cp[3], rp[3])]);
		}
		for (const [k, v] of next) grid.set(k, v);
	}

	return [
		grid.get(0) ?? [0, 0, 0, 0],
		grid.get(1) ?? [0, 0, 0, 0],
		grid.get(2) ?? [0, 0, 0, 0],
	];
}

function c2_3xProject(state: C2_3xState): [number, number, number] {
	// SpeedupAndTraceKx.C.project = map_project (fun f => fun i => (f 0 i).getD default)
	// f = SP.C.project(q) = fun j => TraceKx.C.project(q(j))
	// TraceKx.C.project(q) = fun i => some(C.project(q(i.castSucc)))
	// So f(j)(i) = some(C.project(q(j)(i))) for i < k
	// map_project: f(0)(i).getD default = C.project(q(0)(i)) = q(0)(i) (since project = id for delta3)
	// Output: [state[0][0], state[0][1], state[0][2]]
	return [state[0][0], state[0][1], state[0][2]];
}

function eqC2_3xState(a: C2_3xState, b: C2_3xState): boolean {
	for (let j = 0; j < 3; j++)
		for (let i = 0; i < 4; i++)
			if ((a[j]?.[i] ?? 0) !== (b[j]?.[i] ?? 0)) return false;
	return true;
}

// Full SimFromΛ state with C2_3x inner CA
interface FullSimState {
	triggered: boolean;
	counter: number; // 0, 1, 2
	innerCur: C2_3xState;
	innerPrev: C2_3xState;
	innerStep: number;
	triggerTriple: [number | null, number | null, number | null];
}

const defaultFullSimState: FullSimState = {
	triggered: false, counter: 0,
	innerCur: c2_3xBorder, innerPrev: c2_3xBorder,
	innerStep: 0, triggerTriple: [null, null, null],
};

function getFullNeighborVal(q: FullSimState): C2_3xState {
	if (!q.triggered) return c2_3xBorder;
	return q.counter === 1 ? q.innerPrev : q.innerCur;
}

function fullSimStep(
	left: FullSimState, center: FullSimState, right: FullSimState,
	triggerValue: [number | null, number | null, number | null] | null,
): FullSimState {
	if (triggerValue !== null) {
		const init = c2_3xEmbed(triggerValue);
		return { triggered: true, counter: 0, innerCur: init, innerPrev: init, innerStep: 0, triggerTriple: triggerValue };
	}
	if (!center.triggered) return defaultFullSimState;
	if (center.counter === 2) {
		const valA = getFullNeighborVal(left);
		const valC = getFullNeighborVal(right);
		const next = c2_3xDelta(valA, center.innerCur, valC);
		return { triggered: true, counter: 0, innerCur: next, innerPrev: center.innerCur, innerStep: center.innerStep + 1, triggerTriple: center.triggerTriple };
	}
	return { ...center, counter: center.counter + 1 };
}

// DecompressTriple state
interface DecompState {
	counter: number; // 0, 1, 2
	stored: [number, number, number];
}

export interface FullSimStateInfo {
	triggered: boolean;
	counter: number;
	innerStep: number;
	triggerTriple: [number | null, number | null, number | null];
	innerCurProjected: [number, number, number] | null; // c2_3xProject of innerCur
	decompCounter: number;
	decompStored: [number, number, number];
	output: number | null; // final decompressed output
}

function simulateFullCompositionPipeline(
	c1Grid: Map<string, number>,
	wordLen: number,
	steps: number,
): {
	grid: Map<string, number>; maxT: number;
	states: Map<string, FullSimStateInfo>;
	c1Trace: number[];
	decompGrid: Map<string, number>;
} {
	// Step 1: Extract C1 trace at position 0
	const c1Trace: number[] = [];
	for (let t = 0; t < 3 * wordLen; t++) {
		c1Trace.push(c1Grid.get(`0,${t}`) ?? 0);
	}

	const maxT = 3 * steps + 12;
	const minP = -Math.floor(maxT / 2) - 1;
	const maxP = Math.floor(maxT / 2) + 1;

	const key = (p: number, t: number) => `${p},${t}`;

	// --- SimFromΛ with C2_3x ---
	const simGrid = new Map<string, FullSimState>();
	const getSimState = (p: number, t: number): FullSimState =>
		simGrid.get(key(p, t)) ?? defaultFullSimState;

	for (let p = minP; p <= maxP; p++) {
		simGrid.set(key(p, 0), defaultFullSimState);
	}

	for (let t = 1; t <= maxT; t++) {
		for (let p = minP; p <= maxP; p++) {
			const left = getSimState(p - 1, t - 1);
			const center = getSimState(p, t - 1);
			const right = getSimState(p + 1, t - 1);

			const diagTime = 3 + 2 * Math.abs(p);
			let trigger: [number | null, number | null, number | null] | null = null;
			if (t === diagTime && p >= 0) {
				const base = 3 * p;
				trigger = [
					base < c1Trace.length ? c1Trace[base] : null,
					base + 1 < c1Trace.length ? c1Trace[base + 1] : null,
					base + 2 < c1Trace.length ? c1Trace[base + 2] : null,
				];
			} else if (t === diagTime && p < 0) {
				trigger = [null, null, null];
			}

			simGrid.set(key(p, t), fullSimStep(left, center, right, trigger));
		}
	}

	// --- SimFromΛ output: Triple<number> | null when counter=0 and triggered ---
	// --- DecompressTriple: unpack triples ---
	const decompGrid = new Map<string, DecompState>();
	const getDecompState = (p: number, t: number): DecompState =>
		decompGrid.get(key(p, t)) ?? { counter: 0, stored: [0, 0, 0] };

	for (let p = minP; p <= maxP; p++) {
		decompGrid.set(key(p, 0), { counter: 0, stored: [0, 0, 0] });
	}

	for (let t = 1; t <= maxT; t++) {
		for (let p = minP; p <= maxP; p++) {
			const prevDecomp = getDecompState(p, t - 1);
			const simState = getSimState(p, t);

			// SimFromΛ output: project only when counter=0 and triggered
			let simOutput: [number, number, number] | null = null;
			if (simState.triggered && simState.counter === 0) {
				simOutput = c2_3xProject(simState.innerCur);
			}

			if (simOutput !== null) {
				decompGrid.set(key(p, t), { counter: 0, stored: simOutput });
			} else {
				decompGrid.set(key(p, t), {
					counter: (prevDecomp.counter + 1) % 3,
					stored: prevDecomp.stored,
				});
			}
		}
	}

	// --- Build output grids ---
	const grid = new Map<string, number>();
	const states = new Map<string, FullSimStateInfo>();
	const outputGrid = new Map<string, number>();

	for (let t = 0; t <= maxT; t++) {
		for (let p = minP; p <= maxP; p++) {
			const s = getSimState(p, t);
			const d = getDecompState(p, t);
			const projected = s.triggered ? c2_3xProject(s.innerCur) : null;

			// innerStep=0 is just the embed state — projected triple is [v,v,v]
			// which does NOT correspond to C2 output. Only innerStep >= 1 is meaningful.
			const validProjected = s.innerStep >= 1 ? projected : null;

			states.set(key(p, t), {
				triggered: s.triggered,
				counter: s.counter,
				innerStep: s.innerStep,
				triggerTriple: s.triggerTriple,
				innerCurProjected: validProjected,
				decompCounter: d.counter,
				decompStored: d.stored,
				output: d.stored[d.counter],
			});

			// Construction grid: show sim phase
			if (s.triggered && s.counter === 0 && projected) {
				grid.set(key(p, t), projected[0]); // Show first element of triple
			} else if (s.triggered) {
				grid.set(key(p, t), -1 - s.counter);
			}

			// Decompressed output
			if (s.triggered) {
				outputGrid.set(key(p, t), d.stored[d.counter]);
			}
		}
	}

	return { grid, maxT, states, c1Trace, decompGrid: outputGrid };
}

export class TrueFullCompositionConstruction implements Construction {
	readonly id = "true_composition";
	readonly name = "True Full Composition";
	readonly description = `
		<strong>True full composition (C2 ∘ C1):</strong>
		Full pipeline: AddBorder → CompressToΛ → SimFromΛ(_, C2_3x) → DecompressTriple.<br>
		Inner CA is <em>C2_3x = SpeedupAndTraceKx(3, C2)</em>: each inner step = 3 C2 time steps
		on 3 compressed spatial positions. Output triples are decompressed to individual values.
		<strong>No k-step speedup</strong> — output timing has a constant offset.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ wordLen }: ConstructionParams): number {
		return 3 * wordLen;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return { posLo: -steps - 1, posHi: wordLen + steps + 1 };
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		return { type: "single", components: [{ origP: i, origT: t }] };
	}

	computeSecondSim(
		originalGrid: Map<string, number>,
		params: ConstructionParams,
	): SecondSimulation {
		// C2 simulation on C1's trace (for comparison)
		const trace: number[] = [];
		for (let t = 0; t < params.wordLen; t++) {
			trace.push(originalGrid.get(`0,${t}`) ?? 0);
		}
		const c2Sim = simulateCAWithWord(trace, params.steps);

		// True full composition pipeline
		const pipeline = simulateFullCompositionPipeline(originalGrid, params.wordLen, params.steps);

		return {
			grid: c2Sim.grid,
			wordLen: trace.length,
			maxT: params.steps,
			constructionGrid: pipeline.grid,
			constructionMaxT: pipeline.maxT,
			c1Trace: pipeline.c1Trace,
			fullConstructionStates: pipeline.states,
		};
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);
		return (
			<StateCircle
				cx={cx} cy={cy} r={8}
				comp={content.components[0]}
				getColor={getColor} hover={hover} onHover={onHover}
				isExternalHighlight={isTransDep}
			/>
		);
	}
}

// ============================================================================
// FLIP CONSTRUCTION
// ============================================================================

export class FlipConstruction implements Construction {
	readonly id = "flip";
	readonly name = "Flip (Mirror)";
	readonly description = `
		<strong>Flip:</strong> Swaps left and right neighbors in the transition function.
		δ'(l, c, r) = δ(r, c, l). The space-time diagram is mirrored horizontally.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ steps }: ConstructionParams): number {
		return steps;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return { posLo: -steps - 1, posHi: wordLen + steps };
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		// Flip maps position p to -p (mirrored around 0)
		return { type: "single", components: [{ origP: -i, origT: t }] };
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);
		return (
			<StateCircle
				cx={cx} cy={cy} r={8}
				comp={content.components[0]}
				getColor={getColor} hover={hover} onHover={onHover}
				isExternalHighlight={isTransDep}
			/>
		);
	}
}

// ============================================================================
// PRODUCT CONSTRUCTION
// ============================================================================

export class ProductConstruction implements Construction {
	readonly id = "product";
	readonly name = "Product (Parallel)";
	readonly description = `
		<strong>Product:</strong> Runs two CAs in parallel on the same input.
		Q' = Q × Q, δ'((l₁,l₂), (c₁,c₂), (r₁,r₂)) = (δ(l₁,c₁,r₁), δ(l₂,c₂,r₂)).
		Shows original CA and its flip running simultaneously.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ steps }: ConstructionParams): number {
		return steps;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return { posLo: -steps - 1, posHi: wordLen + steps };
	}

	getCellContent(_params: ConstructionParams, i: number, t: number): TransformedCellContent {
		// Product shows both original and flipped state
		return {
			type: "multi",
			components: [
				{ origP: i, origT: t },      // Original CA
				{ origP: -i, origT: t },     // Flipped CA
			],
		};
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, cellSize, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);

		const allBorder = content.components.every((c) => getColor(c.origP, c.origT).isBorder);

		return (
			<>
				<rect
					x={cx - cellSize / 2 + 2} y={cy - cellSize / 2 + 2}
					width={cellSize - 4} height={cellSize - 4}
					fill={allBorder ? "#f0f0f0" : "#fff"}
					stroke={allBorder ? "#ccc" : "#888"}
					strokeWidth={0.5} rx={3}
				/>
				{content.components.map((comp, j) => (
					<StateCircle
						key={j}
						cx={cx + (j - 0.5) * 10} cy={cy} r={5}
						comp={comp}
						getColor={getColor} hover={hover} onHover={onHover}
						isExternalHighlight={isTransDep}
					/>
				))}
			</>
		);
	}
}

// ============================================================================
// ADD BORDER CONSTRUCTION
// ============================================================================

export class AddBorderConstruction implements Construction {
	readonly id = "add_border";
	readonly name = "Add Border";
	readonly description = `
		<strong>Add Border:</strong> Marks cells outside the input word as border (null).
		Runs CA in parallel with a border marker signal that propagates from right.
		Output is <em>some(v)</em> inside word, <em>none</em> outside.
	`;
	readonly hasKParam = false;
	readonly isOriginalLeftIndep = false;
	readonly isTransformedLeftIndep = false;

	computeOrigSteps({ steps }: ConstructionParams): number {
		return steps;
	}

	getTransformedRange({ steps, wordLen }: ConstructionParams): { posLo: number; posHi: number } {
		return { posLo: -steps - 1, posHi: wordLen + steps };
	}

	getCellContent(params: ConstructionParams, i: number, t: number): TransformedCellContent {
		// Check if this cell is border (outside light cone of input)
		const isBorderCell = (i + t < 0) || (i + t >= params.wordLen);
		if (isBorderCell) {
			// Border cells show as empty
			return { type: "single", components: [{ origP: i, origT: -1 }] };  // -1 marks border
		}
		return { type: "single", components: [{ origP: i, origT: t }] };
	}

	getIntermediateStates(): IntermediateState[] { return []; }
	renderOriginalCell(ctx: OriginalCellRenderContext): React.ReactNode { return defaultRenderOriginalCell(ctx); }

	renderTransformedCell(ctx: TransformedCellRenderContext): React.ReactNode {
		const { cx, cy, i, t, content, getColor, hover, onHover } = ctx;
		const isTransDep = isTransformedDependency(hover, i, t);

		// Check if it's a border cell (marked with origT = -1)
		const isBorder = content.components[0].origT < 0;

		if (isBorder) {
			return (
				<circle
					cx={cx} cy={cy} r={6}
					fill="#f0f0f0" stroke="#ccc" strokeWidth={0.5}
					strokeDasharray="2,2"
				/>
			);
		}

		return (
			<StateCircle
				cx={cx} cy={cy} r={8}
				comp={content.components[0]}
				getColor={getColor} hover={hover} onHover={onHover}
				isExternalHighlight={isTransDep}
			/>
		);
	}
}

// ============================================================================
// CONSTRUCTION REGISTRY
// ============================================================================

export const CONSTRUCTIONS: Construction[] = [
	new LeftIndepSpeedupConstruction(),
	new RegularToLeftIndepConstruction(),
	new LeftIndepToRegularConstruction(),
	new FullPipelineConstruction(),
	new DiagSignalConstruction(),
	new CompressToDiagConstruction(),
	new DecompressTripleConstruction(),
	new SimFromLambdaConstruction(),
	new CompositionConstruction(),
	new TrueFullCompositionConstruction(),
	new FlipConstruction(),
	new ProductConstruction(),
	new AddBorderConstruction(),
];

export function getConstructionById(id: string): Construction | undefined {
	return CONSTRUCTIONS.find((c) => c.id === id);
}
