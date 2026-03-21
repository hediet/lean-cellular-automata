import type React from "react";

type SigState = "SR" | "SL" | "None";
type MirrorState = "M1" | "M2" | "M3" | "None";
type WordSymbol = "circle" | "star" | "none" | "border";

export type ExpWordQ = {
	readonly word: WordSymbol;
	readonly sig: SigState;
	readonly mirror: MirrorState;
	readonly unit: boolean;
};

const BORDER: ExpWordQ = { word: "border", sig: "None", mirror: "None", unit: false };

function expWordDelta(left: ExpWordQ, center: ExpWordQ, right: ExpWordQ): ExpWordQ {
	const atLeftEdge = left.word === "border";

	// Yellow symbols vanish after one step; at the left edge they trigger exp start
	const hasSymbol = center.word === "circle" || center.word === "star";
	if (hasSymbol) {
		if (atLeftEdge) {
			return { word: "none", sig: "SR", mirror: "M1", unit: true };
		}
		return { word: "none", sig: "None", mirror: "None", unit: false };
	}

	const lSig = left.sig;
	const lMirror = left.mirror;
	const rSig = right.sig;

	const mCenter = center.mirror;
	let m2: MirrorState;
	if (mCenter === "M1") m2 = "None";
	else if (mCenter === "M2") m2 = "M3";
	else if (mCenter === "M3") m2 = "M1";
	else m2 = lMirror === "M1" ? "M2" : "None";

	const u = center.unit;

	const incoming: SigState =
		lSig === "SR" ? "SR" :
		rSig === "SL" ? "SL" : "None";

	let s2: SigState;
	if (incoming === "SR") s2 = m2 === "M2" ? "SL" : "SR";
	else if (incoming === "SL") s2 = u ? "SR" : "SL";
	else s2 = "None";

	return { word: "none", sig: s2, mirror: m2, unit: u };
}

export function buildExpWordGrid(
	word: WordSymbol[],
	totalCells: number,
	wordStart: number,
	rows: number,
): ExpWordQ[][] {
	const grid: ExpWordQ[][] = [];

	const row0: ExpWordQ[] = Array.from({ length: totalCells }, (_, i) => {
		const wi = i - wordStart;
		if (wi >= 0 && wi < word.length) {
			return { word: word[wi], sig: "None" as const, mirror: "None" as const, unit: false };
		}
		return BORDER;
	});
	grid.push(row0);

	for (let t = 1; t < rows; t++) {
		const prev = grid[t - 1];
		const next = prev.map((_, i) => {
			const l = i > 0 ? prev[i - 1] : BORDER;
			const c = prev[i];
			const r = i < prev.length - 1 ? prev[i + 1] : BORDER;
			return expWordDelta(l, c, r);
		});
		grid.push(next);
	}

	return grid;
}

export function buildTrivialWordGrid(
	word: WordSymbol[],
	totalCells: number,
	wordStart: number,
	rows: number,
): ExpWordQ[][] {
	const grid: ExpWordQ[][] = [];
	const NONE: ExpWordQ = { word: "none", sig: "None", mirror: "None", unit: false };

	const row0: ExpWordQ[] = Array.from({ length: totalCells }, (_, i) => {
		const wi = i - wordStart;
		if (wi >= 0 && wi < word.length) {
			return { word: word[wi], sig: "None" as const, mirror: "None" as const, unit: false };
		}
		return BORDER;
	});
	grid.push(row0);

	for (let t = 1; t < rows; t++) {
		const prev = grid[t - 1];
		const next = prev.map((_, i) => {
			const c = prev[i];
			if (c.word === "circle" || c.word === "star") return NONE;
			return NONE;
		});
		grid.push(next);
	}

	return grid;
}

const CELL_SIZE = 24;
const GRID_MARGIN = 10;
const LABEL_W = 30;

const SIGNAL_COLOR = "#2563eb";
const MIRROR_COLOR = "#dc2626";
const SYMBOL_COLOR = "#f59e0b";

export function ExpWordGrid({ grid, wordStart, wordLen, coneHeight, coneRightCells, showCone, showInfluenceCone, restrictToWord, highlightCell, highlightLabel }: { grid: ExpWordQ[][]; wordStart?: number; wordLen?: number; coneHeight?: number; coneRightCells?: number; showCone?: boolean; showInfluenceCone?: boolean; restrictToWord?: boolean; highlightCell?: { col: number; row: number }; highlightLabel?: React.ReactNode }) {
	const rows = grid.length;
	const cols = grid[0].length;
	const cellsStartX = GRID_MARGIN;
	const viewW = 2 * GRID_MARGIN + cols * CELL_SIZE;
	const viewH = rows * CELL_SIZE;
	const viewX = -LABEL_W;
	const viewBoxW = viewW + LABEL_W;

	function cx(i: number) { return cellsStartX + i * CELL_SIZE; }

	return (
		<svg
			viewBox={`${viewX} 0 ${viewBoxW} ${viewH}`}
			preserveAspectRatio="xMidYMid meet"
			style={{ width: "100%", display: "block" }}
		>
			{grid.map((row, t) => {
				const y = t * CELL_SIZE;
				return (
					<g key={t}>
						<text
							x={cellsStartX - 6}
							y={y + CELL_SIZE / 2}
							textAnchor="end"
							dominantBaseline="central"
							fontSize={CELL_SIZE * 0.45}
							fill="#999"
							fontStyle="italic"
						>
							t={t}
						</text>
						{row.map((q, i) => {
							const x = cx(i);
							const { word, sig, mirror, unit } = q;
							const isBorder = word === "border";
							return (
								<g key={i}>
									<rect
										x={x} y={y}
										width={CELL_SIZE} height={CELL_SIZE}
										fill="#f5f5f5"
										stroke="#ddd"
										strokeWidth={0.5}
									/>
									{mirror !== "None" && (
										<polygon
											points={`${x + CELL_SIZE},${y} ${x + CELL_SIZE},${y + CELL_SIZE} ${x},${y}`}
											fill={MIRROR_COLOR}
											opacity={mirror === "M1" ? 1 : mirror === "M2" ? 0.7 : 0.4}
										/>
									)}
									{sig !== "None" && (
										<polygon
											points={`${x},${y + CELL_SIZE} ${x + CELL_SIZE},${y + CELL_SIZE} ${x},${y}`}
											fill={SIGNAL_COLOR}
											opacity={sig === "SR" ? 0.8 : 0.5}
										/>
									)}
									{word === "circle" && (
										<circle
											cx={x + CELL_SIZE / 2}
											cy={y + CELL_SIZE / 2}
											r={CELL_SIZE * 0.22}
											fill={SYMBOL_COLOR}
											stroke="#d97706"
											strokeWidth={0.8}
										/>
									)}
									{word === "star" && (
										<polygon
											points={starPoints(x + CELL_SIZE / 2, y + CELL_SIZE / 2, CELL_SIZE * 0.28, CELL_SIZE * 0.14, 5)}
											fill={SYMBOL_COLOR}
											stroke="#d97706"
											strokeWidth={0.8}
										/>
									)}
									{unit && (
										<rect
											x={x + 0.5} y={y + 0.5}
											width={CELL_SIZE - 1} height={CELL_SIZE - 1}
											fill="none"
											stroke="#000"
											strokeWidth={1}
										/>
									)}
								</g>
							);
						})}
					</g>
				);
			})}
			{showCone && wordStart !== undefined && wordLen !== undefined && (() => {
				const cs = CELL_SIZE;
				const h = coneHeight ?? (wordLen - 1);
				const rightCells = coneRightCells ?? wordLen;
				const x0 = cellsStartX + wordStart * cs;
				const xN = cellsStartX + (wordStart + rightCells) * cs;
				const y0 = 0;
				const yBottom = h * cs + cs;
				const xLeft = showInfluenceCone && !restrictToWord ? x0 - h * cs : x0;

				const r = 6;

				let pathParts: string[];

				if (restrictToWord) {
					// Rectangle from (0,0) to (wordLen,0) to (wordLen, wordLen-1),
					// then RT cone diagonal to (1, coneHeight), then straight left side
					const xW = cellsStartX + (wordStart + wordLen) * cs;
					const yMid = (wordLen - 1) * cs + cs; // bottom of row wordLen-1

					pathParts = [
						`M ${x0 + r},${y0}`,
						`L ${xW - r},${y0}`,
						`Q ${xW},${y0} ${xW},${y0 + r}`,
						`L ${xW},${yMid - r}`,
						`Q ${xW},${yMid} ${xW - r * 0.7},${yMid + r * 0.7}`,
						`L ${x0 + r * 0.7 + cs},${yBottom - r * 0.7}`,
						`Q ${x0 + cs},${yBottom} ${x0 + cs - r},${yBottom}`,
						`L ${x0 + r},${yBottom}`,
						`Q ${x0},${yBottom} ${x0},${yBottom - r}`,
						`L ${x0},${y0 + r}`,
						`Q ${x0},${y0} ${x0 + r},${y0}`,
						`Z`,
					];
				} else {
					const rightSide = rightCells > 1
						? [
							`L ${xN - r},${y0}`,
							`Q ${xN},${y0} ${xN},${y0 + r}`,
							`L ${xN},${y0 + cs - r}`,
							`Q ${xN},${y0 + cs} ${xN - r * 0.7},${y0 + cs + r * 0.7}`,
							`L ${x0 + r * 0.7 + cs},${yBottom - r * 0.7}`,
							`Q ${x0 + cs},${yBottom} ${x0 + cs - r},${yBottom}`,
						]
						: [
							`L ${xN - r},${y0}`,
							`Q ${xN},${y0} ${xN},${y0 + r}`,
							`L ${xN},${yBottom - r}`,
							`Q ${xN},${yBottom} ${xN - r},${yBottom}`,
						];

					const bottomAndLeft = showInfluenceCone
						? [
							`L ${x0 - r},${yBottom}`,
							`Q ${x0},${yBottom} ${x0 - r * 0.7},${yBottom - r * 0.7}`,
							`L ${xLeft + r * 0.7},${y0 + cs + r * 0.7}`,
							`Q ${xLeft},${y0 + cs} ${xLeft},${y0 + cs - r}`,
							`L ${xLeft},${y0 + r}`,
							`Q ${xLeft},${y0} ${xLeft + r},${y0}`,
						]
						: [
							`L ${x0 + r},${yBottom}`,
							`Q ${x0},${yBottom} ${x0},${yBottom - r}`,
							`L ${x0},${y0 + r}`,
							`Q ${x0},${y0} ${x0 + r},${y0}`,
						];

					pathParts = [
						`M ${xLeft + r},${y0}`,
						...rightSide,
						...bottomAndLeft,
						`Z`,
					];
				}

				return (
					<path
						d={pathParts.join(" ")}
						fill="none"
						stroke="#e74c3c"
						strokeWidth={2.5}
						strokeDasharray="6 3"
						opacity={0.8}
						style={{ transition: "d 0.5s ease" }}
					/>
				);
			})()}
			{highlightCell && (() => {
				const hx = cellsStartX + highlightCell.col * CELL_SIZE;
				const hy = highlightCell.row * CELL_SIZE;
				return (
					<g>
						<rect
							x={hx + 1.5} y={hy + 1.5}
							width={CELL_SIZE - 3} height={CELL_SIZE - 3}
							fill="none"
							stroke="#e74c3c"
							strokeWidth={2.5}
							strokeDasharray="6 3"
							rx={4}
							style={{ transition: "x 0.5s ease, y 0.5s ease" }}
						/>
						{highlightLabel && (
							<foreignObject
								x={hx - 366}
								y={hy}
								width={360}
								height={CELL_SIZE}
								style={{ transition: "y 0.5s ease" }}
							>
								<div style={{ fontSize: 13.2, color: "#000", fontWeight: "bold", lineHeight: `${CELL_SIZE}px`, whiteSpace: "nowrap", textAlign: "right" }}>
									{highlightLabel}
								</div>
							</foreignObject>
						)}
					</g>
				);
			})()}
		</svg>
	);
}

function starPoints(cx: number, cy: number, outerR: number, innerR: number, points: number): string {
	const pts: string[] = [];
	for (let i = 0; i < points * 2; i++) {
		const angle = (Math.PI / 2) * -1 + (Math.PI / points) * i;
		const r = i % 2 === 0 ? outerR : innerR;
		pts.push(`${cx + r * Math.cos(angle)},${cy + r * Math.sin(angle)}`);
	}
	return pts.join(" ");
}
