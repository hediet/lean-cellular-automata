import { Config } from "./ca-engine";
import { stateColor } from "./examples";

// Render a space-time diagram of a CA execution as SVG.
// Each row is a time step, each cell is a colored rectangle.
interface SpaceTimeDiagramProps {
	readonly configs: Config<number>[];
	readonly cellSize: number;
	readonly posRange: readonly [number, number]; // [lo, hi] inclusive
	readonly title?: string;
	// Optional: highlight mapping (compressed cell → original position/time)
	readonly highlights?: ReadonlyMap<string, { origPos: number; origTime: number }>;
}

export function SpaceTimeDiagram({
	configs,
	cellSize,
	posRange,
	title,
}: SpaceTimeDiagramProps) {
	const [lo, hi] = posRange;
	const width = (hi - lo + 1) * cellSize;
	const height = configs.length * cellSize;

	return (
		<svg
			width={width + (title ? 0 : 0)}
			height={height + (title ? 24 : 0)}
			style={{ display: "block" }}
		>
			{title && (
				<text x={width / 2} y={16} textAnchor="middle" fontSize={14} fontWeight="bold" fill="#333">
					{title}
				</text>
			)}
			<g transform={title ? "translate(0, 24)" : undefined}>
				{configs.map((config, t) =>
					Array.from({ length: hi - lo + 1 }, (_, idx) => {
						const pos = lo + idx;
						const q = config.get(pos);
						return (
							<rect
								key={`${t}-${pos}`}
								x={idx * cellSize}
								y={t * cellSize}
								width={cellSize}
								height={cellSize}
								fill={stateColor(q)}
								stroke="#ccc"
								strokeWidth={0.5}
							/>
						);
					})
				)}
			</g>
		</svg>
	);
}

// Render the compressed CA with k-tuple cells expanded into sub-columns.
// Each compressed cell at position i is rendered as k sub-columns.
interface CompressedDiagramProps {
	readonly configs: Config<{ tag: string; q?: number; w?: readonly number[] }>[];
	readonly k: number;
	readonly cellSize: number;
	readonly posRange: readonly [number, number];
	readonly title?: string;
}

export function CompressedDiagram({
	configs,
	k,
	cellSize,
	posRange,
	title,
}: CompressedDiagramProps) {
	const [lo, hi] = posRange;
	const numCells = hi - lo + 1;
	const subCellWidth = cellSize / k;
	const width = numCells * cellSize;
	const height = configs.length * cellSize;

	return (
		<svg width={width} height={height + (title ? 24 : 0)} style={{ display: "block" }}>
			{title && (
				<text x={width / 2} y={16} textAnchor="middle" fontSize={14} fontWeight="bold" fill="#333">
					{title}
				</text>
			)}
			<g transform={title ? "translate(0, 24)" : undefined}>
				{configs.map((config, t) =>
					Array.from({ length: numCells }, (_, idx) => {
						const pos = lo + idx;
						const state = config.get(pos);
						const values = stateValues(state, k);
						return (
							<g key={`${t}-${pos}`}>
								{values.map((v, j) => (
									<rect
										key={j}
										x={idx * cellSize + j * subCellWidth}
										y={t * cellSize}
										width={subCellWidth}
										height={cellSize}
										fill={stateColor(v)}
										stroke="#ccc"
										strokeWidth={0.3}
									/>
								))}
								{/* Cell boundary */}
								<rect
									x={idx * cellSize}
									y={t * cellSize}
									width={cellSize}
									height={cellSize}
									fill="none"
									stroke="#999"
									strokeWidth={1}
								/>
							</g>
						);
					})
				)}
			</g>
		</svg>
	);
}

function stateValues(
	state: { tag: string; q?: number; w?: readonly number[] },
	k: number
): number[] {
	if (state.tag === "single") {
		return Array.from({ length: k }, () => state.q ?? 0);
	}
	if (state.tag === "compr" && state.w) {
		return [...state.w] as number[];
	}
	return Array.from({ length: k }, () => 0);
}

// Side-by-side dual diagram showing the spec correspondence
interface DualDiagramProps {
	readonly origConfigs: Config<number>[];
	readonly compressedConfigs: Config<{ tag: string; q?: number; w?: readonly number[] }>[];
	readonly k: number;
	readonly origPosRange: readonly [number, number];
	readonly compPosRange: readonly [number, number];
	readonly cellSize: number;
	readonly ψ: (i: number, j: number) => number;
	readonly φ: (t: number, i: number, j: number) => number;
}

export function DualDiagram({
	origConfigs,
	compressedConfigs,
	k,
	origPosRange,
	compPosRange,
	cellSize,
	ψ,
	φ,
}: DualDiagramProps) {
	const [origLo, origHi] = origPosRange;
	const [compLo, compHi] = compPosRange;
	const origWidth = (origHi - origLo + 1) * cellSize;
	const compNumCells = compHi - compLo + 1;
	const compWidth = compNumCells * cellSize;
	const origHeight = origConfigs.length * cellSize;
	const compHeight = compressedConfigs.length * cellSize;
	const gap = 40;
	const headerH = 28;
	const totalWidth = origWidth + gap + compWidth;
	const totalHeight = Math.max(origHeight, compHeight) + headerH;
	const subCellWidth = cellSize / k;

	return (
		<svg width={totalWidth} height={totalHeight} style={{ display: "block" }}>
			{/* Original CA */}
			<text x={origWidth / 2} y={16} textAnchor="middle" fontSize={14} fontWeight="bold" fill="#333">
				Original CA
			</text>
			<g transform={`translate(0, ${headerH})`}>
				{origConfigs.map((config, t) =>
					Array.from({ length: origHi - origLo + 1 }, (_, idx) => {
						const pos = origLo + idx;
						const q = config.get(pos);
						return (
							<rect
								key={`o-${t}-${pos}`}
								x={idx * cellSize}
								y={t * cellSize}
								width={cellSize}
								height={cellSize}
								fill={stateColor(q)}
								stroke="#ddd"
								strokeWidth={0.5}
							/>
						);
					})
				)}
			</g>

			{/* Compressed CA */}
			<text
				x={origWidth + gap + compWidth / 2}
				y={16}
				textAnchor="middle"
				fontSize={14}
				fontWeight="bold"
				fill="#333"
			>
				Compressed CA (k={k})
			</text>
			<g transform={`translate(${origWidth + gap}, ${headerH})`}>
				{compressedConfigs.map((config, t) =>
					Array.from({ length: compNumCells }, (_, idx) => {
						const pos = compLo + idx;
						const state = config.get(pos);
						const values = stateValues(state, k);
						return (
							<g key={`c-${t}-${pos}`}>
								{values.map((v, j) => (
									<rect
										key={j}
										x={idx * cellSize + j * subCellWidth}
										y={t * cellSize}
										width={subCellWidth}
										height={cellSize}
										fill={stateColor(v)}
										stroke="#eee"
										strokeWidth={0.3}
									/>
								))}
								<rect
									x={idx * cellSize}
									y={t * cellSize}
									width={cellSize}
									height={cellSize}
									fill="none"
									stroke="#999"
									strokeWidth={1}
								/>
							</g>
						);
					})
				)}
			</g>

			{/* Correspondence lines for i < 0 */}
			<g opacity={0.3}>
				{compressedConfigs.map((_, t) =>
					Array.from({ length: compNumCells }, (_, idx) => {
						const pos = compLo + idx;
						if (pos >= 0) return null;
						return Array.from({ length: k }, (_, j) => {
							const origPos = ψ(pos, j);
							const origTime = φ(t, pos, j);
							if (origTime < 0 || origTime >= origConfigs.length) return null;
							if (origPos < origLo || origPos > origHi) return null;
							const cx =
								origWidth + gap + idx * cellSize + j * subCellWidth + subCellWidth / 2;
							const cy = headerH + t * cellSize + cellSize / 2;
							const ox = (origPos - origLo) * cellSize + cellSize / 2;
							const oy = headerH + origTime * cellSize + cellSize / 2;
							return (
								<line
									key={`l-${t}-${pos}-${j}`}
									x1={cx}
									y1={cy}
									x2={ox}
									y2={oy}
									stroke="#666"
									strokeWidth={0.5}
								/>
							);
						});
					})
				)}
			</g>
		</svg>
	);
}
