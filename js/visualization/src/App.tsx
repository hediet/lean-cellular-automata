import { observableValue, IDisposable, derived } from "@vscode/observables";
import { viewWithModel } from "@vscode/observables-react";
import {
    Construction,
    CONSTRUCTIONS,
    getConstructionById,
    HoverState,
    ConstructionParams,
    isDependency,
    getDependencies, SecondSimulation,
    SimStateInfo,
    FullSimStateInfo
} from "./constructions";

// ============================================================================
// CA SIMULATION
// ============================================================================

type State = number;

function delta3(left: State, center: State, right: State): State {
	if (left === 0 && center === 0 && right === 0) return 0;
	return 1 + ((left + center + right) % 7);
}

export function simulateCAWithWord(
	word: State[],
	maxT: number
): { grid: Map<string, State>; minPos: number; maxPos: number } {
	const grid = new Map<string, State>();
	const key = (p: number, t: number) => `${p},${t}`;

	const minPos = -maxT - 2;
	const maxPos = word.length + maxT + 3;

	for (let p = minPos; p <= maxPos; p++) {
		grid.set(key(p, 0), p >= 0 && p < word.length ? word[p] : 0);
	}

	for (let t = 1; t <= maxT; t++) {
		for (let p = minPos; p <= maxPos; p++) {
			const left = grid.get(key(p - 1, t - 1)) ?? 0;
			const center = grid.get(key(p, t - 1)) ?? 0;
			const right = grid.get(key(p + 1, t - 1)) ?? 0;
			grid.set(key(p, t), delta3(left, center, right));
		}
	}

	return { grid, minPos, maxPos };
}

function simulateCA(
	wordLen: number,
	maxT: number
): { grid: Map<string, State>; minPos: number; maxPos: number } {
	const word: State[] = [];
	for (let p = 0; p < wordLen; p++) word.push(1 + p);
	return simulateCAWithWord(word, maxT);
}

// ============================================================================
// COLOR UTILITIES
// ============================================================================

function coordColor(
	p: number,
	t: number,
	minP: number,
	maxP: number,
	maxT: number,
	isBorder: boolean,
	hueOffset = 0,
): string {
	if (isBorder) return "#ccc";
	const posRange = maxP - minP || 1;
	const hue = (240 - ((p - minP) / posRange) * 240 + hueOffset) % 360;
	const tNorm = maxT > 0 ? t / maxT : 0;
	const lightness = 45 + (1 - tNorm) * 25;
	const saturation = 70 + (1 - tNorm) * 20;
	return `hsl(${hue}, ${saturation}%, ${lightness}%)`;
}

// ============================================================================
// MODEL
// ============================================================================

class AppModel implements IDisposable {
	readonly constructionId = observableValue<string>(this, CONSTRUCTIONS[0].id);
	readonly k = observableValue<number>(this, 3);
	readonly steps = observableValue<number>(this, 4);
	readonly wordLen = observableValue<number>(this, 5);
	readonly hover = observableValue<HoverState>(this, null);
	readonly selectedCell = observableValue<{ p: number; t: number; diagram: "c1" | "c2" | "construction" } | null>(this, null);

	readonly construction = derived(this, (reader) => {
		const id = reader.readObservable(this.constructionId);
		return getConstructionById(id) ?? CONSTRUCTIONS[0];
	});

	readonly params = derived(this, (reader): ConstructionParams => ({
		k: reader.readObservable(this.k),
		steps: reader.readObservable(this.steps),
		wordLen: reader.readObservable(this.wordLen),
	}));

	readonly data = derived(this, (reader) => {
		const construction = reader.readObservable(this.construction);
		const params = reader.readObservable(this.params);
		const origSteps = construction.computeOrigSteps(params);
		const sim = simulateCA(params.wordLen, origSteps);
		const secondSim = construction.computeSecondSim?.(sim.grid, params, origSteps) ?? null;
		return { origSteps, grid: sim.grid, minPos: sim.minPos, maxPos: sim.maxPos, secondSim };
	});

	dispose() {}
}

// ============================================================================
// APP COMPONENT
// ============================================================================

export const App = viewWithModel(AppModel, (reader, model) => {
	const construction = reader.readObservable(model.construction);
	const params = reader.readObservable(model.params);
	const data = reader.readObservable(model.data);
	const hover = reader.readObservable(model.hover);
	const selectedCell = reader.readObservable(model.selectedCell);

	const selectCell = (p: number, t: number, diagram: "c1" | "c2" | "construction") => {
		model.selectedCell.set({ p, t, diagram }, undefined);
	};

	const selectedInfo = (() => {
		if (!selectedCell) return null;
		const { p, t, diagram } = selectedCell;
		const key = `${p},${t}`;
		if (diagram === "c1") {
			const state = data.grid.get(key) ?? 0;
			return { diagram: "C1", p, t, state, isBorder: state === 0 };
		}
		if (diagram === "c2" && data.secondSim) {
			const state = data.secondSim.grid.get(key) ?? 0;
			return { diagram: "C2", p, t, state, isBorder: state === 0 };
		}
		if (diagram === "construction" && data.secondSim?.constructionStates) {
			const simState = data.secondSim.constructionStates.get(key);
			if (simState) {
				const c2Key = `${p},${simState.innerStep}`;
				const c2Val = data.secondSim.grid.get(c2Key) ?? null;
				return {
					diagram: "Construction (SimFromΛ)",
					p, t,
					...simState,
					c2GridPos: `(${p}, ${simState.innerStep})`,
					c2GridVal: c2Val,
					matchesC2: simState.counter === 0 && simState.triggered ? simState.innerCur === c2Val : null,
				};
			}
		}
		if (diagram === "construction" && data.secondSim?.fullConstructionStates) {
			const state = data.secondSim.fullConstructionStates.get(key);
			if (state) {
				// Spec: C2_3x.trace(compress(c), t1+1)[t2] = C2.trace(c, 3*t1 + t2)
				// innerStep counts delta invocations. innerStep=n means t1+1=n, so t1=n-1.
				// Valid only for innerStep >= 1.
				const c2Matches: { t2: number; expected: number; actual: number | null }[] = [];
				if (state.innerCurProjected && state.innerStep >= 1) {
					for (let j = 0; j < 3; j++) {
						const c2Time = 3 * (state.innerStep - 1) + j;
						const c2Val = data.secondSim.grid.get(`0,${c2Time}`) ?? null;
						c2Matches.push({ t2: c2Time, expected: state.innerCurProjected[j], actual: c2Val });
					}
				}
				return {
					diagram: "True Composition (SimFromΛ + C2_3x + DecompressTriple)",
					p, t,
					...state,
					c2Matches,
					decompOutput: state.output,
				};
			}
		}
		return null;
	})();

	return (
		<div style={{ fontFamily: "system-ui, sans-serif", padding: 20 }}>
			<h1 style={{ margin: "0 0 16px" }}>CA Construction Visualizer</h1>

			<div style={{ display: "flex", gap: 24, marginBottom: 20, flexWrap: "wrap", alignItems: "center" }}>
				<label>
					Construction:{" "}
					<select
						value={construction.id}
						onChange={(e) => model.constructionId.set(e.target.value, undefined)}
						style={{ padding: "4px 8px" }}
					>
						{CONSTRUCTIONS.map((c) => (
							<option key={c.id} value={c.id}>
								{c.name}
							</option>
						))}
					</select>
				</label>
				{construction.hasKParam && (
					<label>
						k:{" "}
						<input
							type="range"
							min={2}
							max={6}
							value={params.k}
							onChange={(e) => model.k.set(Number(e.target.value), undefined)}
						/>
						{" "}{params.k}
					</label>
				)}
				<label>
					Steps:{" "}
					<input
						type="range"
						min={2}
						max={10}
						value={params.steps}
						onChange={(e) => model.steps.set(Number(e.target.value), undefined)}
					/>
					{" "}{params.steps}
				</label>
				<label>
					Word length:{" "}
					<input
						type="range"
						min={3}
						max={8}
						value={params.wordLen}
						onChange={(e) => model.wordLen.set(Number(e.target.value), undefined)}
					/>
					{" "}{params.wordLen}
				</label>
			</div>

			<div
				style={{ marginBottom: 16, fontSize: 13, color: "#555" }}
				dangerouslySetInnerHTML={{ __html: construction.description }}
			/>

			<div style={{ display: "flex", gap: 60, overflowX: "auto", alignItems: "flex-start" }}>
				<OriginalCADiagram
					construction={construction}
					params={params}
					origSteps={data.origSteps}
					grid={data.grid}
					minPos={data.minPos}
					maxPos={data.maxPos}
					hover={hover}
					setHover={(h) => model.hover.set(h, undefined)}
					hasSecondSim={data.secondSim !== null}
				/>
				<TransformedCADiagram
					construction={construction}
					params={params}
					origSteps={data.origSteps}
					grid={data.grid}
					secondSim={data.secondSim}
					hover={hover}
					setHover={(h) => model.hover.set(h, undefined)}
				/>
			</div>

			{data.secondSim?.constructionGrid && !data.secondSim?.fullConstructionStates && (
				<ConstructionDiagram
					constructionGrid={data.secondSim.constructionGrid}
					constructionMaxT={data.secondSim.constructionMaxT!}
					constructionStates={data.secondSim.constructionStates}
					c1Grid={data.grid}
					c2Grid={data.secondSim.grid}
					c1Trace={data.secondSim.c1Trace ?? []}
					params={params}
					origSteps={data.origSteps}
					hover={hover}
					setHover={(h) => model.hover.set(h, undefined)}
					onCellClick={(p, t) => selectCell(p, t, "construction")}
				/>
			)}

			{data.secondSim?.fullConstructionStates && (
				<TrueCompositionDiagram
					constructionGrid={data.secondSim.constructionGrid!}
					constructionMaxT={data.secondSim.constructionMaxT!}
					states={data.secondSim.fullConstructionStates}
					c1Grid={data.grid}
					c2Grid={data.secondSim.grid}
					c1Trace={data.secondSim.c1Trace ?? []}
					params={params}
					onCellClick={(p, t) => selectCell(p, t, "construction")}
				/>
			)}

			{selectedInfo && (
				<div style={{
					marginTop: 16, padding: 12, background: "#f5f5f5", borderRadius: 6,
					fontFamily: "monospace", fontSize: 12, maxWidth: 600, whiteSpace: "pre-wrap",
				}}>
					<strong>Selected Cell State</strong>
					<button
						onClick={() => model.selectedCell.set(null, undefined)}
						style={{ float: "right", cursor: "pointer", border: "none", background: "none", fontSize: 14 }}
					>✕</button>
					<pre style={{ margin: "8px 0 0", fontSize: 11 }}>
						{JSON.stringify(selectedInfo, null, 2)}
					</pre>
				</div>
			)}
		</div>
	);
});

// ============================================================================
// ORIGINAL CA DIAGRAM
// ============================================================================

function OriginalCADiagram({
	construction,
	params,
	origSteps,
	grid,
	minPos,
	maxPos,
	hover,
	setHover,
	hasSecondSim,
}: {
	construction: Construction;
	params: ConstructionParams;
	origSteps: number;
	grid: Map<string, State>;
	minPos: number;
	maxPos: number;
	hover: HoverState;
	setHover: (h: HoverState) => void;
	hasSecondSim: boolean;
}) {
	const cellSize = 24;
	const circleR = 8;
	const { wordLen } = params;

	const displayMinPos = Math.max(minPos, -origSteps - 1);
	const displayMaxPos = Math.min(maxPos, wordLen + origSteps + 1);
	const numPos = displayMaxPos - displayMinPos + 1;

	const width = numPos * cellSize + 40;
	const height = (origSteps + 1) * cellSize + 50;

	const key = (p: number, t: number) => `${p},${t}`;

	return (
		<svg width={width} height={height}>
			<text x={width / 2} y={20} textAnchor="middle" fontSize={14} fontWeight="bold" fill="#333">
				{hasSecondSim ? `C1 Simulation (${origSteps} steps)` : `Original CA (${origSteps} steps)`}
			</text>

			<g transform="translate(30, 45)">
				{range(0, origSteps - 1).map((t) =>
					range(displayMinPos, displayMaxPos).map((p) => {
						const cx = (p - displayMinPos) * cellSize + cellSize / 2;
						const cy = (t + 1) * cellSize;
						// Check if this cell (p, t+1) is hovered - if so, highlight its dependency lines
						const isTargetHovered = hover !== null && hover.origP === p && hover.origT === t + 1;
						const highlightCenter = isTargetHovered;
						const highlightRight = isTargetHovered;
						const highlightLeft = isTargetHovered && !construction.isOriginalLeftIndep;
						return (
							<g key={`dep-${t}-${p}`}>
								{!construction.isOriginalLeftIndep && (
									<line
										x1={cx - cellSize}
										y1={cy - cellSize}
										x2={cx}
										y2={cy}
										stroke={highlightLeft ? "#f00" : "#ddd"}
										strokeWidth={highlightLeft ? 2 : 1}
									/>
								)}
								<line
									x1={cx}
									y1={cy - cellSize}
									x2={cx}
									y2={cy}
									stroke={highlightCenter ? "#f00" : "#ddd"}
									strokeWidth={highlightCenter ? 2 : 1}
								/>
								{p + 1 <= displayMaxPos && (
									<line
										x1={cx + cellSize}
										y1={cy - cellSize}
										x2={cx}
										y2={cy}
										stroke={highlightRight ? "#f00" : "#ddd"}
										strokeWidth={highlightRight ? 2 : 1}
									/>
								)}
							</g>
						);
					})
				)}

				{range(0, origSteps).map((t) =>
					range(displayMinPos, displayMaxPos).map((p) => {
						const cx = (p - displayMinPos) * cellSize + cellSize / 2;
						const cy = t * cellSize;
						const state = grid.get(key(p, t)) ?? 0;
						const isBorder = state === 0;
						const color = coordColor(p, t, 0, wordLen - 1, origSteps, isBorder);
						const isHovered = hover !== null && hover.origP === p && hover.origT === t;
						const isDep = isDependency(hover, p, t);
						const setHoverWithDeps = (h: HoverState) => {
							if (h) {
								setHover({ ...h, deps: getDependencies(h.origP, h.origT, construction.isOriginalLeftIndep) });
							} else {
								setHover(null);
							}
						};
						return (
							<g key={`c-${t}-${p}`}>
								{construction.renderOriginalCell({
									cx,
									cy,
									p,
									t,
									circleR,
									color,
									isBorder,
									isHighlighted: isHovered,
									isDependency: isDep,
									onHover: setHoverWithDeps,
								})}
							</g>
						);
					})
				)}

				{range(displayMinPos, displayMaxPos).map((p) => (
					<text
						key={`pl-${p}`}
						x={(p - displayMinPos) * cellSize + cellSize / 2}
						y={-8}
						textAnchor="middle"
						fontSize={9}
						fill="#666"
					>
						{p}
					</text>
				))}

				{range(0, origSteps).map((t) => (
					<text key={`tl-${t}`} x={-12} y={t * cellSize + 4} textAnchor="middle" fontSize={9} fill="#666">
						{t}
					</text>
				))}
			</g>
		</svg>
	);
}

// ============================================================================
// TRANSFORMED CA DIAGRAM
// ============================================================================

function TransformedCADiagram({
	construction,
	params,
	origSteps,
	grid,
	secondSim,
	hover,
	setHover,
}: {
	construction: Construction;
	params: ConstructionParams;
	origSteps: number;
	grid: Map<string, State>;
	secondSim: SecondSimulation | null;
	hover: HoverState;
	setHover: (h: HoverState) => void;
}) {
	const cellSize = 32;
	const { steps, wordLen } = params;
	const { posLo, posHi } = construction.getTransformedRange(params);
	const numPos = posHi - posLo + 1;

	const width = numPos * cellSize + 50;
	const height = (steps + 1) * cellSize + 50;

	const key = (p: number, t: number) => `${p},${t}`;

	const useSecondGrid = secondSim !== null;
	const activeGrid = useSecondGrid ? secondSim.grid : grid;
	const activeWordLen = useSecondGrid ? secondSim.wordLen : wordLen;
	const activeMaxT = useSecondGrid ? secondSim.maxT : origSteps;
	const hueOffset = useSecondGrid ? 120 : 0;

	const getColor = (origP: number, origT: number) => {
		const state = origT >= 0 ? (activeGrid.get(key(origP, origT)) ?? 0) : 0;
		const isBorder = state === 0;
		const color = coordColor(origP, origT, 0, activeWordLen - 1, activeMaxT, isBorder, hueOffset);
		return { color, isBorder };
	};

	return (
		<svg width={width} height={height}>
			<text x={width / 2} y={20} textAnchor="middle" fontSize={14} fontWeight="bold" fill="#333">
				{useSecondGrid ? `C2 Simulation (${steps} steps)` : `Transformed CA (${steps} steps)`}
			</text>

			<g transform="translate(40, 45)">
				{range(0, steps - 1).map((t) =>
					range(posLo, posHi).map((i) => {
						const cx = (i - posLo) * cellSize + cellSize / 2;
						const cy = (t + 1) * cellSize;
						const isTargetHovered = hover !== null && hover.transI === i && hover.transT === t + 1;
						const highlightCenter = isTargetHovered;
						const highlightRight = isTargetHovered;
						const highlightLeft = isTargetHovered && !construction.isTransformedLeftIndep;
						return (
							<g key={`dep-${t}-${i}`}>
								{!construction.isTransformedLeftIndep && (
									<line
										x1={cx - cellSize}
										y1={cy - cellSize}
										x2={cx}
										y2={cy}
										stroke={highlightLeft ? "#f00" : "#ccc"}
										strokeWidth={highlightLeft ? 2 : 1}
									/>
								)}
								<line
									x1={cx}
									y1={cy - cellSize}
									x2={cx}
									y2={cy}
									stroke={highlightCenter ? "#f00" : "#ccc"}
									strokeWidth={highlightCenter ? 2 : 1}
								/>
								{i + 1 <= posHi && (
									<line
										x1={cx + cellSize}
										y1={cy - cellSize}
										x2={cx}
										y2={cy}
										stroke={highlightRight ? "#f00" : "#ccc"}
										strokeWidth={highlightRight ? 2 : 1}
									/>
								)}
							</g>
						);
					})
				)}

				{range(0, steps).map((t) =>
					range(posLo, posHi).map((i) => {
						const cx = (i - posLo) * cellSize + cellSize / 2;
						const cy = t * cellSize;
						const content = construction.getCellContent(params, i, t);
						const setHoverWithDeps = (h: HoverState) => {
							if (h) {
								const transDeps = getTransformedDeps(i, t, construction.isTransformedLeftIndep);
								setHover({
									...h,
									transI: i,
									transT: t,
									deps: getDependencies(h.origP, h.origT, construction.isOriginalLeftIndep),
									transDeps,
								});
							} else {
								setHover(null);
							}
						};
						return (
							<g key={`cell-${t}-${i}`}>
								{construction.renderTransformedCell({
									cx,
									cy,
									i,
									t,
									cellSize,
									content,
									getColor,
									hover,
									onHover: setHoverWithDeps,
								})}
							</g>
						);
					})
				)}

				{range(0, steps - 1).map((t) => {
					const intermediates = construction.getIntermediateStates(params, t);
					return intermediates.map((int, idx) => {
						const cx = (int.column - posLo) * cellSize + cellSize / 2;
						const cy = t * cellSize + cellSize / 2;
						const { color, isBorder } = getColor(int.origP, int.origT);
						const isHovered = hover !== null && hover.origP === int.origP && hover.origT === int.origT;
						const isDepHL = isDependency(hover, int.origP, int.origT);
						const r = 5;

						return (
							<g key={`inter-${t}-${idx}`}>
								<circle
									cx={cx}
									cy={cy}
									r={isHovered ? r + 2 : r}
									fill={color}
									stroke={isHovered || isDepHL ? "#000" : isBorder ? "#aaa" : "#555"}
									strokeWidth={isHovered ? 2 : isDepHL ? 1.5 : isBorder ? 0.3 : 0.6}
									opacity={isBorder ? 0.4 : 0.85}
									style={{ cursor: "pointer" }}
									onMouseEnter={() => {
										setHover({
											origP: int.origP,
											origT: int.origT,
											deps: getDependencies(int.origP, int.origT, construction.isOriginalLeftIndep),
										});
									}}
									onMouseLeave={() => setHover(null)}
								/>
							</g>
						);
					});
				})}

				{range(posLo, posHi).map((p) => (
					<text
						key={`pl-${p}`}
						x={(p - posLo) * cellSize + cellSize / 2}
						y={-10}
						textAnchor="middle"
						fontSize={9}
						fill="#666"
					>
						{p}
					</text>
				))}

				{range(0, steps).map((t) => (
					<text key={`tl-${t}`} x={-14} y={t * cellSize + 4} textAnchor="middle" fontSize={9} fill="#666">
						{t}
					</text>
				))}
			</g>
		</svg>
	);
}

// ============================================================================
// CONSTRUCTION EXECUTION DIAGRAM
// ============================================================================

function ConstructionDiagram({
	constructionGrid,
	constructionMaxT,
	constructionStates,
	c1Grid,
	c2Grid,
	c1Trace,
	params,
	origSteps,
	hover,
	setHover,
	onCellClick,
}: {
	constructionGrid: Map<string, number>;
	constructionMaxT: number;
	constructionStates?: Map<string, SimStateInfo>;
	c1Grid: Map<string, number>;
	c2Grid: Map<string, number>;
	c1Trace: number[];
	params: ConstructionParams;
	origSteps: number;
	hover: HoverState;
	setHover: (h: HoverState) => void;
	onCellClick: (p: number, t: number) => void;
}) {
	const cellSize = 32;
	const maxP = Math.min(Math.floor(constructionMaxT / 2), params.steps + 2);
	const posLo = -Math.min(maxP, 3);
	const posHi = maxP;
	const numPos = posHi - posLo + 1;

	const width = numPos * cellSize + 60;
	const height = (constructionMaxT + 1) * cellSize + 50;

	const key = (p: number, t: number) => `${p},${t}`;

	// C2 palette (green-shifted)
	const c2Color = (val: number) => {
		if (val === 0) return "#bbb";
		const hue = (120 + (val * 40)) % 360;
		return `hsl(${hue}, 70%, 50%)`;
	};

	// C1 palette (blue-red)
	const c1Color = (val: number) => {
		if (val === 0) return "#ccc";
		const hue = 240 - ((val - 1) / Math.max(params.wordLen - 1, 1)) * 240;
		return `hsl(${hue}, 80%, 55%)`;
	};

	return (
		<svg width={width} height={height}>
			<text x={width / 2} y={20} textAnchor="middle" fontSize={14} fontWeight="bold" fill="#333">
				Construction Execution (SimFromΛ)
			</text>

			<g transform="translate(40, 45)">
				{range(0, constructionMaxT).map((t) =>
					range(posLo, posHi).map((p) => {
						const cx = (p - posLo) * cellSize + cellSize / 2;
						const cy = t * cellSize;
						const state = constructionStates?.get(key(p, t));
						const diagTime = 3 + 2 * Math.abs(p);
						const onDiag = t === diagTime;

						if (!state || !state.triggered) {
							if (onDiag && p >= 0) {
								// Diagonal trigger: show C1 triple
								const triple = [
									3 * p < c1Trace.length ? c1Trace[3 * p] : 0,
									3 * p + 1 < c1Trace.length ? c1Trace[3 * p + 1] : 0,
									3 * p + 2 < c1Trace.length ? c1Trace[3 * p + 2] : 0,
								];
								return (
									<g key={`cc-${t}-${p}`} onClick={() => onCellClick(p, t)} style={{ cursor: "pointer" }}>
										<rect
											x={cx - cellSize / 2 + 1} y={cy - cellSize / 2 + 1}
											width={cellSize - 2} height={cellSize - 2}
											fill="#fff" stroke="#e74c3c" strokeWidth={1.5} rx={3}
										/>
										{triple.map((v, j) => (
											<g key={j}>
												<circle
													cx={cx + (j - 1) * 8} cy={cy - 4} r={3}
													fill={c1Color(v)} stroke="#c0392b" strokeWidth={0.4}
												/>
												<text x={cx + (j - 1) * 8} y={cy + 8} textAnchor="middle" fontSize={4} fill="#999">
													t{3 * p + j}
												</text>
											</g>
										))}
									</g>
								);
							}
							return (
								<circle
									key={`cc-${t}-${p}`}
									cx={cx} cy={cy} r={2}
									fill="#eee" stroke="#ddd" strokeWidth={0.3}
								/>
							);
						}

						// Triggered cell with nested state
						const isOutput = state.counter === 0;
						const innerVal = state.innerCur;
						const prevVal = state.innerPrev;
						const step = state.innerStep;
						const triple = state.triggerTriple;

						// Look up the corresponding C2 state for verification
						const c2Val = c2Grid.get(key(p, step)) ?? -1;
						const matches = innerVal === c2Val;

						return (
							<g key={`cc-${t}-${p}`} onClick={() => onCellClick(p, t)} style={{ cursor: "pointer" }}>
								<rect
									x={cx - cellSize / 2 + 1} y={cy - cellSize / 2 + 1}
									width={cellSize - 2} height={cellSize - 2}
									fill={isOutput ? "#f8f8f8" : "#fafafa"}
									stroke={isOutput ? (matches ? "#2ecc71" : "#e74c3c") : "#ddd"}
									strokeWidth={isOutput ? 1.5 : 0.5}
									rx={2}
								/>
								{/* C1 source: small dots top-left showing trigger triple */}
								{triple.some((v) => v !== 0) && (
									<>
										{triple.map((v, j) => (
											<circle
												key={`c1-${j}`}
												cx={cx - 8 + j * 5} cy={cy - 9} r={2}
												fill={c1Color(v)} stroke="#aaa" strokeWidth={0.2}
											/>
										))}
									</>
								)}
								{/* C2 inner state: main circle */}
								<circle
									cx={cx} cy={cy + 1} r={isOutput ? 8 : 5}
									fill={c2Color(innerVal)}
									stroke={isOutput ? "#000" : "#777"}
									strokeWidth={isOutput ? 1.2 : 0.4}
								/>
								{isOutput && (
									<text
										x={cx} y={cy + 3.5}
										textAnchor="middle" fontSize={6}
										fill="#fff" pointerEvents="none" fontWeight="bold"
									>
										{innerVal}
									</text>
								)}
								{/* C2 prev state: small circle bottom-left */}
								<circle
									cx={cx - 8} cy={cy + 8} r={2}
									fill={c2Color(prevVal)}
									stroke="#999" strokeWidth={0.2}
									opacity={0.6}
								/>
								{/* Step + phase label */}
								<text
									x={cx + 8} y={cy + 10}
									textAnchor="middle" fontSize={3.5}
									fill="#999" pointerEvents="none"
								>
									s{step} φ{state.counter}
								</text>
							</g>
						);
					})
				)}

				{range(posLo, posHi).map((p) => (
					<text
						key={`pl-${p}`}
						x={(p - posLo) * cellSize + cellSize / 2}
						y={-8}
						textAnchor="middle"
						fontSize={8}
						fill="#666"
					>
						{p}
					</text>
				))}

				{range(0, constructionMaxT).filter((t) => t % 3 === 0).map((t) => (
					<text key={`tl-${t}`} x={-14} y={t * cellSize + 3} textAnchor="middle" fontSize={7} fill="#666">
						{t}
					</text>
				))}
			</g>
		</svg>
	);
}

function range(lo: number, hi: number): number[] {
	const result: number[] = [];
	for (let i = lo; i <= hi; i++) result.push(i);
	return result;
}

// ============================================================================
// TRUE COMPOSITION DIAGRAM
// ============================================================================
//
// Shows the full pipeline: C1 trace → CompressToΛ → SimFromΛ(C2_3x) → DecompressTriple
// Each cell shows:
//   - C1 trigger triple (top, small blue-red dots)
//   - C2_3x projected output triple (center, 3 green circles)
//   - DecompressTriple output (bottom indicator)
//   - Phase counter + inner step

function TrueCompositionDiagram({
	constructionGrid,
	constructionMaxT,
	states,
	c1Grid,
	c2Grid,
	c1Trace,
	params,
	onCellClick,
}: {
	constructionGrid: Map<string, number>;
	constructionMaxT: number;
	states: Map<string, FullSimStateInfo>;
	c1Grid: Map<string, number>;
	c2Grid: Map<string, number>;
	c1Trace: number[];
	params: ConstructionParams;
	onCellClick: (p: number, t: number) => void;
}) {
	const cellSize = 38;
	const maxP = Math.min(Math.floor(constructionMaxT / 2), params.steps + 2);
	const posLo = -Math.min(maxP, 3);
	const posHi = maxP;
	const numPos = posHi - posLo + 1;

	const width = numPos * cellSize + 60;
	const height = (constructionMaxT + 1) * cellSize + 50;

	const key = (p: number, t: number) => `${p},${t}`;

	// C2 palette (green-shifted)
	const c2Color = (val: number | null) => {
		if (val === null || val === 0) return "#bbb";
		const hue = (120 + (val * 40)) % 360;
		return `hsl(${hue}, 70%, 50%)`;
	};

	// C1 palette (blue-red)
	const c1Color = (val: number | null) => {
		if (val === null || val === 0) return "#ccc";
		const hue = 240 - ((val - 1) / Math.max(params.wordLen - 1, 1)) * 240;
		return `hsl(${hue}, 80%, 55%)`;
	};

	return (
		<svg width={width} height={height}>
			<text x={width / 2} y={20} textAnchor="middle" fontSize={14} fontWeight="bold" fill="#333">
				True Composition: SimFromΛ(C1_Λ, C2_3x) → DecompressTriple
			</text>

			<g transform="translate(40, 45)">
				{range(0, constructionMaxT).map((t) =>
					range(posLo, posHi).map((p) => {
						const cx = (p - posLo) * cellSize + cellSize / 2;
						const cy = t * cellSize;
						const state = states.get(key(p, t));
						const diagTime = 3 + 2 * Math.abs(p);
						const onDiag = t === diagTime;

						if (!state || !state.triggered) {
							if (onDiag && p >= 0) {
								// Diagonal trigger: show C1 triple
								const tripleVals = [
									3 * p < c1Trace.length ? c1Trace[3 * p] : 0,
									3 * p + 1 < c1Trace.length ? c1Trace[3 * p + 1] : 0,
									3 * p + 2 < c1Trace.length ? c1Trace[3 * p + 2] : 0,
								];
								return (
									<g key={`cc-${t}-${p}`} onClick={() => onCellClick(p, t)} style={{ cursor: "pointer" }}>
										<rect
											x={cx - cellSize / 2 + 1} y={cy - cellSize / 2 + 1}
											width={cellSize - 2} height={cellSize - 2}
											fill="#fff" stroke="#e74c3c" strokeWidth={1.5} rx={3}
										/>
										<text x={cx} y={cy - 10} textAnchor="middle" fontSize={4} fill="#c0392b">
											C1 trigger
										</text>
										{tripleVals.map((v, j) => (
											<g key={j}>
												<circle cx={cx + (j - 1) * 10} cy={cy} r={5}
													fill={c1Color(v)} stroke="#c0392b" strokeWidth={0.6}
												/>
												<text x={cx + (j - 1) * 10} y={cy + 2} textAnchor="middle" fontSize={5} fill="#fff">
													{v}
												</text>
												<text x={cx + (j - 1) * 10} y={cy + 11} textAnchor="middle" fontSize={3.5} fill="#999">
													t={3 * p + j}
												</text>
											</g>
										))}
									</g>
								);
							}
							return (
								<circle key={`cc-${t}-${p}`} cx={cx} cy={cy} r={2}
									fill="#eee" stroke="#ddd" strokeWidth={0.3}
								/>
							);
						}

						// Triggered cell
						const isOutput = state.counter === 0;
						const projected = state.innerCurProjected;
						const step = state.innerStep;
						const trigger = state.triggerTriple;
						const decompC = state.decompCounter;
						const decompS = state.decompStored;

						// Verify against C2 grid
						// Spec: after innerStep delta steps (= t1+1 total), output[j] = C2.trace(c, 3*(innerStep-1) + j)
						// Valid only for innerStep >= 1
						let allMatch = true;
						if (projected && isOutput && step >= 1) {
							for (let j = 0; j < 3; j++) {
								const c2Time = 3 * (step - 1) + j;
								const c2Val = c2Grid.get(`0,${c2Time}`) ?? 0;
								if (projected[j] !== c2Val) allMatch = false;
							}
						} else if (step === 0) {
							allMatch = true; // embed state — no spec to verify against
						}

						return (
							<g key={`cc-${t}-${p}`} onClick={() => onCellClick(p, t)} style={{ cursor: "pointer" }}>
								<rect
									x={cx - cellSize / 2 + 1} y={cy - cellSize / 2 + 1}
									width={cellSize - 2} height={cellSize - 2}
									fill={isOutput ? "#fafafa" : "#fdfdfd"}
									stroke={isOutput ? (allMatch ? "#2ecc71" : "#e74c3c") : "#eee"}
									strokeWidth={isOutput ? 1.5 : 0.5}
									rx={2}
								/>

								{/* Top row: C1 trigger triple (small dots) */}
								{trigger.some(v => v !== null && v !== 0) && (
									<>
										{trigger.map((v, j) => (
											<circle key={`c1-${j}`}
												cx={cx - 8 + j * 8} cy={cy - 12} r={2.5}
												fill={c1Color(v)} stroke="#aaa" strokeWidth={0.3}
											/>
										))}
									</>
								)}

								{/* Center: C2_3x output triple (3 circles) */}
								{projected ? projected.map((v, j) => {
									// Highlight the element selected by DecompressTriple
									const isDecompActive = isOutput && decompC === j;
									return (
										<g key={`c2-${j}`}>
											<circle
												cx={cx + (j - 1) * 10} cy={cy + 1}
												r={isDecompActive ? 7 : 5}
												fill={c2Color(v)}
												stroke={isDecompActive ? "#000" : "#777"}
												strokeWidth={isDecompActive ? 1.5 : 0.4}
											/>
											<text
												x={cx + (j - 1) * 10} y={cy + 3}
												textAnchor="middle" fontSize={isDecompActive ? 6 : 4.5}
												fill="#fff" pointerEvents="none"
												fontWeight={isDecompActive ? "bold" : "normal"}
											>
												{v}
											</text>
										</g>
									);
								}) : (
									<circle cx={cx} cy={cy + 1} r={4}
										fill="#ddd" stroke="#bbb" strokeWidth={0.3}
									/>
								)}

								{/* Bottom: step + phase + decompress info */}
								<text
									x={cx} y={cy + 14}
									textAnchor="middle" fontSize={3.5}
									fill="#999" pointerEvents="none"
								>
									s{step} φ{state.counter} d{decompC}
								</text>
							</g>
						);
					})
				)}

				{/* Position labels */}
				{range(posLo, posHi).map((p) => (
					<text key={`pl-${p}`}
						x={(p - posLo) * cellSize + cellSize / 2} y={-8}
						textAnchor="middle" fontSize={8} fill="#666"
					>
						{p}
					</text>
				))}

				{/* Time labels */}
				{range(0, constructionMaxT).filter((t) => t % 3 === 0).map((t) => (
					<text key={`tl-${t}`} x={-14} y={t * cellSize + 3}
						textAnchor="middle" fontSize={7} fill="#666">
						{t}
					</text>
				))}
			</g>
		</svg>
	);
}

function getTransformedDeps(i: number, t: number, isLeftIndep: boolean): { i: number; t: number }[] {
	if (t <= 0) return [];
	if (isLeftIndep) {
		return [
			{ i, t: t - 1 },
			{ i: i + 1, t: t - 1 },
		];
	}
	return [
		{ i: i - 1, t: t - 1 },
		{ i, t: t - 1 },
		{ i: i + 1, t: t - 1 },
	];
}
