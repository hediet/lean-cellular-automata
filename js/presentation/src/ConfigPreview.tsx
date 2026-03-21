const MARGIN = 40;
const CELL_H = 48;
const GAP = 48;
const FONT_SIZE = 20;

interface ConfigPreviewProps {
	states0: string[];
	states1: string[];
	showRow0: boolean;
	showRow1: boolean;
	highlightInputs?: number[];
	slideDown?: number[];
	revealedCells: number[];
	revealRest: boolean;
	highlightResult?: number[];
	deltaTarget?: number;
	showDelta: boolean;
	colorMode?: boolean;
	compact?: boolean;
	extraRows?: string[][];
	showExtraRows?: boolean;
	markedCell?: number;
}

export function ConfigPreview({
	states0,
	states1,
	showRow0,
	showRow1,
	highlightInputs,
	slideDown,
	revealedCells,
	revealRest,
	highlightResult,
	deltaTarget,
	showDelta,
	colorMode = false,
	compact = false,
	extraRows = [],
	showExtraRows = false,
	markedCell,
}: ConfigPreviewProps) {
	const n = states0.length;
	const cellH = compact ? CELL_H / 2 : CELL_H;
	const gap = compact ? 0 : GAP;
	const visibleExtraRows = compact ? extraRows : [];
	const numRows = 2 + visibleExtraRows.length;
	const margin = compact ? 10 : MARGIN;
	const totalH = compact ? numRows * cellH : cellH + gap + cellH;

	// Make cells square: viewW derived from n * cellH + margins
	const labelW = compact ? 30 : 40;
	const viewW = 2 * margin + n * cellH;
	const fullCellW = cellH;

	// In non-compact mode, crop viewBox to center 19 cells
	const visibleCellCount = compact ? n : 19;
	const cellStart = compact ? 0 : Math.floor((n - visibleCellCount) / 2);
	const viewX = (compact ? 0 : margin + cellStart * fullCellW - MARGIN) - labelW;
	const viewBoxW = (compact ? viewW : visibleCellCount * fullCellW + 2 * MARGIN) + labelW;
	const highlightSet = new Set(highlightInputs ?? []);
	const slideDownSet = new Set(slideDown ?? []);
	const revealedSet = new Set(revealedCells);
	const resultSet = new Set(highlightResult ?? []);

	function cellX(i: number): number {
		const cellArea = viewW - 2 * margin;
		return margin + (i * cellArea) / n;
	}

	function cellCenterX(i: number): number {
		return cellX(i) + fullCellW / 2;
	}

	const cw = fullCellW;
	const row0Y = 0;
	const row1Y = cellH + gap;

	function renderRow(
		states: string[],
		y: number,
		visible: boolean,
		opts: {
			highlight?: Set<number>;
			slideDown?: Set<number>;
			revealed?: Set<number>;
			revealRest?: boolean;
			result?: Set<number>;
			revealCenter?: number;
		},
	) {
		return states.map((s, i) => {
			const isHighlighted = opts.highlight?.has(i) ?? false;
			const isSlidDown = opts.slideDown?.has(i) ?? false;
			const hasReveal = opts.revealed !== undefined;
			const isRevealed = !hasReveal || opts.revealed!.has(i) || opts.revealRest;
			const isResult = opts.result?.has(i) ?? false;

			let ty = 0;
			let opacity = 1;
			if (hasReveal && !isRevealed) {
				ty = cellH;
				opacity = 0;
			} else if (isSlidDown) {
				ty = cellH * 0.45;
			}

			if (!visible) {
				opacity = 0;
			}

			const delay = 0;

			const normalFill = isHighlighted ? "#fde8e8" : isResult ? "#d4edda" : "#f5f5f5";
			const normalStroke = isHighlighted ? "#e74c3c" : isResult ? "#28a745" : "#bbb";
			const isPlain = !isHighlighted && !isResult;
			const colorFill = colorMode && isPlain && s === "1"
				? "#000"
				: normalFill;
			const colorStroke = colorMode && isPlain
				? "#bbb"
				: normalStroke;
			const cx = cellX(i);

			return (
				<g
					key={i}
					style={{
						transform: `translate(0, ${ty}px)`,
						opacity,
						transition: `transform 0.4s ease ${delay}s, opacity 0.4s ease ${delay}s`,
					}}
				>
					<rect
						x={cx}
						y={y}
						width={cw}
						height={cellH}
						fill={colorFill}
						stroke={colorStroke}
						strokeWidth={1}
						style={{ transition: "fill 0.5s ease, stroke 0.3s ease" }}
					/>
					<text
						x={cx + cw / 2}
						y={y + cellH / 2}
						textAnchor="middle"
						dominantBaseline="central"
						fontSize={FONT_SIZE}
						fill={colorMode && isPlain && s === "1" ? "#fff" : "#000"}
						fontWeight={isResult ? "bold" : "normal"}
						style={{ opacity: (colorMode && isPlain) ? 0 : 1, transition: "opacity 0.5s ease" }}
					>
						{s}
					</text>
				</g>
			);
		});
	}

	function renderConnectors() {
		const visible = revealRest
			? Array.from({ length: n }, (_, i) => i)
			: revealedCells;

		let lineIdx = 0;
		return visible.flatMap((i) =>
			[i - 1, i, i + 1]
				.filter((src) => src >= 0 && src < n)
				.map((src, idx) => {
					const delay = lineIdx * 0.05;
					lineIdx++;
					const isResult = resultSet.has(i);
					const color = isResult ? "#000" : "#888";
					const markerId = `arrow-${i}-${idx}`;

					const x1 = cellCenterX(src);
					const y1 = row0Y + cellH / 2;
					const x2 = cellCenterX(i);
					const y2 = row1Y + cellH / 2;

					// Clip line end to top edge of target cell
					const t = (row1Y - y1) / (y2 - y1);
					const xEnd = x1 + t * (x2 - x1);

					return (
						<g key={`${i}-${idx}`}>
							<defs>
								<marker
									id={markerId}
									markerWidth="6"
									markerHeight="4"
									refX="6"
									refY="2"
									orient="auto"
								>
									<path d="M0,0 L6,2 L0,4" fill={color} fillOpacity={0.5} />
								</marker>
							</defs>
							<line
								x1={x1}
								y1={y1}
								x2={xEnd}
								y2={row1Y}
								stroke={color}
								strokeWidth={isResult ? 1.5 : 1}
								markerEnd={`url(#${markerId})`}
								style={{
									strokeOpacity: 0.5,
									transition: `stroke-opacity 0.3s ease ${delay}s`,
								}}
							/>
						</g>
					);
				}),
		);
	}

	function renderLabel(t: number, y: number, visible: boolean) {
		const firstCellX = cellX(compact ? 0 : cellStart);
		const labelX = firstCellX - 6;
		return (
			<text
				x={labelX}
				y={y + cellH / 2}
				textAnchor="end"
				dominantBaseline="central"
				fontSize={compact ? FONT_SIZE * 0.6 : FONT_SIZE * 0.8}
				fill="#999"
				fontStyle="italic"
				style={{ opacity: visible ? 1 : 0, transition: "opacity 0.3s" }}
			>
				t={t}
			</text>
		);
	}

	function renderDelta() {
		if (deltaTarget === undefined) return null;
		const leftX = cellX(deltaTarget - 1);
		const rightX = cellX(deltaTarget + 2);
		const midY = row0Y + cellH + gap / 2;

		return (
			<g style={{ opacity: showDelta ? 1 : 0, transition: "opacity 0.3s ease" }}>
				<defs>
					<radialGradient id="delta-bg">
						<stop offset="0%" stopColor="#f0f0f0" stopOpacity={1} />
						<stop offset="100%" stopColor="#f0f0f0" stopOpacity={0} />
					</radialGradient>
				</defs>
				<ellipse cx={leftX - 20} cy={midY} rx={30} ry={18} fill="url(#delta-bg)" />
				<ellipse cx={rightX + 20} cy={midY} rx={30} ry={18} fill="url(#delta-bg)" />
				<text
					x={leftX - 6}
					y={midY}
					textAnchor="end"
					dominantBaseline="central"
					fontSize={FONT_SIZE}
					fill="#000"
				>
					<tspan fontStyle="italic">δ</tspan> (
				</text>
				<text
					x={rightX + 6}
					y={midY}
					textAnchor="start"
					dominantBaseline="central"
					fontSize={FONT_SIZE}
					fill="#000"
				>
					) =
				</text>
			</g>
		);
	}

	return (
		<svg
			viewBox={`${viewX} 0 ${viewBoxW} ${totalH}`}
			preserveAspectRatio="xMidYMid meet"
			style={{ width: "100%", display: "block" }}
		>
			{showRow1 && !compact && renderConnectors()}
			{renderRow(states0, row0Y, showRow0, {
				highlight: highlightSet,
				slideDown: slideDownSet,
			})}
			{renderRow(states1, row1Y, showRow1, {
				revealed: revealedSet,
				revealRest,
				result: resultSet,
				revealCenter: revealedCells[0] ?? 0,
			})}
			{!compact && renderDelta()}
			{compact && renderLabel(0, row0Y, true)}
			{compact && renderLabel(1, row1Y, true)}
			{visibleExtraRows.map((row, rowIdx) => {
				const ey = (2 + rowIdx) * cellH;
				const delay = rowIdx * 0.05;
				return (
					<g
						key={`extra-${rowIdx}`}
						style={{
							opacity: showExtraRows ? 1 : 0,
							transition: `opacity 0.4s ease ${delay}s`,
						}}
					>
						{renderLabel(2 + rowIdx, ey, showExtraRows)}
						{row.map((s, i) => {
							const cx = cellX(i);
							const fill = s === "1" ? "#000" : "#f5f5f5";
							return (
								<rect
									key={i}
									x={cx}
									y={ey}
									width={cw}
									height={cellH}
									fill={fill}
									stroke="#bbb"
									strokeWidth={1}
								/>
							);
						})}
					</g>
				);
			})}
			{markedCell !== undefined && (() => {
				const mx = cellX(markedCell) + cw / 2;
				const allRows = [row0Y, row1Y, ...visibleExtraRows.map((_, idx) => (2 + idx) * cellH)];
				return allRows.map((ry, idx) => (
					<circle
						key={`mark-${idx}`}
						cx={mx}
						cy={ry + cellH / 2}
						r={cellH * 0.3}
						fill="none"
						stroke="#e74c3c"
						strokeWidth={2}
					/>
				));
			})()}
		</svg>
	);
}
