const CELL_SIZE = 24;
const FONT_SIZE = 11;

interface EmbeddingVizProps {
	word: string[];
	borderCount?: number;
	showWord: boolean;
	showConfig: boolean;
	showIndices: boolean;
}

export function EmbeddingViz({
	word,
	borderCount = 4,
	showWord,
	showConfig,
	showIndices,
}: EmbeddingVizProps) {
	const n = word.length;
	const totalCells = n + 2 * borderCount;
	const cs = CELL_SIZE;
	const margin = 20;
	const labelW = 50;

	const configX = margin;
	const wordX = configX + borderCount * cs;
	const gridW = totalCells * cs;

	const wordY = 0;
	const arrowGap = 26;
	const configY = cs + arrowGap;
	const indexH = 18;
	const viewW = 2 * margin + gridW;
	const viewH = configY + cs + indexH + 5;

	const midX = wordX + (n * cs) / 2;

	return (
		<svg
			viewBox={`${-labelW} -5 ${viewW + labelW + 20} ${viewH + 5}`}
			preserveAspectRatio="xMidYMid meet"
			style={{ width: "100%", display: "block" }}
		>
			{/* Word row */}
			<g style={{ opacity: showWord ? 1 : 0, transition: "opacity 0.5s" }}>
				<text
					x={wordX - 10}
					y={wordY + cs / 2}
					textAnchor="end"
					dominantBaseline="central"
					fontSize={FONT_SIZE}
					fill="#555"
					fontStyle="italic"
				>
					w =
				</text>
				{word.map((s, i) => (
					<g key={i}>
						<rect
							x={wordX + i * cs}
							y={wordY}
							width={cs}
							height={cs}
							fill="#e3f2fd"
							stroke="#1976d2"
							strokeWidth={1.5}
							rx={2}
						/>
						<text
							x={wordX + i * cs + cs / 2}
							y={wordY + cs / 2}
							textAnchor="middle"
							dominantBaseline="central"
							fontSize={FONT_SIZE * 1.1}
							fill="#1565c0"
							fontWeight="bold"
						>
							{s}
						</text>
					</g>
				))}
			</g>

			{/* Arrow */}
			<g style={{ opacity: showConfig ? 1 : 0, transition: "opacity 0.5s" }}>
				<defs>
					<marker id="emb-arr" markerWidth="8" markerHeight="6" refX="8" refY="3" orient="auto">
						<path d="M0,0 L8,3 L0,6" fill="#888" />
					</marker>
				</defs>
				<line
					x1={midX}
					y1={cs + 5}
					x2={midX}
					y2={configY - 4}
					stroke="#888"
					strokeWidth={1.5}
					markerEnd="url(#emb-arr)"
				/>
				<text
					x={midX - 12}
					y={cs + arrowGap / 2 + 2}
					textAnchor="end"
					dominantBaseline="central"
					fontSize={FONT_SIZE * 0.85}
					fill="#888"
					fontStyle="italic"
				>
					embed
				</text>
			</g>

			{/* Config row */}
			<g style={{ opacity: showConfig ? 1 : 0, transition: "opacity 0.5s" }}>
				<text
					x={configX - 8}
					y={configY + cs / 2}
					textAnchor="end"
					dominantBaseline="central"
					fontSize={FONT_SIZE * 1.3}
					fill="#bbb"
				>
					…
				</text>
				<text
					x={configX + gridW + 8}
					y={configY + cs / 2}
					textAnchor="start"
					dominantBaseline="central"
					fontSize={FONT_SIZE * 1.3}
					fill="#bbb"
				>
					…
				</text>

				{Array.from({ length: totalCells }, (_, idx) => {
					const ci = idx - borderCount;
					const isWord = ci >= 0 && ci < n;
					const x = configX + idx * cs;
					return (
						<g key={idx}>
							<rect
								x={x}
								y={configY}
								width={cs}
								height={cs}
								fill={isWord ? "#e3f2fd" : "#f5f5f5"}
								stroke={isWord ? "#1976d2" : "#ccc"}
								strokeWidth={isWord ? 1.5 : 1}
							/>
							<text
								x={x + cs / 2}
								y={configY + cs / 2}
								textAnchor="middle"
								dominantBaseline="central"
								fontSize={FONT_SIZE}
								fill={isWord ? "#1565c0" : "#aaa"}
								fontWeight={isWord ? "bold" : "normal"}
							>
								{isWord ? word[ci] : "#"}
							</text>
						</g>
					);
				})}
			</g>

			{/* Indices */}
			<g style={{ opacity: showIndices ? 1 : 0, transition: "opacity 0.5s" }}>
				{Array.from({ length: totalCells }, (_, idx) => {
					const ci = idx - borderCount;
					const x = configX + idx * cs;
					return (
						<text
							key={idx}
							x={x + cs / 2}
							y={configY + cs + 16}
							textAnchor="middle"
							fontSize={FONT_SIZE * 0.7}
							fill="#999"
						>
							{ci}
						</text>
					);
				})}
			</g>
		</svg>
	);
}
