const CELL_SIZE = 32;
const FONT_SIZE = 11;
const MARGIN = 10;
const LABEL_W = 35;

interface AcceptanceGridProps {
	grid: string[][];
	wordStart: number;
	wordLen: number;
	acceptCol: number;
	acceptRow: number;
	showGrid: boolean;
	showAccept: boolean;
}

export function AcceptanceGrid({
	grid,
	wordStart,
	wordLen,
	acceptCol,
	acceptRow,
	showGrid,
	showAccept,
}: AcceptanceGridProps) {
	const rows = grid.length;
	const cols = grid[0].length;
	const cs = CELL_SIZE;

	const gridW = cols * cs + 2 * MARGIN;
	const gridH = rows * cs;
	const acceptLabelW = 80;

	return (
		<svg
			viewBox={`${-LABEL_W} 0 ${gridW + LABEL_W + acceptLabelW} ${gridH}`}
			preserveAspectRatio="xMidYMid meet"
			style={{ width: "100%", display: "block" }}
		>
			<g style={{ opacity: showGrid ? 1 : 0, transition: "opacity 0.5s" }}>
				{grid.map((row, t) => {
					const y = t * cs;
					return (
						<g key={t}>
							<text
								x={MARGIN - 6}
								y={y + cs / 2}
								textAnchor="end"
								dominantBaseline="central"
								fontSize={FONT_SIZE}
								fill="#999"
								fontStyle="italic"
							>
								t={t}
							</text>
							{row.map((s, i) => {
								const x = MARGIN + i * cs;
								const isWordInit = t === 0 && i >= wordStart && i < wordStart + wordLen;
								const fill = s === "1" ? "#222" : "#f5f5f5";
								const stroke = isWordInit ? "#1976d2" : "#ddd";
								return (
									<rect
										key={i}
										x={x} y={y}
										width={cs} height={cs}
										fill={fill}
										stroke={stroke}
										strokeWidth={isWordInit ? 1.5 : 0.5}
									/>
								);
							})}
						</g>
					);
				})}

				{/* Word bracket at t=0 */}
				{(() => {
					const bx1 = MARGIN + wordStart * cs;
					const bx2 = MARGIN + (wordStart + wordLen) * cs;
					const by = -8;
					return (
						<g>
							<line x1={bx1} y1={by} x2={bx2} y2={by} stroke="#1976d2" strokeWidth={1.5} />
							<line x1={bx1} y1={by} x2={bx1} y2={by + 5} stroke="#1976d2" strokeWidth={1.5} />
							<line x1={bx2} y1={by} x2={bx2} y2={by + 5} stroke="#1976d2" strokeWidth={1.5} />
							<text
								x={(bx1 + bx2) / 2}
								y={by - 5}
								textAnchor="middle"
								fontSize={FONT_SIZE}
								fill="#1976d2"
								fontStyle="italic"
							>
								w
							</text>
						</g>
					);
				})()}

				{/* Acceptance cell highlight */}
				<g style={{ opacity: showAccept ? 1 : 0, transition: "opacity 0.5s" }}>
					{(() => {
						const ax = MARGIN + acceptCol * cs;
						const ay = acceptRow * cs;
						const accepted = grid[acceptRow][acceptCol] === "1";
						const color = accepted ? "#28a745" : "#dc3545";
						return (
							<>
								<rect
									x={ax + 1.5} y={ay + 1.5}
									width={cs - 3} height={cs - 3}
									fill="none"
									stroke={color}
									strokeWidth={3}
									rx={3}
								/>
								<text
									x={MARGIN + cols * cs + 8}
									y={ay + cs / 2}
									textAnchor="start"
									dominantBaseline="central"
									fontSize={FONT_SIZE * 1.3}
									fill={color}
									fontWeight="bold"
								>
									← {accepted ? "accept" : "reject"}
								</text>
							</>
						);
					})()}
				</g>
			</g>
		</svg>
	);
}
