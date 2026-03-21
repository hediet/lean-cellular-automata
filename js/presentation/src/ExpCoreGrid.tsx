type SigState = "SR" | "SL" | "None";
type MirrorState = "M1" | "M2" | "M3" | "None";
type ExpQ = [SigState, MirrorState, boolean];

const CELL_SIZE = 24;
const GRID_MARGIN = 10;
const LABEL_W = 30;

const SIGNAL_COLOR = "#2563eb";
const MIRROR_COLOR = "#dc2626";

export function ExpCoreGrid({ grid }: { grid: ExpQ[][] }) {
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
							const [sig, mirror, isUnit] = q;
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
									{isUnit && (
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
		</svg>
	);
}
