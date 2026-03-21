const ELLIPSIS_WIDTH = 40;

export function TransitionConnectors({
	cellCount,
	visibleCells,
	height = 40,
}: {
	cellCount: number;
	visibleCells: number[];
	height?: number;
}) {
	const visibleSet = new Set(visibleCells);

	function cellCenterX(i: number): string {
		const viewWidth = 1000;
		const cellArea = viewWidth - 2 * ELLIPSIS_WIDTH;
		return String(ELLIPSIS_WIDTH + (i + 0.5) / cellCount * cellArea);
	}

	const lines: { x1: string; x2: string }[] = [];
	for (const i of visibleSet) {
		for (const src of [i - 1, i, i + 1]) {
			if (src >= 0 && src < cellCount) {
				lines.push({
					x1: cellCenterX(src),
					x2: cellCenterX(i),
				});
			}
		}
	}

	return (
		<svg
			viewBox={`0 0 1000 ${height}`}
			preserveAspectRatio="none"
			style={{
				width: "100%",
				height,
				display: "block",
				transition: "opacity 0.3s ease",
			}}
		>
			{lines.map((l, idx) => (
				<line
					key={idx}
					x1={l.x1}
					y1={0}
					x2={l.x2}
					y2={height}
					stroke="#888"
					strokeWidth={1}
					strokeOpacity={0.5}
				/>
			))}
		</svg>
	);
}
