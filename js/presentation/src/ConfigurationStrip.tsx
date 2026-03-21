import { Latex } from "./Latex";

const cellStyle: React.CSSProperties = {
	display: "flex",
	alignItems: "center",
	justifyContent: "center",
	height: 56,
	minWidth: 56,
	flex: "1 1 0",
	borderLeft: "1px solid #bbb",
	borderTop: "1px solid #bbb",
	borderBottom: "1px solid #bbb",
	background: "#f5f5f5",
	fontSize: 22,
};

const ellipsisStyle: React.CSSProperties = {
	display: "flex",
	alignItems: "center",
	justifyContent: "center",
	height: 56,
	minWidth: 40,
	flex: "0 0 auto",
	fontSize: 28,
	letterSpacing: 2,
};

export function ConfigurationStrip({
	states,
	revealedCell,
	revealedCells,
	revealRest,
	highlightCells,
	slideDown,
	highlightResult,
}: {
	states: string[];
	revealedCell?: number;
	revealedCells?: number[];
	revealRest?: boolean;
	highlightCells?: number[];
	slideDown?: number[];
	highlightResult?: number[];
}) {
	const revealedSet = new Set(revealedCells ?? (revealedCell !== undefined ? [revealedCell] : []));
	const hasRevealLogic = revealedCells !== undefined || revealedCell !== undefined;
	const revealCenter = revealedCells?.[0] ?? revealedCell ?? 0;
	const highlightSet = new Set(highlightCells ?? []);
	const slideDownSet = new Set(slideDown ?? []);
	const resultSet = new Set(highlightResult ?? []);

	const hasSlideDown = slideDown && slideDown.length > 0;

	return (
		<div style={{ display: "flex", width: "100%", alignItems: "center", overflow: hasSlideDown ? "visible" : "hidden" }}>
			<div style={ellipsisStyle}>⋯</div>
			{states.map((s, i) => {
				const isRevealed = !hasRevealLogic || revealedSet.has(i) || revealRest;
				const isHighlighted = highlightSet.has(i);
				const isSlidDown = slideDownSet.has(i);
				const isResult = resultSet.has(i);
				const delay = hasRevealLogic
					? Math.abs(i - revealCenter) * 0.03
					: 0;

				let transform = "translateY(0)";
				let opacity = 1;
				if (hasRevealLogic && !isRevealed) {
					transform = "translateY(100%)";
					opacity = 0;
				} else if (isSlidDown) {
					transform = "translateY(50%)";
				}

				const borderColor = isHighlighted ? "#e74c3c" : isResult ? "#28a745" : "#bbb";

				return (
					<div
						key={i}
						style={{
							...cellStyle,
							borderColor,
							borderRight: i === states.length - 1 ? `1px solid ${borderColor}` : undefined,
							transform,
							opacity,
							transition: `transform 0.4s ease ${delay}s, opacity 0.4s ease ${delay}s, background 0.3s ease, border-color 0.3s ease`,
							...(isHighlighted ? { background: "#fde8e8" } : {}),
							...(isResult ? { background: "#d4edda", fontWeight: "bold" } : {}),
						}}
					>
						<Latex>{s}</Latex>
					</div>
				);
			})}
			<div style={ellipsisStyle}>⋯</div>
		</div>
	);
}
