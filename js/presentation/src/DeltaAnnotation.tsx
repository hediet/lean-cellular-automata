import { Latex } from "./Latex";

const ELLIPSIS_WIDTH = 40;

export function DeltaAnnotation({
	cellCount,
	targetCell,
	visible,
}: {
	cellCount: number;
	targetCell: number;
	visible: boolean;
}) {
	// Position the δ( and ) = labels aligned with the cells.
	// The cells occupy the space between two ellipsis regions, each ELLIPSIS_WIDTH wide.
	// Each cell has equal flex width: cellWidth = (100% - 2*ELLIPSIS_WIDTH) / cellCount
	// We use percentage-based positioning.
	const cellWidthPct = (100 - (2 * ELLIPSIS_WIDTH * 100) / 1366) / cellCount;
	const ellipsisPct = (ELLIPSIS_WIDTH * 100) / 1366;

	// Left edge of the leftmost highlighted cell (targetCell - 1)
	const leftCellLeft = ellipsisPct + (targetCell - 1) * cellWidthPct;
	// Right edge of the rightmost highlighted cell (targetCell + 1)
	const rightCellRight = ellipsisPct + (targetCell + 2) * cellWidthPct;

	return (
		<div style={{
			position: "relative",
			height: 48,
			opacity: visible ? 1 : 0,
			transition: "opacity 0.3s ease",
			zIndex: 1,
		}}>
			<span style={{
				position: "absolute",
				right: `${100 - leftCellLeft}%`,
				top: "50%",
				transform: "translateY(-50%)",
				fontSize: 22,
				whiteSpace: "nowrap",
			}}>
				<Latex>{"\\delta\\;(\\;"}</Latex>
			</span>
			<span style={{
				position: "absolute",
				left: `${rightCellRight}%`,
				top: "50%",
				transform: "translateY(-50%)",
				fontSize: 22,
				whiteSpace: "nowrap",
			}}>
				<Latex>{"\\;)\\; ="}</Latex>
			</span>
		</div>
	);
}
