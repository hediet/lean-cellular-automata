import { useRef, useLayoutEffect, useState, type ReactNode } from "react";

export function AutoScale({
	children,
	zoomRange = { min: 0.1, max: 1 },
}: {
	children: ReactNode;
	zoomRange?: { min: number; max: number };
}) {
	const outerRef = useRef<HTMLDivElement>(null);
	const innerRef = useRef<HTMLDivElement>(null);
	const [scale, setScale] = useState(1);

	useLayoutEffect(() => {
		const outer = outerRef.current;
		const inner = innerRef.current;
		if (!outer || !inner) return;

		const observer = new ResizeObserver(() => {
			const outerW = outer.clientWidth;
			const outerH = outer.clientHeight;
			if (outerW === 0 || outerH === 0) return;

			// Reset to natural size to measure correctly
			inner.style.transform = "none";
			inner.style.width = "100%";
			const naturalW = inner.scrollWidth;
			const naturalH = inner.scrollHeight;

			if (naturalW === 0 || naturalH === 0) return;

			const s = Math.min(outerW / naturalW, outerH / naturalH);
			const clamped = Math.max(zoomRange.min, Math.min(zoomRange.max, s));
			setScale(clamped);

			// Re-apply transform immediately to avoid flicker
			inner.style.transform = `scale(${clamped})`;
			inner.style.width = `${100 / clamped}%`;
		});

		observer.observe(outer);
		observer.observe(inner);
		return () => observer.disconnect();
	}, [zoomRange.min, zoomRange.max]);

	return (
		<div ref={outerRef} style={{ width: "100%", height: "100%", overflow: "hidden" }}>
			<div
				ref={innerRef}
				style={{
					transformOrigin: "top left",
					transform: `scale(${scale})`,
					width: `${100 / scale}%`,
				}}
			>
				{children}
			</div>
		</div>
	);
}
