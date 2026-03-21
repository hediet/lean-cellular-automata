import katex from "katex";
import "katex/dist/katex.min.css";

export function Latex({ children, display }: { children: string; display?: boolean }) {
	const html = katex.renderToString(children, {
		displayMode: display ?? false,
		throwOnError: false,
	});
	return <span dangerouslySetInnerHTML={{ __html: html }} />;
}
