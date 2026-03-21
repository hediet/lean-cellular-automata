import {
    Deck,
    Slide,
    Heading,
    Text,
    FlexBox,
    UnorderedList,
    ListItem,
    useSteps,
} from "spectacle";
import { Latex } from "./Latex";
import { AutoScale } from "./AutoScale";
import { ConfigPreview } from "./ConfigPreview";
import { ExpCoreGrid } from "./ExpCoreGrid";
import { ExpWordGrid, buildExpWordGrid, buildTrivialWordGrid } from "./ExpWordGrid";

export const theme = {
	colors: {
		primary: "#000",
		secondary: "#333",
		tertiary: "#fff",
	},
	fonts: {
		header: '"Helvetica Neue", Helvetica, Arial, sans-serif',
		text: '"Helvetica Neue", Helvetica, Arial, sans-serif',
	},
};

const COMPACT_EXTRA = 8;
const TOTAL_CELLS = 19 + 2 * COMPACT_EXTRA;
const CENTER = 9 + COMPACT_EXTRA;

const configStates = Array.from({ length: TOTAL_CELLS }, (_, i) => i === CENTER ? "1" : "0");

function rule30(p: number, q: number, r: number): number {
	return p ^ (q | r);
}

const configStates2 = configStates.map((_, i) => {
	const p = i > 0 ? Number(configStates[i - 1]) : 0;
	const q = Number(configStates[i]);
	const r = i < configStates.length - 1 ? Number(configStates[i + 1]) : 0;
	return String(rule30(p, q, r));
});

function applyRule30(row: string[]): string[] {
	return row.map((_, i) => {
		const p = i > 0 ? Number(row[i - 1]) : 0;
		const q = Number(row[i]);
		const r = i < row.length - 1 ? Number(row[i + 1]) : 0;
		return String(rule30(p, q, r));
	});
}

const extraRows: string[][] = [];
{
	let prev = configStates2;
	for (let t = 0; t < 25; t++) {
		prev = applyRule30(prev);
		extraRows.push(prev);
	}
}

// Demo data for embedding/acceptance slides
const DEMO_WORD = ["1", "0", "1", "1", "0"];
const DEMO_N = DEMO_WORD.length;
const DEMO_BORDER = 4;
const DEMO_CELL_COUNT = DEMO_N + 2 * DEMO_BORDER;
const DEMO_WORD_START = DEMO_BORDER;

const demoEmbedded = Array.from({ length: DEMO_CELL_COUNT }, (_, i) => {
	const wi = i - DEMO_WORD_START;
	return (wi >= 0 && wi < DEMO_N) ? DEMO_WORD[wi] : "0";
});

const demoSteps: string[][] = [demoEmbedded];
{
	let prev = demoEmbedded;
	for (let t = 0; t < DEMO_N - 1; t++) {
		prev = applyRule30(prev);
		demoSteps.push(prev);
	}
}

export function DefinitionSlideContent({ step }: { step: number }) {
	const demoCell =
		step === 1 ? CENTER :
		step === 2 ? CENTER + 1 :
		step === 3 ? CENTER + 2 :
		step === 4 ? CENTER + 3 :
		undefined;
	const showDemo = demoCell !== undefined;

	const highlightCells = demoCell !== undefined ? [demoCell - 1, demoCell, demoCell + 1] : undefined;
	const slideDown = highlightCells;
	const highlightResult = demoCell !== undefined ? [demoCell] : undefined;
	const deltaTarget = demoCell ?? CENTER;
	const revealedCells =
		step === 1 ? [CENTER] :
		step === 2 ? [CENTER, CENTER + 1] :
		step === 3 ? [CENTER, CENTER + 1, CENTER + 2] :
		step >= 4 ? [CENTER, CENTER + 1, CENTER + 2, CENTER + 3] :
		[];

	const compact = step >= 7;

	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%" }}>
			<div style={{
				opacity: compact ? 0 : 1,
				maxHeight: compact ? 0 : "100%",
				overflow: "hidden",
				transition: "opacity 0.5s ease, max-height 0.5s ease",
				flex: compact ? "0 0 0" : "1 1 auto",
			}}>
				<AutoScale zoomRange={{ min: 0.1, max: 1 }}>
					<Heading fontSize="h3">Definition: Cellular Automaton</Heading>
					<Text>
						A one-dimensional cellular automaton is a tuple{" "}
						<Latex>{"C = (Q, \\delta)"}</Latex> where
					</Text>
					<UnorderedList>
						<ListItem>
							<div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline" }}>
								<span><Latex>{"Q"}</Latex> is a finite, non-empty set of <em>states</em></span>
								<span style={{ color: "#999" }}>
									e.g. <Latex>{"Q = \\{0, 1\\}"}</Latex>
								</span>
							</div>
						</ListItem>
						<ListItem>
							<div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline" }}>
								<span><Latex>{"\\delta: Q^3 \\to Q"}</Latex> is the <em>local transition function</em></span>
								<span style={{ color: "#999" }}>
									e.g. <Latex>{"\\delta(p, q, r) = p \\oplus (q \\lor r)"}</Latex>
								</span>
							</div>
						</ListItem>
					</UnorderedList>

					<div style={{ visibility: step >= 0 ? "visible" : "hidden" }}>
						<Text>
							A <em>configuration</em> <Latex>{"c \\in Q^{\\mathbb{Z}}"}</Latex> assigns a state to every cell.
						</Text>
					</div>

					<div style={{ visibility: step >= 1 ? "visible" : "hidden" }}>
						<Text>
							The <em>global transition</em> is:{" "}
							<Latex>{"\\Delta_C(c)(i) \\;=\\; \\delta\\bigl(c_{i-1},\\; c_i,\\; c_{i+1}\\bigr)"}</Latex>
						</Text>
					</div>
				</AutoScale>
			</div>

			<div style={{
				marginLeft: 0,
				marginRight: 0,
				padding: compact ? 0 : "16px 0",
				background: "#f0f0f0",
				flex: compact ? "1 1 auto" : "0 0 auto",
				transition: "padding 0.5s ease",
			}}>
				<ConfigPreview
					states0={configStates}
					states1={configStates2}
					showRow0={step >= 0}
					showRow1={step >= 1}
					highlightInputs={highlightCells}
					slideDown={slideDown}
					revealedCells={revealedCells}
					revealRest={step >= 5}
					highlightResult={highlightResult}
					deltaTarget={deltaTarget}
					showDelta={showDemo}
					colorMode={step >= 6}
					compact={compact}
					extraRows={extraRows}
					showExtraRows={step >= 8}
				/>
			</div>
		</div>
	);
}





// exp_core CA simulation (signal-bouncing CA that marks powers of 2)
type SigState = "SR" | "SL" | "None";
type MirrorState = "M1" | "M2" | "M3" | "None";
type ExpQ = [SigState, MirrorState, boolean];

function expDelta(left: ExpQ, center: ExpQ, right: ExpQ): ExpQ {
	const mCenter = center[1];
	let m2: MirrorState;
	if (mCenter === "M1") m2 = "None";
	else if (mCenter === "M2") m2 = "M3";
	else if (mCenter === "M3") m2 = "M1";
	else m2 = left[1] === "M1" ? "M2" : "None";

	const u = center[2];

	const incoming: SigState =
		left[0] === "SR" ? "SR" :
		right[0] === "SL" ? "SL" : "None";

	let s2: SigState;
	if (incoming === "SR") s2 = m2 === "M2" ? "SL" : "SR";
	else if (incoming === "SL") s2 = u ? "SR" : "SL";
	else s2 = "None";

	return [s2, m2, u];
}

const borderState: ExpQ = ["None", "None", false];
const centerState: ExpQ = ["SR", "M1", true];

const EXP_CELLS = TOTAL_CELLS;
const EXP_CENTER = CENTER;
const EXP_ROWS = 21;

function buildExpGrid(): ExpQ[][] {
	const grid: ExpQ[][] = [];
	const row0: ExpQ[] = Array.from({ length: EXP_CELLS }, (_, i) =>
		i === EXP_CENTER ? centerState : borderState
	);
	grid.push(row0);

	for (let t = 1; t < EXP_ROWS; t++) {
		const prev = grid[t - 1];
		const next: ExpQ[] = prev.map((_, i) => {
			const l = i > 0 ? prev[i - 1] : borderState;
			const c = prev[i];
			const r = i < prev.length - 1 ? prev[i + 1] : borderState;
			return expDelta(l, c, r);
		});
		grid.push(next);
	}

	return grid;
}

class Lazy<T> {
	private _value: T | undefined = undefined;
	constructor(private readonly _compute: () => T) {}
	get(): T {
		if (this._value === undefined) this._value = this._compute();
		return this._value;
	}
}

const expGrid = new Lazy(() => buildExpGrid());

const EXP_WORD: ("circle" | "star")[] = ["circle", "circle", "star", "star", "circle", "star", "circle", "star", "star"];
const EXP_WORD_START = CENTER;
const EXP_WORD_ROWS = 21;
const expWordGrid9 = new Lazy(() => buildExpWordGrid(EXP_WORD, TOTAL_CELLS, EXP_WORD_START, EXP_WORD_ROWS));
const expWordGrid8 = new Lazy(() => buildExpWordGrid(EXP_WORD.slice(0, 8), TOTAL_CELLS, EXP_WORD_START, EXP_WORD_ROWS));
const expWordGrid7 = new Lazy(() => buildExpWordGrid(EXP_WORD.slice(0, 7), TOTAL_CELLS, EXP_WORD_START, EXP_WORD_ROWS));
const trivialGrid9 = new Lazy(() => buildTrivialWordGrid(EXP_WORD, TOTAL_CELLS, EXP_WORD_START, EXP_WORD_ROWS));
const trivialGrid8 = new Lazy(() => buildTrivialWordGrid(EXP_WORD.slice(0, 8), TOTAL_CELLS, EXP_WORD_START, EXP_WORD_ROWS));
const trivialGrid7 = new Lazy(() => buildTrivialWordGrid(EXP_WORD.slice(0, 7), TOTAL_CELLS, EXP_WORD_START, EXP_WORD_ROWS));

export function ExpMiddleSlideContent() {
	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%", background: "#f0f0f0" }}>
			<ExpCoreGrid grid={expGrid.get()} />
		</div>
	);
}

export function ExpWordSlideContent({ step }: { step: number }) {
	// step=-1 (stepIndex 0): plain grid only
	// step=0  (stepIndex 1): RT with exp grid, |w|=9
	// step=1  (stepIndex 2): RT with exp grid, |w|=8
	// step=2  (stepIndex 3): RT with exp grid, |w|=7
	// step=3  (stepIndex 4): RT with exp grid, |w|=9 (back to full word)
	// step=4  (stepIndex 5): RT with trivial grid, |w|=7
	// step=5  (stepIndex 6): RT with trivial grid + influence, |w|=7
	// step=6  (stepIndex 7): RT with trivial grid + influence, |w|=7
	// step=7  (stepIndex 8): LT with trivial grid, |w|=7 + dead border hint
	const showDeadBorderOverlay = step === 7;
	const s = step <= 0 ? 0 : step;

	const isLT = s >= 6;
	const useTrivial = s >= 4;
	const restricted = s >= 7;

	const wordLens: Record<number, number> = {
		0: 9, 1: 8, 2: 7, 3: 9, 4: 7, 5: 7, 6: 7, 7: 7,
	};
	const wLen = wordLens[s] ?? 9;

	const coneLens: Record<number, number> = {
		0: 9, 1: 8, 2: 7, 3: 7, 4: 7, 5: 7, 6: 7, 7: 7,
	};
	const cLen = coneLens[s] ?? 9;

	const expGrids: Record<number, ReturnType<typeof expWordGrid9.get>> = { 7: expWordGrid7.get(), 8: expWordGrid8.get(), 9: expWordGrid9.get() };
	const trivGrids: Record<number, ReturnType<typeof trivialGrid9.get>> = { 7: trivialGrid7.get(), 8: trivialGrid8.get(), 9: trivialGrid9.get() };
	const grid = useTrivial ? trivGrids[wLen] : expGrids[wLen];

	const coneHeight = isLT ? 2 * (cLen - 1) : cLen - 1;
	const coneRightCells = isLT ? coneHeight + 1 : cLen;

	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%", background: "#f0f0f0", position: "relative" }}>
			<ExpWordGrid
				grid={grid}
				wordStart={EXP_WORD_START}
				wordLen={step >= 0 ? cLen : undefined}
				coneHeight={step >= 0 ? coneHeight : undefined}
				coneRightCells={step >= 0 ? coneRightCells : undefined}
				showCone={step >= 0}
				showInfluenceCone={s >= 5}
				restrictToWord={restricted}
				highlightCell={step >= 0 ? { col: EXP_WORD_START, row: coneHeight } : undefined}
				highlightLabel={step >= 0
					? isLT
						? <span>Linear Time (LT): Check cell 0 at <Latex>{`t = 2|w|,\\; |w| = ${cLen}`}</Latex></span>
						: <span>Real Time (RT): Check cell 0 at <Latex>{`t = |w| - 1,\\; |w| = ${cLen}`}</Latex></span>
					: undefined}
			/>
			{showDeadBorderOverlay && (
				<div style={{
					position: "absolute",
					bottom: 0,
					left: 0,
					right: 0,
					background: "#fff",
					padding: "24px 32px",
					textAlign: "center",
					fontSize: "1.82em",
				}}>
					<Latex display>{"\\forall\\, C \\in \\text{CA},\\; \\exists\\, C':\\; L_{\\{\\text{RT, LT}\\}}(C') = L_{\\{\\text{RT, LT}\\}}(C) \\;\\wedge\\; \\delta_{C'}(*, \\#, *) = \\#"}</Latex>
				</div>
			)}
		</div>
	);
}

export function TitleSlideContent() {
	return (
		<FlexBox height="100%" flexDirection="column">
			<Heading>Cellular Automata</Heading>
			<Text>Formalized in Lean 4 With GitHub Copilot</Text>
      <Text><a href="https://github.com/hediet/lean-cellular-automata">https://github.com/hediet/lean-cellular-automata</a></Text>
		</FlexBox>
	);
}

export function BioSlideContent() {
	return (
		<FlexBox flexDirection="column" >
			<Heading fontSize="h3">About Me</Heading>
			<Text >
				<strong>Henning Dieterichs</strong>
			</Text>
			<UnorderedList >
				<ListItem>Software engineer at <strong>Microsoft</strong> — working on <strong>VS Code</strong> and <strong>GitHub Copilot</strong> since 2021</ListItem>
				<ListItem>Bachelor's thesis on <strong>cellular automata</strong> under Thomas Worsch at KIT (2018)</ListItem>
				<ListItem>Master's thesis on <strong>formal verification with Lean</strong></ListItem>
				<ListItem>This project: a personal hobby combining both interests</ListItem>
			</UnorderedList>
		</FlexBox>
	);
}

export function FormalizationComparisonSlideContent({ step }: { step: number }) {

	const sectionStyle: React.CSSProperties = {
		display: "flex",
		flexDirection: "column",
		gap: 8,
	};

	const labelStyle: React.CSSProperties = {
		fontSize: "0.85em",
		fontWeight: 700,
		color: "#666",
		textTransform: "uppercase",
		letterSpacing: "0.05em",
		marginBottom: 2,
	};

	const noteStyle: React.CSSProperties = {
		...codeStyle,
		fontSize: "0.78em",
		background: "#fff8f0",
		padding: "12px 16px",
	};

	const noteStyleGreen: React.CSSProperties = {
		...codeStyle,
		fontSize: "0.78em",
		background: "#f0fff0",
		padding: "12px 16px",
	};

	const noteStyleBlue: React.CSSProperties = {
		...codeStyle,
		fontSize: "0.78em",
		background: "#f0f0ff",
		padding: "12px 16px",
	};

	return (
		<AutoScale zoomRange={{ min: 1, max: 1 }}>
			<div style={{ padding: "0 32px" }}>
			<Heading fontSize="h3">Formalization: Literature vs. Lean</Heading>

			<div style={sectionStyle}>
				<div style={labelStyle}>Literature (typical definition)</div>
				<div style={{ fontSize: "1.3em", padding: "8px 0" }}>
					<Latex display>{"C = (Q,\\; \\Sigma,\\; \\#,\\; \\delta,\\; F^+)"}</Latex>
				</div>
				<div style={{ display: "flex", gap: 24, flexWrap: "wrap", fontSize: "1.05em", padding: "0 8px" }}>
					<span><Latex>{"Q"}</Latex> — finite state set</span>
					<span><Latex>{"\\Sigma \\subseteq Q"}</Latex> — input alphabet</span>
					<span><Latex>{"\\#  \\in Q"}</Latex> — border symbol</span>
					<span><Latex>{"\\delta: Q^3 \\to Q"}</Latex></span>
					<span><Latex>{"F^+ \\subseteq Q"}</Latex> — accepting</span>
				</div>

					<div style={noteStyle}>
{`Border constraint: often δ(#, #, #) = # (quiescent) or δ(*, #, *) = # (dead)
Varies by author — must track which convention each paper uses.`}
					</div>
			
			</div>

			<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

			<div style={sectionStyle}>
				<div style={labelStyle}>Our Lean Formalization</div>
				<div style={{ display: "flex", gap: 16 }}>
					<div style={{ ...codeStyle, flex: 1 }}>
{`structure CellAutomaton (α β : Type) where
  Q       : Type
  [fin    : Fintype Q]
  [dec    : DecidableEq Q]
  δ       : Q → Q → Q → Q
  embed   : α → Q
  project : Q → β`}
					</div>
					<div style={{ ...codeStyle, flex: 1 }}>
{`abbrev LCellAutomaton (α) :=
  CellAutomaton (Option α) Bool

structure tCellAutomaton (α : Type)
    extends LCellAutomaton α where
  t : ℕ → ℕ
  p : ℕ → ℤ`}
					</div>
				</div>
			
			</div>
			</div>
		</AutoScale>
	);
}

const codeStyle: React.CSSProperties = {
  fontFamily: "'Fira Code', 'Cascadia Code', 'Consolas', monospace",
  fontSize: "1.2em",
  background: "#f5f5f5",
  borderRadius: 8,
  padding: "16px 20px",
  lineHeight: 1.5,
  whiteSpace: "pre",
  overflow: "hidden",
  margin: "8px 0",
};

export function ComputationComparisonSlideContent() {
	const labelStyle: React.CSSProperties = {
		fontSize: "0.85em",
		fontWeight: 700,
		color: "#666",
		textTransform: "uppercase",
		letterSpacing: "0.05em",
		marginBottom: 2,
	};

	return (
		<AutoScale zoomRange={{ min: 0.1, max: 1 }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Computation</Heading>

				<div style={{ marginBottom: 16 }}>
					<div style={labelStyle}>Literature</div>
					<div style={{ fontSize: "1.15em", padding: "8px 0" }}>
						<Latex display>{"\\Delta_C(c)(i) = \\delta(c_{i-1},\\, c_i,\\, c_{i+1}) \\qquad \\Delta_C^{\\,t}(c) = \\underbrace{\\Delta_C \\circ \\cdots \\circ \\Delta_C}_{t\\text{ times}}(c)"}</Latex>
					</div>
					</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div>
					<div style={labelStyle}>Our Lean Formalization</div>
					<div style={{ display: "flex", gap: 16 }}>
						<div style={{ ...codeStyle, flex: 1 }}>
              {`def Config (\u03b1: Type) := \u2124 \u2192 \u03b1

def next (C: CellAutomaton \u03b1 \u03b2) (c: Config C.Q): Config C.Q :=
  fun p => C.\u03b4 (c (p - 1)) (c p) (c (p + 1))`}
						</div>
					</div>
          <div style={{ display: "flex", gap: 16 }}>
            <div style={{ ...codeStyle, flex: 1 }}>
              {`def Trace (\u03b1: Type) := \u2115 \u2192 \u03b1

def nextt (C: CellAutomaton \u03b1 \u03b2) (c: Config C.Q): Trace (Config C.Q) :=
  fun t => Nat.iterate (C.next) t c

def comp (c: Config C.Q) : Trace (Config \u03b2) :=
  C.project_config \u2218 C.nextt c
`}
            </div>
          </div>
				</div>
			</div>
		</AutoScale>
	);
}

export function EmbeddingComparisonSlideContent({ step }: { step: number }) {
	const labelStyle: React.CSSProperties = {
		fontSize: "0.85em",
		fontWeight: 700,
		color: "#666",
		textTransform: "uppercase",
		letterSpacing: "0.05em",
		marginBottom: 2,
	};

	return (
		<AutoScale zoomRange={{ min: 0.1, max: 1 }}>
			<div style={{ padding: "0 32px" }}>
			<Heading fontSize="h3">Word Embedding & Language Recognition</Heading>

			<div style={{ marginBottom: 16 }}>
				<div style={labelStyle}>Literature</div>
				<div style={{ fontSize: "1.15em", padding: "8px 0" }}>
					<Latex display>{"\\overline{w}(i) = \\begin{cases} w_i & 0 \\le i < |w| \\\\ \\# & \\text{otherwise} \\end{cases} \\qquad L_{\\text{RT}}(C) = \\bigl\\{\\, w \\in \\Sigma^* \\mid \\Delta_C^{\\,|w|-1}(\\overline{w})(0) \\in F^+ \\bigr\\}"}</Latex>
				</div>
			</div>

			<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

			<div>
				<div style={labelStyle}>Our Lean Formalization</div>
				<div style={{ display: "flex", gap: 16 }}>
					<div style={{ ...codeStyle, flex: 1 }}>
{`def word_to_config (w : Word α) : Config (Option α) :=
  fun p =>
    if p ≥ 0 ∧ p < w.length
    then some w[p.toNat]
    else none

notation "⟬" w "⟭" => word_to_config w`}
					</div>
					<div style={{ ...codeStyle, flex: 1 }}>
{`def embed_config (c : Config α) : Config C.Q :=
  fun p => C.embed (c p)

instance : Coe (Config α) (Config C.Q) :=
  ⟨embed_config⟩`}
					</div>
				</div>
				<div style={codeStyle}>
{`def tCellAutomaton.accepts (w : Word α) : Bool :=
  C.comp ⟬w⟭ (C.t w.length) (C.p w.length)

def tCellAutomaton.L : Language α :=
  { w | C.accepts w }`}
				</div>
			</div>
			</div>
		</AutoScale>
	);
}

export function CAClassesSlideContent() {
	return (
		<AutoScale zoomRange={{ min: 0.1, max: 1 }}>
			<div style={{ padding: "0 32px" }}>
			<Heading fontSize="h3">CA Classes</Heading>
			<div style={{ display: "flex", gap: 16 }}>
          <div style={{ ...codeStyle, flex: 1 }}>
            {`def CA   := { C ∈ tCellAutomata α | C.p = fun _ => 0 }
def CA_rt := CA α |> t_rt α
def CA_2n := CA α |> t_2n α
def CA_lt := CA α |> t_lt α

def CAr  := { C | C.p = fun n => (n: ℤ) }`}
          </div>
				<div style={{ ...codeStyle, flex: 1 }}>
{`def t_rt (S: Set (tCellAutomaton α)) :=
  { C ∈ S | ∀ n, C.t n = n - 1 }
def t_2n (S: Set (tCellAutomaton α)) :=
  { C ∈ S | ∀ n, C.t n = 2 * n }
def t_lt (S: Set (tCellAutomaton α)) :=
  { C ∈ S | ∃ c: ℕ, ∀ n, C.t n = c * n }`}
				</div>
			</div>
			<div style={{ display: "flex", gap: 16 }}>
				<div style={{ ...codeStyle, flex: 1 }}>
{`def OCA  := { C ∈ CA α | C.left_independent }
def OCA_rt := OCA α |> t_rt α
def OCA_2n := OCA α |> t_2n α
def OCA_lt := OCA α |> t_lt α`}
				</div>
				<div style={{ ...codeStyle, flex: 1 }}>
{`def OCAr  := { C ∈ CAr α | C.right_independent }
def OCAr_rt := OCAr α |> t_rt α
def OCAr_2n := OCAr α |> t_2n α
def OCAr_lt := OCAr α |> t_lt α`}
				</div>
			</div>

			<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

			<div style={codeStyle}>
{`def \u2112 [d: DefinesLanguage T \u03b1] (s: Set T): Set (Language \u03b1) :=
  fun L => \u2203 ca: T, ca \u2208 s \u2227 L = DefinesLanguage.L ca

theorem ca_linear_time_eq_2n: \u2112 (CA_lt \u03b1) = \u2112 (CA_2n \u03b1) := by sorry
theorem ocar_lt_eq_ca_rt: \u2112 (OCAr_lt \u03b1) = \u2112 (CA_rt \u03b1) := by sorry`}
			</div>
			</div>
		</AutoScale>
	);
}

export function ClassicalResultsSlideContent() {
	const results: { label: React.ReactNode; lines: number }[] = [
        { label: <span><Latex>{"\\{w \\mid |w| = 2^n\\} \\in \\mathscr{L}(\\text{CA}_{\\text{rt}})"}</Latex></span>, lines: 817 },
		{ label: <span><strong>OCA ↔ CA</strong> simulation with factor-2 time overhead</span>, lines: 279 },
		{ label: <span><strong>Quiescent border</strong> for arbitrary and for left-independent CAs</span>, lines: 422 },
		{ label: <span><strong>Dead border</strong> — absorbing border preserving trace for <Latex>{"t < c \\cdot |w|"}</Latex></span>, lines: 772 },
        { label: <span><strong>k-step additive RT speedup</strong> — <Latex>{"\\text{trace}_{C'}(w)(i) = \\text{trace}_C(w)(i + k)"}</Latex> for <Latex>{"i \\geq |w| - 1"}</Latex></span>, lines: 194 },
        { label: <span><strong>Speedup by a constant factor</strong> by running a CA on a compressed configuration</span>, lines: 179 },
	];

	return (
		<AutoScale zoomRange={{ min: 0.1, max: 1 }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Verified Results from the Literature</Heading>
				<UnorderedList>
					{results.map(({ label, lines }, i) => (
						<ListItem key={i} style={{ fontSize: "0.8em", marginBottom: 4 }}>
							<div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline" }}>
								{label}
								<span style={{ color: "#999", marginLeft: 16, whiteSpace: "nowrap", fontSize: "0.85em" }}>~{lines} lines</span>
							</div>
						</ListItem>
					))}
                  <ListItem  style={{ fontSize: "0.8em", marginBottom: 4 }}>
                    <div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline" }}>
                      And more
                    </div>
                  </ListItem>
				</UnorderedList>
			</div>
		</AutoScale>
	);
}

export function TraceDefinitionSlideContent() {
	return (
		<AutoScale zoomRange={{ min: 0.1, max: 1 }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Trace & Real-Time Trace</Heading>

				<div style={{ marginBottom: 16, fontSize: "1.4em" }}>
					<Text style={{ marginBottom: 8 }}>
						The <strong>trace</strong> of <Latex>{"C"}</Latex> on a configuration <Latex>{"c"}</Latex> is the temporal output sequence at position 0:
					</Text>
					<Latex display>{"\\text{trace}_C(c) : \\mathbb{N} \\to \\Gamma, \\quad t \\mapsto \\text{project}\\bigl(\\Delta_C^{\\,t}(c)_0\\bigr)"}</Latex>
				</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div style={{ marginBottom: 16, fontSize: "1.4em" }}>
					<Text style={{ marginBottom: 8 }}>
						The <strong>real-time trace</strong> is a length-preserving transduction:
					</Text>
					<Latex display>{"\\text{trace\\_rt}_C(w) = \\bigl(\\text{trace}_C(\\overline{w})(0),\\; \\text{trace}_C(\\overline{w})(1),\\; \\dots,\\; \\text{trace}_C(\\overline{w})(|w|-1)\\bigr)"}</Latex>
				</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div style={{ display: "flex", gap: 16 }}>
					<div style={{ ...codeStyle, flex: 1 }}>
{`def trace (c: Config α): Trace β := (C.comp c · 0)
  
def trace_rt (C: CellAutomaton α? β) (w: Word α): Word β := (List.range w.length).map (C.trace ⟬w⟭)`}
					</div>
				</div>
			</div>
		</AutoScale>
	);
}

export function AdviceDefinitionSlideContent({ step }: { step: number }) {
	const alph = step >= 0 ? "(\\Sigma \\times \\Gamma)" : "";
	const alphSig = step >= 0 ? "(\\Sigma)" : "";
	
	return (
		<AutoScale zoomRange={{ min: 0.1, max: 1 }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Advice Functions</Heading>

				<div style={{ marginBottom: 16, fontSize: "1.56em" }}>
					<Text style={{ marginBottom: 8 }}>
						An <strong>advice</strong> is a length-preserving map <Latex>{"f : \\Sigma^* \\to \\Gamma^*, \\quad |f(w)| = |w|"}</Latex>
					</Text>
				</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div style={{ marginBottom: 16, fontSize: "1.56em" }}>
					<Text style={{ marginBottom: 8 }}>
						It induces <Latex>{"f^*"}</Latex> to annotate a word:
					</Text>
					<Latex display>{`f^*(w) := w \\otimes f(w) = \\bigl((w_0, f(w)_0),\\; \\dots,\\; (w_{n-1}, f(w)_{n-1})\\bigr)`}</Latex>
				</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div style={{ marginBottom: 16, fontSize: "1.56em" }}>
					<Text style={{ marginBottom: 8 }}>
						The languages accepted by a CA with advice <Latex>{"f"}</Latex>:
					</Text>
					<Latex display>{`\\mathscr{L}\\bigl(\\text{CA}_{\\text{rt}}${alph} \\,/\\, f\\bigr) = \\bigl\\{\\, L \\subseteq \\Sigma^* \\;\\big|\\; L \\circ f^* \\in \\mathscr{L}\\bigl(\\text{CA}_{\\text{rt}}${alph}\\bigr) \\,\\bigr\\}`}</Latex>
				</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div style={{ marginBottom: 16, fontSize: "1.56em" }}>
					<Text style={{ marginBottom: 8 }}>
						<strong><Latex>{"f"}</Latex> is RT-closed</strong> if <Latex>{"f"}</Latex> does not increase the power of RT CAs:
					</Text>
					<Latex display>{`\\mathscr{L}\\bigl(\\text{CA}_{\\text{rt}}${alph} \\,/\\, f\\bigr) = \\mathscr{L}\\bigl(\\text{CA}_{\\text{rt}}${alphSig}\\bigr)`}</Latex>
				</div>
			</div>
		</AutoScale>
	);
}

function TraceGrid({ id, CS, WORD_LEN, GRID_COLS, inputColor, inputStroke, traceColor, traceStroke, splitColor, splitStroke }: {
	id: string;
	CS: number;
	WORD_LEN: number;
	GRID_COLS: number;
	inputColor: string;
	inputStroke: string;
	traceColor: string;
	traceStroke: string;
	splitColor?: string;
	splitStroke?: string;
}) {
	const TRACE_LEN = WORD_LEN - 1;
	const TOTAL_ROWS = TRACE_LEN + 1;
	const MARGIN = 10;
	const LABEL_W = 30;
	const viewW = 2 * MARGIN + GRID_COLS * CS;
	const viewH = TOTAL_ROWS * CS;
	const r = CS * 0.35;

	return (
		<svg
			viewBox={`${-LABEL_W} 0 ${viewW + LABEL_W} ${viewH}`}
			preserveAspectRatio="xMidYMid meet"
			style={{ width: "100%", maxHeight: "100%", display: "block" }}
		>
			<defs>
				<clipPath id={`split-tr-${id}`}>
					<polygon points={`${MARGIN},${0} ${MARGIN + CS},${0} ${MARGIN + CS},${CS}`} />
				</clipPath>
				<clipPath id={`split-bl-${id}`}>
					<polygon points={`${MARGIN},${0} ${MARGIN + CS},${CS} ${MARGIN},${CS}`} />
				</clipPath>
			</defs>
			{Array.from({ length: TOTAL_ROWS }, (_, t) => {
				const y = t * CS;
				return (
					<g key={t}>
						<text x={MARGIN - 6} y={y + CS / 2} textAnchor="end" dominantBaseline="central" fontSize={CS * 0.45} fill="#999" fontStyle="italic">
							t={t}
						</text>
						{Array.from({ length: GRID_COLS }, (_, i) => (
							<rect key={i} x={MARGIN + i * CS} y={y} width={CS} height={CS} fill="#f5f5f5" stroke="#ddd" strokeWidth={0.5} />
						))}
					</g>
				);
			})}
			{/* Input word circles at row 0 */}
			{Array.from({ length: WORD_LEN }, (_, wi) => {
				const x = MARGIN + wi * CS + CS / 2;
				const y = CS / 2;
				if (wi === 0 && splitColor) {
					return (
						<g key={`word-${wi}`}>
							<circle cx={x} cy={y} r={r} fill={splitColor} stroke={splitStroke ?? splitColor} strokeWidth={0.8} clipPath={`url(#split-bl-${id})`} />
							<circle cx={x} cy={y} r={r} fill={inputColor} stroke={inputStroke} strokeWidth={0.8} clipPath={`url(#split-tr-${id})`} />
							<line x1={x - r * 0.707} y1={y - r * 0.707} x2={x + r * 0.707} y2={y + r * 0.707} stroke="#333" strokeWidth={0.8} />
							<text x={x} y={y} textAnchor="middle" dominantBaseline="central" fontSize={CS * 0.38} fill="#fff" fontWeight="bold">{wi + 1}</text>
						</g>
					);
				}
				return (
					<g key={`word-${wi}`}>
						<circle cx={x} cy={y} r={r} fill={inputColor} stroke={inputStroke} strokeWidth={0.8} />
						<text x={x} y={y} textAnchor="middle" dominantBaseline="central" fontSize={CS * 0.38} fill="#fff" fontWeight="bold">{wi + 1}</text>
					</g>
				);
			})}
			{/* Trace circles at column 0, rows 1..TRACE_LEN */}
			{Array.from({ length: TRACE_LEN }, (_, ti) => {
				const x = MARGIN + CS / 2;
				const y = (ti + 1) * CS + CS / 2;
				return (
					<g key={`trace-${ti}`}>
						<circle cx={x} cy={y} r={r} fill={traceColor} stroke={traceStroke} strokeWidth={0.8} />
						<text x={x} y={y} textAnchor="middle" dominantBaseline="central" fontSize={CS * 0.38} fill="#fff" fontWeight="bold">{ti + 2}</text>
					</g>
				);
			})}
		</svg>
	);
}

export function TraceCompositionResultSlideContent({ step }: { step: number }) {
	const CS = 24;
	const WORD_LEN = 5;
	const GRID_COLS = 5;
	const TRACE_LEN = WORD_LEN - 1;
	const TOTAL_ROWS = TRACE_LEN + 1;
	const LABEL_W = 30;
	const r = CS * 0.35;
	const TRANS = "all 0.8s ease";

	const YELLOW = "#f59e0b";
	const YELLOW_STROKE = "#d97706";
	const RED = "#e74c3c";
	const RED_STROKE = "#c0392b";
	const BLUE = "#2563eb";
	const BLUE_STROKE = "#1d4ed8";

	const showCA1 = step >= 0 && step < 3;
	const showCA2 = step >= 1 && step < 3;
	const merged = step === 2;
	const showContent = step >= 3;

	// CA1: top-right. Origin at (g1x, g1y)
	const GAP = CS * 2;
	const g1x = LABEL_W + TRACE_LEN * CS + GAP;
	const g1y = 0;
	// CA2: bottom-left. Origin at (g2x, g2y)
	const g2x = LABEL_W;
	const g2y = TOTAL_ROWS * CS + GAP;

	const totalW = g1x + GRID_COLS * CS + 20;
	const totalH = g2y + TOTAL_ROWS * CS;

	// Red diagonal line in CA1 grid: from (0,0) to approx (p=1.7, t=3.3) in cell coords
	const diagEndCol = 1.7;
	const diagEndRow = 3.3;

	function numberedCircle(cx: number, cy: number, radius: number, color: string, stroke: string, label: number, transition?: string) {
		return (
			<g style={transition ? { transition } : undefined}>
				<circle cx={cx} cy={cy} r={radius} fill={color} stroke={stroke} strokeWidth={0.8} style={transition ? { transition } : undefined} />
				<text x={cx} y={cy} textAnchor="middle" dominantBaseline="central" fontSize={CS * 0.38} fill="#fff" fontWeight="bold" style={transition ? { transition } : undefined}>{label}</text>
			</g>
		);
	}

	function renderGridCells(gx: number, gy: number) {
		return (
			<g transform={`translate(${gx}, ${gy})`}>
				{Array.from({ length: TOTAL_ROWS }, (_, t) => (
					<g key={t}>
						<text x={-6} y={t * CS + CS / 2} textAnchor="end" dominantBaseline="central" fontSize={CS * 0.45} fill="#999" fontStyle="italic">
							t={t}
						</text>
						{Array.from({ length: GRID_COLS }, (_, i) => (
							<rect key={i} x={i * CS} y={t * CS} width={CS} height={CS} fill="#f5f5f5" stroke="#ddd" strokeWidth={0.5} />
						))}
					</g>
				))}
			</g>
		);
	}

	// Positions for each red cell (i=0..4):
	// In CA1 space: (col=0, row=i) i.e. x = g1x + CS/2, y = g1y + i*CS + CS/2
	// In CA2 space: (col=i, row=0) i.e. x = g2x + i*CS + CS/2, y = g2y + CS/2
	// Merged: on diagonal in CA1 grid: uniform on line from (0,0) to (diagEndCol, diagEndRow)
	function redPos(i: number): { x: number; y: number } {
		if (merged) {
			const frac = i / (WORD_LEN - 1);
			return {
				x: g1x + frac * diagEndCol * CS + CS / 2,
				y: g1y + frac * diagEndRow * CS + CS / 2,
			};
		}
		// At CA1 position
		return { x: g1x + CS / 2, y: g1y + i * CS + CS / 2 };
	}

	// Blue cells: CA2 trace at (col=0, rows 1..4) → in merged, move to CA1 trace position (col=0, rows 1..4)
	function bluePos(ti: number): { x: number; y: number } {
		if (merged) {
			return { x: g1x + CS / 2, y: g1y + (ti + 1) * CS + CS / 2 };
		}
		return { x: g2x + CS / 2, y: g2y + (ti + 1) * CS + CS / 2 };
	}

	// Yellow cells: CA1 input at (col=wi, row=0)
	function yellowPos(wi: number): { x: number; y: number } {
		return { x: g1x + wi * CS + CS / 2, y: g1y + CS / 2 };
	}

	const redR = merged ? r * 0.5 : r;

	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%" }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Main Result 1: Trace Composition</Heading>
			</div>
			<div style={{ flex: 1, background: "#f0f0f0", display: "flex", alignItems: "center", justifyContent: "center", padding: "16px 32px" }}>
				{showContent ? (
					<div style={{ display: "flex", flexDirection: "column", alignItems: "center", gap: 24 }}>
						<img src="/media/main-result-1.png" alt="Main Result 1" style={{ maxWidth: "100%", maxHeight: "60%", objectFit: "contain" }} />
						<div style={{ fontSize: 22, textAlign: "center", lineHeight: 2 }}>
                            <div>~2070 Lines of code</div>
							<div>Without speedup: <Latex>{"|Q_C| = \\Theta\\!\\left(|Q_{C_1}|^{96} \\cdot |Q_{C_2}|^{24}\\right)"}</Latex></div>
							<div>With speedup: <Latex>{"|Q_C| \\geq |Q_{C_1}|^{96} \\cdot |Q_{C_2}|^{24} \\uparrow\\uparrow 6"}</Latex></div>
						</div>
					</div>
				) : (
				<svg
					viewBox={`0 0 ${totalW} ${totalH}`}
					preserveAspectRatio="xMidYMid meet"
					style={{ height: 500, display: "block" }}
				>
					<defs>
						<clipPath id="ca1-split-tr">
							<polygon points={`${g1x},${g1y} ${g1x + CS},${g1y} ${g1x + CS},${g1y + CS}`} />
						</clipPath>
						<clipPath id="ca1-split-bl">
							<polygon points={`${g1x},${g1y} ${g1x + CS},${g1y + CS} ${g1x},${g1y + CS}`} />
						</clipPath>
						<clipPath id="ca2-split-tr">
							<polygon points={`${g2x},${g2y} ${g2x + CS},${g2y} ${g2x + CS},${g2y + CS}`} />
						</clipPath>
						<clipPath id="ca2-split-bl">
							<polygon points={`${g2x},${g2y} ${g2x + CS},${g2y + CS} ${g2x},${g2y + CS}`} />
						</clipPath>
					</defs>
					{/* CA1 grid (always visible when step >= 0) */}
					<g style={{ opacity: showCA1 ? 1 : 0, transition: "opacity 0.5s ease" }}>
						{renderGridCells(g1x, g1y)}
					</g>

					{/* CA2 grid (visible step >= 1, fade out on merge) */}
					<g style={{ opacity: showCA2 && !merged ? 1 : 0, transition: "opacity 0.5s ease" }}>
						{renderGridCells(g2x, g2y)}
					</g>

					{/* Connection lines (visible step >= 1, fade out on merge) */}
					{showCA2 && Array.from({ length: WORD_LEN }, (_, i) => (
						<line
							key={`conn-${i}`}
							x1={g1x + CS / 2}
							y1={g1y + i * CS + CS / 2}
							x2={g2x + i * CS + CS / 2}
							y2={g2y + CS / 2}
							stroke={RED}
							strokeWidth={1.5}
							strokeDasharray="4 3"
							opacity={merged ? 0 : 0.6}
							style={{ transition: "opacity 0.5s ease" }}
						/>
					))}

					{/* Yellow input circles for CA1 */}
					{showCA1 && Array.from({ length: WORD_LEN }, (_, wi) => {
						const { x, y } = yellowPos(wi);
						return (
							<g key={`y-${wi}`} clipPath={wi === 0 && !merged ? "url(#ca1-split-tr)" : undefined}>
								{numberedCircle(x, y, r, YELLOW, YELLOW_STROKE, wi + 1)}
							</g>
						);
					})}

					{/* Red cells - animate between positions */}
					{showCA1 && Array.from({ length: WORD_LEN }, (_, i) => {
						const { x, y } = redPos(i);
						return (
							<g key={`r-${i}`} style={{ transition: TRANS }} clipPath={i === 0 && !merged ? "url(#ca1-split-bl)" : undefined}>
								{numberedCircle(x, y, redR, RED, RED_STROKE, i + 1, TRANS)}
							</g>
						);
					})}

					{/* Red cells from CA2 input - overlap with CA1 red on merge */}
					{showCA2 && Array.from({ length: WORD_LEN }, (_, i) => {
						const pos = merged ? redPos(i) : { x: g2x + i * CS + CS / 2, y: g2y + CS / 2 };
						return (
							<g key={`r2-${i}`} style={{ transition: TRANS, opacity: merged ? 0 : 1 }} clipPath={i === 0 && !merged ? "url(#ca2-split-tr)" : undefined}>
								{numberedCircle(pos.x, pos.y, merged ? redR : r, RED, RED_STROKE, i + 1, TRANS)}
							</g>
						);
					})}

					{/* Blue cells - CA2 trace, animate to CA1 trace on merge */}
					{showCA2 && Array.from({ length: TRACE_LEN }, (_, ti) => {
						const { x, y } = bluePos(ti);
						return (
							<g key={`b-${ti}`} style={{ transition: TRANS }}>
								{numberedCircle(x, y, r, BLUE, BLUE_STROKE, ti + 2, TRANS)}
							</g>
						);
					})}

					{/* Blue half at CA2 (0,0) */}
					{showCA2 && !merged && (() => {
						const x = g2x + CS / 2;
						const y = g2y + CS / 2;
						return (
							<g clipPath="url(#ca2-split-bl)">
								{numberedCircle(x, y, r, BLUE, BLUE_STROKE, 1)}
							</g>
						);
					})()}

					{/* Split cell overlay at CA1 (0,0): yellow/red */}
					{showCA1 && (() => {
						const { x, y } = yellowPos(0);
						const { x: rx, y: ry } = redPos(0);
						// Only show split when red is at (0,0) i.e. not merged
						if (!merged) {
							return (
								<line x1={x - r * 0.707} y1={y - r * 0.707} x2={x + r * 0.707} y2={y + r * 0.707} stroke="#333" strokeWidth={0.8} />
							);
						}
						return null;
					})()}

					{/* Split cell overlay at CA2 (0,0): red/blue */}
					{showCA2 && !merged && (() => {
						const x = g2x + CS / 2;
						const y = g2y + CS / 2;
						return (
							<line x1={x - r * 0.707} y1={y - r * 0.707} x2={x + r * 0.707} y2={y + r * 0.707} stroke="#333" strokeWidth={0.8} />
						);
					})()}
				</svg>
				)}
			</div>
		</div>
	);
}

export function MainResult2SlideContent() {
	return (
		<AutoScale zoomRange={{ min: 0.1, max: 0.8 }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Main Result 2: Characterization of Causal RT-Closed Advice</Heading>

				<div style={{ marginBottom: 16, fontSize: "1.6em" }}>
					<Text style={{ marginBottom: 8 }}>
						Definition: An advice <Latex>{"f"}</Latex> is <strong>causal</strong> (prefix-stable) if prefixes determine prefixes:
					</Text>
					<Latex display>{"f(w)_{[0..i)} = f(w')_{[0..i)} \\quad \\text{whenever } w_{[0..i)} = w'_{[0..i)}"}</Latex>
				</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div style={{ marginBottom: 16, fontSize: "1.6em" }}>
					<Text style={{ marginBottom: 8 }}>
						<strong>Characterization of Causal RT-Closed Advice:</strong>
					</Text>
					<Latex display>{"f \\text{ is RT-closed} \\;\\wedge\\; f \\text{ is causal} \\;\\Longleftrightarrow\\; \\exists\\, C :\\; f = \\text{trace\\_rt}_C"}</Latex>
				</div>

				</div>
		</AutoScale>
	);
}

export function MainResult3SlideContent() {
	return (
		<AutoScale zoomRange={{ min: 0.1, max: 0.8 }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Main Result 3: Two-Stage Advices</Heading>

				<div style={{ marginBottom: 16, fontSize: "1.6em" }}>
					<Text style={{ marginBottom: 8 }}>
						An advice <Latex>{"f"}</Latex> is <strong>two-stage</strong> if it factors as:
					</Text>
					<Latex display>{"f = M \\circ \\text{trace\\_rt}_C"}</Latex>
					<Text style={{ marginBottom: 8 }}>
						where <Latex>{"C"}</Latex> is a CA and <Latex>{"M"}</Latex> is a finite-state transducer scanning right-to-left (!).
					</Text>
				</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div style={{ marginBottom: 16, fontSize: "1.6em" }}>
					<Text style={{ marginBottom: 8 }}>
						<strong>Two-stage advices are RT-closed:</strong>
					</Text>
					<Latex display>{"f \\text{ is two-stage} \\;\\Longrightarrow\\; f \\text{ is RT-closed}"}</Latex>
				</div>

				<div style={{ borderTop: "1px solid #ddd", margin: "12px 0" }} />

				<div style={{ marginBottom: 16, fontSize: "1.6em" }}>
					<Text style={{ marginBottom: 8 }}>
						<strong>Closed under composition:</strong>
					</Text>
					<Latex display>{"f_1, f_2 \\text{ two-stage} \\;\\Longrightarrow\\; f_2 \\circ f_1 \\text{ two-stage}"}</Latex>
				</div>

			</div>
		</AutoScale>
	);
}

export function PipelineDiagramSlideContent() {
	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%" }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Main Result 1: Composition Pipeline</Heading>
			</div>
			<div style={{ flex: 1, display: "flex", alignItems: "center", justifyContent: "center", padding: "16px 32px" }}>
				<img src="/media/pipeline.drawio.svg" alt="Composition Pipeline" style={{ maxWidth: "100%", maxHeight: "600px", objectFit: "contain" }} />
			</div>
		</div>
	);
}

export function Quote1SlideContent() {
	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%" }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Why is Verification With Lean Difficult?</Heading>
			</div>
			<div style={{ flex: 1, display: "flex", alignItems: "center", justifyContent: "center", padding: "16px 32px" }}>
				<img src="/media/quote1-technical-difficulties.png" alt="Quote: Technical Difficulties" style={{ maxWidth: "100%", maxHeight: "100%", objectFit: "contain" }} />
			</div>
		</div>
	);
}

export function Quote2SlideContent() {
	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%" }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Why is Verification With Lean Difficult?</Heading>
			</div>
			<div style={{ flex: 1, display: "flex", alignItems: "center", justifyContent: "center", padding: "16px 32px" }}>
				<img src="/media/quote2-difficult-proof.png" alt="Quote: Difficult Proof" style={{ maxWidth: "100%", maxHeight: "100%", objectFit: "contain" }} />
			</div>
		</div>
	);
}

export function AILoop1SlideContent() {
	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%" }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Why is Verification With Lean Easy?</Heading>
			</div>
			<div style={{ flex: 1, display: "flex", alignItems: "center", justifyContent: "center", padding: "16px 32px" }}>
				<img src="/media/ai-loop.drawio.svg" alt="AI Loop" style={{ maxWidth: "100%", maxHeight: "100%", objectFit: "contain" }} />
			</div>
		</div>
	);
}

export function AILoop2SlideContent() {
	return (
		<div style={{ display: "flex", flexDirection: "column", width: "100%", height: "100%" }}>
			<div style={{ padding: "0 32px" }}>
				<Heading fontSize="h3">Why is Verification With Lean Easy?</Heading>
			</div>
			<div style={{ flex: 1, display: "flex", alignItems: "center", justifyContent: "center", padding: "16px 32px" }}>
				<img src="/media/ai-loop2.drawio.svg" alt="AI Loop 2" style={{ maxWidth: "100%", maxHeight: "100%", objectFit: "contain" }} />
			</div>
		</div>
	);
}

export function QuestionsSlideContent() {
	return (
		<FlexBox height="100%" flexDirection="column">
			<Heading>Discussion</Heading>
		</FlexBox>
	);
}

export function DesigningCAWithAISlideContent() {
	return (
		<FlexBox height="100%" flexDirection="column">
			<Heading fontSize="h3">Practical Example: Designing CA with AI</Heading>
            <a href="https://gist.github.com/hediet/e3569a7c6b4b7c4f7d4a7db4101047de#file-1_session-md">Chat Session</a>
		</FlexBox>
	);
}

export interface SlideEntry {
	readonly name: string;
	readonly stepCount: number;
	readonly render: (step: number) => React.ReactNode;
}

export const slideRegistry: readonly SlideEntry[] = [
	{ name: "Title", stepCount: 0, render: () => <TitleSlideContent /> },
	{ name: "Bio", stepCount: 0, render: () => <BioSlideContent /> },
	{ name: "Definition", stepCount: 9, render: (step) => <DefinitionSlideContent step={step} /> },
	{ name: "ExpMiddle", stepCount: 0, render: () => <ExpMiddleSlideContent /> },
	{ name: "ExpWord", stepCount: 8, render: (step) => <ExpWordSlideContent step={step} /> },
	{ name: "Formalization", stepCount: 0, render: (step) => <FormalizationComparisonSlideContent step={step} /> },
	{ name: "Computation", stepCount: 0, render: () => <ComputationComparisonSlideContent /> },
	{ name: "Embedding", stepCount: 0, render: (step) => <EmbeddingComparisonSlideContent step={step} /> },
	{ name: "CAClasses", stepCount: 0, render: () => <CAClassesSlideContent /> },
	{ name: "ClassicalResults", stepCount: 0, render: () => <ClassicalResultsSlideContent /> },
	{ name: "DesigningCAWithAI", stepCount: 0, render: () => <DesigningCAWithAISlideContent /> },
	{ name: "TraceDefinition", stepCount: 0, render: () => <TraceDefinitionSlideContent /> },
	{ name: "TraceResults", stepCount: 4, render: (step) => <TraceCompositionResultSlideContent step={step} /> },
	{ name: "PipelineDiagram", stepCount: 0, render: () => <PipelineDiagramSlideContent /> },
	{ name: "AdviceDefinition", stepCount: 1, render: (step) => <AdviceDefinitionSlideContent step={step} /> },
	{ name: "MainResult2", stepCount: 0, render: () => <MainResult2SlideContent /> },
	{ name: "MainResult3", stepCount: 0, render: () => <MainResult3SlideContent /> },
	{ name: "Quote1", stepCount: 0, render: () => <Quote1SlideContent /> },
	{ name: "Quote2", stepCount: 0, render: () => <Quote2SlideContent /> },
	{ name: "AILoop1", stepCount: 0, render: () => <AILoop1SlideContent /> },
	{ name: "AILoop2", stepCount: 0, render: () => <AILoop2SlideContent /> },
	{ name: "Questions", stepCount: 0, render: () => <QuestionsSlideContent /> },
];

function SteppedSlide({ entry }: { entry: SlideEntry }) {
	const { step, placeholder } = useSteps(entry.stepCount);
  	return <>{placeholder}{entry.render(step)}</>;
}

export function Presentation() {
	return (
		<Deck theme={theme}>
			{slideRegistry.map((entry) => (
				<Slide key={entry.name} padding="0px">
					<SteppedSlide entry={entry} />
				</Slide>
			))}
		</Deck>
	);
}
