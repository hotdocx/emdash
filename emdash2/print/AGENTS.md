---
title: emdash paper pipeline SOP (`print/`), and How to read and generate `arrowgram` diagrams
---

# Purpose

The `print/` workspace renders the research paper from a single Markdown source:

- Paper source: `print/public/index.md`
- Short/conference variant: `print/public/index_0.md`
- Renderer app: `print/src/App.tsx`
- Output: “Print / Save PDF” in the preview UI (Paged.js paginates the HTML)

The pipeline supports:

- KaTeX math: inline `$...$` and display `$$...$$`
- Mermaid diagrams: `<div class="mermaid">…</div>`
- Vega-Lite charts: `<div class="vega-lite">{…JSON…}</div>`
- Arrowgram commutative diagrams: `<div class="arrowgram">{…JSON…}</div>`

# Quickstart

From the repo root:

1. Install deps (once):
   - `npm install -w print`
2. Dev preview:
   - `npm run dev -w print`
   - open the shown URL and use the UI toggle for 1-column / 2-column
   - choose which paper to preview via query param:
     - default (archive/full): `/?paper=index.md` (or just `/`)
     - short (conference): `/?paper=index_0.md` (also accepts `?paper=0`)
3. “Print / Save PDF”:
   - use the UI button (top-right) which triggers the browser print dialog

# File map (what to touch for what)

Paper content

- `print/public/index.md`: the paper (YAML frontmatter + Markdown + embedded diagram blocks)
- `print/public/index_0.md`: shorter paper variant (same renderer/pipeline)

Renderer / parsing

- `print/src/App.tsx`: transforms `index.md` into HTML:
  - Pre-renders Mermaid to SVG and Arrowgram to SVG
  - Converts Markdown with Showdown
  - Renders KaTeX math to HTML
  - Feeds final HTML into Paged.js for pagination

Styling / layout

- `print/src/print-styles.css`: 2-column layout, column-spanning blocks (`.fullwidth`), diagram sizing, tables (`.emdash-table`), etc.

Arrowgram schema + validation

- `print/src/types.ts`: Zod schema for Arrowgram (used by validation tooling)
- `print/scripts/validate_paper.mjs`: parses all Arrowgram / Vega-Lite blocks from `print/public/index*.md` and validates JSON (Arrowgram via Zod)

Browser console / end-to-end checks

- `print/scripts/check_console.mjs`: Playwright-based smoke test:
  - starts `vite preview`
  - loads the app
  - fails on `console.error`, `pageerror`, request failures
  - treats KaTeX strict warnings (e.g. `[mathVsTextAccents]`) as failures
  - checks both `index.md` (default) and `index_0.md` (via `?paper=index_0.md`)

NPM scripts (most useful)

- `npm run validate:paper -w print`: validate embedded JSON blocks
- `npm run check:console -w print`: headless browser console check
- `npm run check:render -w print`: validate + build + console check (recommended before sending a PDF)

## Adding more variants

You can add additional public paper variants as `print/public/index_<N>.md` (e.g. `index_1.md`). The renderer can load any `*.md` via `?paper=...`, but the validation script currently auto-discovers and validates only files matching `index*.md`.

# Authoring conventions (important gotchas)

## KaTeX / math escaping

- Prefer normal KaTeX:
  - inline: `$f \\circ g$`
  - display:
    - `$$`
    - `\\mathrm{Hom}_{E(z)}(f_!w, x).`
    - `$$`
- Avoid Unicode combining accents or TeX accent macros that KaTeX treats as “text mode only” in math (these become console warnings and fail `check:console`).

## Arrowgram label formatting (common mistakes)

Arrowgram specs are JSON. That means **every backslash in LaTeX must be doubled for JSON**, and the label must be wrapped in `$...$`.

Typical examples that work well:

- Use explicit spaces with `\\ ` in LaTeX:
  - `"label": "$\\bullet \\ b_2$"`
  - `"label": "$0\\ \\bullet$"`
- Prefer `\\circ` etc.:
  - `"label": "$g \\circ f$"`
- Prefer `label_alignment: "left"` / `"right"` (often reads better than `"over"` in dense diagrams).

## Showdown + underscores + HTML tags inside math

Problem: Markdown parsers may interpret `_` in math as emphasis and inject HTML like `<em>`, breaking KaTeX.

Mitigation: `print/src/App.tsx` protects `$...$` and `$$...$$` blocks before running Showdown and restores them afterward.

If you see literal `<em>` tags inside formulas in the output, it usually means:
- the math delimiters are unbalanced, or
- the content accidentally left math mode (e.g. a missing `$`)

## Arrowgram JSON requirements

All Arrowgram diagrams must be valid JSON inside:

```html
<div class="arrowgram">
{ ... }
</div>
```

Rules:

- JSON strings must be valid JSON (escape backslashes).
- LaTeX labels inside Arrowgram JSON must be wrapped in math delimiters and double-escaped:
  - `"label": "$\\alpha$"`
  - `"label": "$f \\circ g$"`
- Arrow body styles are restricted; see `print/src/types.ts`.
- 2-cells can be drawn as “arrow-to-arrow” by using `name` on 1-arrows and referencing those names in the 2-arrow `from`/`to`.

Sizing tip:

- Arrowgram SVG scales to container width; to make a diagram appear larger in a column, reduce the coordinate span (smaller `left/top` maxima) so the computed `viewBox` is smaller.

## Mermaid diagrams in 2-column layout

If a Mermaid diagram is too wide, wrap it in:

```html
<div class="fullwidth">
  <div class="mermaid">
    ...
  </div>
</div>
```

This uses `.layout-two-column .fullwidth { column-span: all; }` in `print/src/print-styles.css`.

# Debugging playbook

## 1) JSON diagrams failing to render

Run:

- `npm run validate:paper -w print`

If Arrowgram JSON fails schema validation:
- check `style.body.name` is one of the allowed enums
- ensure `label` strings are valid JSON and LaTeX is double-escaped

## 2) “Diagram Error” boxes in the output

- Arrowgram errors: open browser console; the renderer logs parsing errors from `JSON.parse` and/or the Arrowgram runtime.
- Mermaid errors: usually Mermaid syntax; isolate by rendering in a minimal Mermaid live editor.

## 3) KaTeX warnings / math not rendering

Run:

- `npm run check:console -w print`

Typical causes:
- invalid math commands
- missing closing `$` / `$$`
- TeX accents used in math mode (KaTeX strict warns)

## 4) Something looks wrong only in the final PDF

Paged.js changes layout (page breaks, floats, columns). Use:

- toggle between 1-column and 2-column in the UI
- adjust CSS in `print/src/print-styles.css`
- prefer `break-inside: avoid` for figures/tables that should not split

# Local patches (what we changed and why)

These are “infrastructure” edits made while authoring the current paper; they explain why some parts of the pipeline behave the way they do.

## `print/src/App.tsx` (renderer hardening)

- **Math protection before Markdown**: `$...$` and `$$...$$` blocks are replaced by placeholder tokens before Showdown runs, then restored immediately after `makeHtml`. This prevents Showdown from turning `_` into `<em>` inside math.
- **Placeholder tokens avoid `_`**: placeholders use `AGPROT…AGPROT` tokens because underscores may be mutated by Markdown emphasis rules.
- **Code blocks protected from KaTeX pass**: `<pre>…</pre>` and `<code>…</code>` blocks are temporarily replaced so `$` inside code does not get interpreted as math.
- **“Double backslash” normalization**: KaTeX rendering trims a common authoring artifact where `\\omega` (etc.) accidentally appears in math; the renderer normalizes some of these back to `\omega` before calling KaTeX.

## `print/src/vite-env.d.ts` (TypeScript module typing)

- Adds a local module declaration for `pagedjs` (`Previewer.preview(...)`) so `print/src/App.tsx` typechecks without pulling in additional ambient types.

## `print/src/components/ArrowGramStatic.tsx` (Arrowgram SVG behavior)

- Uses `viewBox={diagram.viewBox}` with `className="w-full h-auto max-w-full"` so diagrams scale responsively to the column width.
- Keeps a small minimum size (`minWidth`, `minHeight`) to avoid “tiny” renders when diagrams are embedded in narrow contexts.

# Minimal checklist before sending a PDF

- `npm run check:render -w print`
- Open preview, toggle 2-column, scroll for:
  - missing diagrams
  - “Diagram Error” boxes
  - obvious KaTeX render failures
- Print to PDF from the preview UI

# How to read and generate `arrowgram` diagrams

You are an expert in Category Theory and Commutative Diagrams. 

Your goal is to generate "Arrowgram" diagram specifications based on the user's description.

Output ONLY valid JSON. Do not include markdown formatting.

The JSON specification format is as follows (TypeScript interface):

// Source of Truth: packages/arrowgram/src/types.ts
// IMPORTANT: Keep this in sync with the actual code!

interface NodeSpec {
  name: string; // Unique ID (e.g., "A", "node_1")
  label?: string; // LaTeX label (e.g. "$A$", "$X \\times B$"). MUST be wrapped in $.
  color?: string; // Hex color code (e.g. "#FF0000"). Default: "black".
  left: number; // X coordinate (pixels)
  top: number; // Y coordinate (pixels)
}

interface ArrowStyleSpec {
  mode?: "arrow" | "adjunction" | "corner" | "corner_inverse";
  head?: {
    name?: "normal" | "none" | "epi" | "hook" | "maps_to" | "harpoon";
    side?: "top" | "bottom"
  }; 
  tail?: {
    name?: "normal" | "none" | "mono" | "hook" | "maps_to";
    side?: "top" | "bottom"
  };
  // NOTE: "maps_to" renders a vertical bar (|). 
  // To create a standard "maps to" arrow (|->), use tail: { name: "maps_to" } and head: { name: "normal" }.
  
  body?: {
    name?: "solid" | "dashed" | "dotted" | "squiggly" | "wavy" | "barred" | "double_barred" | "bullet_solid" | "bullet_hollow" | "none"
  };
  level?: number; // 1 for single (->), 2 for double (=>), 3 for triple.
}

interface ArrowSpec {
  from: string; // Node ID OR Arrow ID (for 2-cells)
  to: string; // Node ID OR Arrow ID
  name?: string; // Unique arrow ID (required if this arrow is a target)
  label?: string; // LaTeX label (e.g. "$f$", "$\\pi$"). MUST be wrapped in $.
  label_alignment?: "over" | "left" | "right"; // "over" is default.
  color?: string; // Hex color for arrow stroke.
  label_color?: string; // Hex color for label.
  curve?: number; // Curvature (e.g positive 150 curves to the left of the arrow direction, and negative -150 curves to its right), 0 is straight
  shift?: number; // Parallel shift
  radius?: number; // For loops
  angle?: number; // For loops (degrees)
  shorten?: {
      source?: number; // Gap at source (px)
      target?: number; // Gap at target (px)
  };
  style?: ArrowStyleSpec;
}

interface DiagramSpec {
  version?: number;
  nodes: NodeSpec[];
  arrows?: ArrowSpec[];
}

Layout Guidelines:
- Coordinate system: (0,0) is top-left.
- Standard spacing: Nodes are usually 100-200 pixels apart.
- Centered diagrams usually look best around (300, 300) or similar.
- Use standard LaTeX for labels (e.g., "$\\pi$", "$f \\circ g$").
- IMPORTANT: All labels MUST be wrapped in dollar signs for math mode (e.g., "$A$", "$f$").
- For 2-cells (natural transformations), name the source/target arrows and connect a new arrow between them.

CRITICAL JSON SYNTAX RULE:
- **Double Escape Backslashes**: When writing LaTeX commands in the JSON string, you MUST double-escape backslashes. 
  - WRONG: "label": "$A \to B$" (Invalid JSON escape sequence)
  - CORRECT: "label": "$A \\to B$" (becomes "$A \to B$" in the parser, which is correct)
  - Example: Use "$\\pi$" for $\pi$, "$\\alpha$" for $\alpha$.

CRITICAL RULES FOR UPDATES:
1. When provided with an existing spec ("Current Diagram Spec"), you must return the FULL merged JSON.
2. PRESERVE the coordinates (left, top) of existing nodes unless the user explicitly asks to move them or reorganize the layout.
3. PRESERVE existing node IDs ("name") to maintain arrow connections.
4. If adding a new node, place it intelligently relative to connected nodes (e.g., forming a square or triangle).

---
EXAMPLES:

1. **Pullback Square (Corner)**
{
  "version": 1,
  "nodes": [
    { "name": "P", "left": 100, "top": 100, "label": "$P$" },
    { "name": "A", "left": 300, "top": 100, "label": "$A$" },
    { "name": "B", "left": 100, "top": 300, "label": "$B$" },
    { "name": "C", "left": 300, "top": 300, "label": "$C$" }
  ],
  "arrows": [
    { "from": "P", "to": "A", "label": "$p_1$" },
    { "from": "P", "to": "B", "label": "$p_2$" },
    { "from": "A", "to": "C", "label": "$f$" },
    { "from": "B", "to": "C", "label": "$g$" },
    { "from": "P", "to": "C", "style": { "mode": "corner" } }
  ]
}

2. **Natural Transformation (2-cell)**
{
  "nodes": [
    { "name": "A", "left": 100, "top": 200, "label": "$A$" },
    { "name": "B", "left": 400, "top": 200, "label": "$B$" }
  ],
  "arrows": [
    { "name": "F", "from": "A", "to": "B", "label": "$F$", "curve": 150 },
    { "name": "G", "from": "A", "to": "B", "label": "$G$", "curve": -150 },
    { "from": "F", "to": "G", "label": "$\\alpha$", "style": { "level": 2 } }
  ]
}

---

You are an expert academic writer and researcher. Your goal is to write and edit academic papers in Markdown format.
The papers are rendered using a pipeline supporting Arrowgram, Vega-Lite, Mermaid, and KaTeX.

Output ONLY valid Markdown.

### Document Structure & Metadata
Start the document with YAML frontmatter for the title and authors:
---
title: My Paper Title
authors: Author One & Author Two
---

### Capabilities & Syntax

1. **Standard Markdown**: Use headers (#, ##), lists, bold, italics, etc.

2. **Mathematics (KaTeX)**:
   - Inline: $E=mc^2$
   - Display:
     $$
     \int_{-\infty}^\infty e^{-x^2} dx = \sqrt{\pi}
     $$

3. **Commutative Diagrams (Arrowgram)**:
   Embed the JSON spec in a div with class "arrowgram".
   <div class="arrowgram">
   {
     "version": 1,
     "nodes": [...],
     "arrows": [...] 
   }
   </div>

4. **Charts (Vega-Lite)**:
   Embed the JSON spec in a div with class "vega-lite".
   <div class="vega-lite">
   {
     "$schema": "https://vega.github.io/schema/vega-lite/v5.json",
     "mark": "bar",
     "encoding": { ... },
     "data": { ... }
   }
   </div>

5. **Diagrams (Mermaid)**:
   Embed the Mermaid syntax in a div with class "mermaid".
   <div class="mermaid">
graph TD;
    A-->B;
   </div>

### Editing Rules
- If editing, PRESERVE existing structure and diagrams unless explicitly changed.
- If asked to add a visualization, choose the most appropriate tool (Arrowgram for category theory, Vega-Lite for data plots, Mermaid for flowcharts).
