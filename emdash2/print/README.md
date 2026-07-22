# Emdash print and book renderer

The `print/` workspace renders two archival v2 article variants, the active
v3.2 article workbench, and the generated *Functorial Type Theory* book with
the same Markdown/KaTeX/diagram/Paged.js pipeline.

## Reproducible setup

From the repository root:

```bash
npm run install:print
npm run dev
```

`install:print` runs a clean lockfile install. The committed default is
the exact published package `@hotdocx/arrowgram@1.0.0`; it does not
depend on a host-specific checkout.

The browser accepts these registered selectors:

- `/` or `?paper=index` — full archival v2 article;
- `?paper=index_0` or `?paper=0` — short archival v2 article;
- `?paper=index_3_2` — active v3.2 article workbench;
- `?paper=emdash-book` or `?paper=book` — generated book.

Absolute HTTP(S) URLs and `?paper=ls:key` remain explicit
development inputs. Other local filenames are rejected.

## Book workflow

Book sources live outside this workspace under `../book/`.

```bash
npm run book:assemble
npm run book:check
npm run book:render
npm run book:pdf
npm run book:pdf:check
npm run book:release
```

- `book:assemble` deterministically joins the ordered manifest sources
  into ignored `public/emdash-book.md`.
- `book:check` checks manifest/provenance agreement, stable anchors and
  links, evidence owners/reviewers, generated freshness, critical proof order,
  and embedded diagram JSON.
- `book:render` builds with local assets and performs the bounded
  browser/pagination check for the book, including external-request,
  overflow, internal-link, and accessible-media gates.
- `book:pdf` exports the Paged.js pages through headless Chromium, fixes the
  manifest-owned metadata with the exact `pdf-lib` dependency, canonicalizes
  process-local tagged-table structure IDs without removing the tag tree, and
  applies a deterministic document identifier with `qpdf`.
- `book:pdf:check` verifies structure, page size, fixed metadata, extracted
  text, blank pages, and font embedding with `qpdf` and Poppler.
- `book:release` runs the browser and PDF gates together.

The assembler also runs before development and production builds. Never edit
the generated book file.

PDF production requires `qpdf`, `pdfinfo`, `pdftotext`, `pdffonts`, and
`pdftoppm` on `PATH`. The latter four commands are supplied by Poppler. The
versioned PDF under `../output/pdf/` and visual-review images under
`../tmp/pdfs/` are ignored generated artifacts.

## Documents and checks

`documents.json` is shared by the browser loader, schema validator, and
browser renderer. Each entry defines its safe filename and selectors, layout,
check groups, lifecycle, source mode and authority, and render budget. An
authored article owns its own `print/public/*.md` file; the generated book is
owned by `book/book.json` and must never claim its assembled Markdown as an
authority. Its `timeoutMs` is the
authoritative page, navigation, and completed-pagination budget for both the
console and PDF gates; increase that document-specific value only when a
measured longer artifact requires it.

To add a document:

1. add its Markdown file or generator;
2. add one registry entry with unique selectors;
3. run `npm run validate:paper`;
4. run the appropriate bounded render group.

Useful commands:

```bash
npm run validate:paper
node scripts/validate_paper.mjs --group=articles
node scripts/check_console.mjs --group=book
npm run check:render
```

`check:render` validates and paginates every registered document.
Warnings are reported; console/page/request failures, malformed math, raw
Markdown tables, diagram error boxes, and missing pages fail the check.

## Optional local Arrowgram development

To test an unpublished local core without changing committed dependency
metadata:

```bash
cd print
npm ci
npm link --no-save /home/user1/arrowgram/packages/arrowgram
npm run book:check
npm run build
npm ci
```

The final `npm ci` restores the published package. Before committing,
verify that `package.json` and `package-lock.json` contain no
`file:` dependency, absolute host path, or link entry. The assembled
book must have the same hash in published and local-link modes.

## Pipeline map

- `src/App.tsx` resolves the registry document, loads Markdown, and
  invokes Paged.js.
- `src/pipeline/commonMarkdownPipeline.tsx` protects math and code,
  renders Mermaid/Vega-Lite/Arrowgram blocks, runs Showdown with tables, and
  sanitizes HTML.
- `src/utils/sanitizeHtml.ts` owns the DOMPurify policy.
- `src/preview/pagedCleanup.ts` removes empty generated pages.
- `src/print-styles.css` owns page and column layout.
- `scripts/validate_paper.mjs` uses the package-exported Arrowgram
  schema.
- `scripts/check_console.mjs` owns bounded browser checks and process
  cleanup.
- `scripts/export_book_pdf.mjs` and `scripts/check_book_pdf.mjs` own the
  deterministic release artifact and its structural/text/font gates.
- `scripts/preview_runtime.mjs` owns the shared cleanup-safe preview server.

## Authoring notes

- In Arrowgram JSON, LaTeX backslashes must be doubled and labels should be
  wrapped in math delimiters.
- Keep math delimiters balanced so Showdown cannot interpret underscores as
  emphasis.
- Use `.fullwidth` around diagrams that must span a two-column layout.
- Prefer `break-inside: avoid` for figures or tables that should not
  split.
- Use the package schema and implementation as the diagram-format authority;
  do not copy its TypeScript interface into this repository.

The current renderer is an emdash adapter with behavior not yet proven
equivalent to `@hotdocx/arrowgram-web`. Preserve document selection,
table handling, sanitization, local assets, and browser checks until a
separate parity review supports further upstream consolidation.
