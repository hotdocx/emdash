# Print Workspace Contributor Instructions

These rules apply to changes under `print/`. Human-facing setup,
authoring, document-selection, and local-upstream instructions live in
`print/README.md`.

## Authorities

- `documents.json` is the only allowlist and check registry for local
  renderable documents.
- `../book/book.json` owns book source order, metadata, and generated
  output.
- `src/pipeline/commonMarkdownPipeline.tsx` owns Markdown, math,
  diagram, and sanitization staging.
- The public `@hotdocx/arrowgram` package owns the Arrowgram schema.
  Do not recreate a local schema.

## Required behavior

- Never hand-edit `public/emdash-book.md`; run
  `npm run book:assemble`.
- Register every local Markdown document explicitly. Do not restore filename
  glob discovery or arbitrary local path loading.
- Keep the committed dependency and lockfile reproducible. A local Arrowgram
  link is opt-in, uses `--no-save`, and must not alter committed
  manifests or lockfiles.
- Keep KaTeX fonts and CSS local. Checked rendering must not require a CDN or
  other network request.
- Preserve Showdown table parsing, math/code protection, sanitization, and
  static Arrowgram/Mermaid reinsertion.
- Preserve checks for console errors, page errors, failed and external
  requests, malformed KaTeX, raw pipe tables, rendered error boxes,
  horizontal overflow, internal links, accessible media, replacement
  characters, and nonempty pagination.
- Every preview subprocess must be stopped on success, failure, timeout,
  `SIGINT`, and `SIGTERM`. Keep document render budgets
  bounded.
- Preserve the existing article documents while changing book behavior.
- Compare renderer parity before replacing this app with an upstream preview
  package. Book manifests, evidence links, and document registration remain
  emdash concerns.

## Validation

For book-only changes:

```bash
npm run book:check
npm run book:render
```

For a production or metadata change, also run the deterministic artifact gate:

```bash
npm run book:release
```

For renderer or shared-pipeline changes:

```bash
npm run validate:paper
npm run check:render
```

Run from `print/`, or use the corresponding root package aliases.
