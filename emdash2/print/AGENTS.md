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
  `./scripts/pnpmw run book:assemble` from the Git root.
- Register every local Markdown document explicitly. Do not restore filename
  glob discovery or arbitrary local path loading.
- Keep the committed dependency and root workspace lockfile reproducible. A
  local Arrowgram link is opt-in, uses `pnpm link` with an explicit path, and
  must not alter committed manifests or the lockfile.
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
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
```

For a production or metadata change, also run the deterministic artifact gate:

```bash
./scripts/pnpmw run book:release
```

For renderer or shared-pipeline changes:

```bash
./scripts/pnpmw --dir emdash2/print run validate:paper
./scripts/pnpmw --dir emdash2/print run check:render
```

Run these commands from the Git root. The wrapper preserves the pinned pnpm
version even when the task itself was started under `print/`.
