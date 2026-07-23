# Book Release Checklist

The source manifest in `book/book.json` owns the edition version and artifact
path. The assembled Markdown and PDF are generated artifacts; they are not
authoring authorities and are not committed by default. A release may attach
the PDF and its reported SHA-256 checksum.

The exporter preserves Chromium's tagged structure while canonicalizing its
process-local table-header IDs, then fixes manifest metadata and lets `qpdf`
own deterministic document identification and recompression. Do not remove
that normalization merely because two warm exports happen to agree; compare
fresh build/export cycles when changing the pipeline.

From the repository root:

```bash
./scripts/pnpmw install --offline --frozen-lockfile
./scripts/pnpmw run book:release
make -C emdash2 ci
```

Before publishing an edition:

- update `edition`, `editionVersion`, `publicationDate`, and `status` together;
- verify every third-party adaptation is present in the provenance ledger and
  compatible with the book license;
- confirm every checked claim has an active owner and independent reviewer;
- inspect the rendered PDF page images, including the title, contents, first
  page of every chapter/appendix, wide evidence tables, bibliography, credits,
  and license;
- confirm the PDF has the manifest title, author, subject, edition, fixed
  metadata dates, page count, embedded fonts, no replacement characters, and
  no external network requests;
- run the link, math, raw-table, overflow, page-break, and accessibility gates;
- run the semantic typography and strict KaTeX gates, and confirm extracted
  PDF text contains no literal or bare TeX control words;
- generate the PDF twice and confirm identical SHA-256 checksums;
- run full repository CI without changing Lambdapi semantics for production
  convenience;
- record the checksum and validation results in the current book-maintenance
  plan or release ledger before tagging or attaching the artifact.

If a release gate fails, fix the authoritative chapter, manifest, renderer,
or evidence source and regenerate. Never patch the assembled Markdown or PDF
directly.
