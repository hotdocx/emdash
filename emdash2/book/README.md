# Emdash Book Workspace

This directory is the authoring source for *Functorial Type Theory: Univalent
Foundations for Mathematics*.

The chapter files are authoritative. The assembled
`print/public/emdash-book.md` file is generated and must not be
edited by hand.

## Source map

- `book.json` owns metadata, source order, and the output target.
- `expansion.json` owns the retained Chapter 1--8 central-theorem audit and
  the ratified Chapter 9--17 migration, conceptual ownership,
  central-theorem/status targets, terminology, and translation contracts.
- `STYLE.md` owns prose, formal-status, and attribution conventions.
- `evidence.json` maps checked claims to active Lambdapi declarations
  and reviewer evidence.
- `CREDITS.md` and `LICENSE.md` establish the attribution
  gate for HoTT-derived material and are included in the assembled back
  matter.
- `references/third-party-sources.json` pins external source
  revisions and records every future adaptation.
- `RELEASE.md` owns the clean-install, PDF, visual-review, and release
  checklist.

## Commands

Run from the repository root:

```bash
./scripts/pnpmw run book:assemble
./scripts/pnpmw run book:typography
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
./scripts/pnpmw run book:pdf
./scripts/pnpmw run book:pdf:check
./scripts/pnpmw run book:release
./scripts/pnpmw run book:promote
```

From `emdash2/`, use the same root-owned commands through the wrapper:

```bash
../scripts/pnpmw run book:assemble
../scripts/pnpmw run book:typography
../scripts/pnpmw run book:check
../scripts/pnpmw run book:render
../scripts/pnpmw run book:pdf
../scripts/pnpmw run book:pdf:check
```

The development edition is theorem-led. Chapters 1--7 are driven by the
prerequisites of the WalkingEnd/Nat computation; Chapter 8 contains the
central proof; Chapters 9--17 form the ratified category-theory, universal-
construction, and directed-duality spiral. Appendix G owns the formal
presentation. Contents and the evidence appendix are generated from
their structured authorities.

Generated release artifacts live under `output/pdf/` and are ignored by Git.
The release command paginates, exports, normalizes, and checks the manifest's
PDF, then reports its checksum. Attach the artifact and checksum to a release
rather than editing or committing the generated file as source.

After a checked release, `book:promote` atomically copies the manifest PDF and
assembled Markdown to `docs/emdash-book.pdf` and `docs/emdash-book.md`.
Those tracked paths are distribution artifacts, not additional authoring
sources.

## Authority

The book is exposition, not an implementation authority. Active Lambdapi
sources and checks outrank the book whenever they disagree. Correct a stale
book claim and its evidence entry together.
