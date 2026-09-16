# Emdash Book Workspace

This directory is the authoring source for *Functorial Type Theory: Univalent
Foundations for Mathematics*.

Book record: [10.5281/zenodo.21544186](https://doi.org/10.5281/zenodo.21544186).
Code and source: [hotdocx/emdash](https://github.com/hotdocx/emdash).
The opening material and bibliography include the same self-reference.

The chapter files own authored prose. The assembled
`../print/public/emdash-book.md` file is generated and must not be
edited by hand.

## Source map

- `book.json` owns metadata, source order, and the output target.
- `expansion.json` owns the staged chapter-group architecture, conceptual
  ownership, theorem/status targets, terminology and translation contracts.
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
construction, and directed-duality spiral. Chapters 18--24 develop local
geometry, 25--28 groupoidal and Gray structure, 29 dependent simplexes,
30 Cartesian/indexed constructions, and 31 homology and proof-CAS integration.
Local edition `0.9.0-dev` includes the native whole-universality reformulation,
both displayed LES/snake certificates and their nonsplit example. Chapters 12
and 31 distinguish the declared ordinary structural interfaces from derived
homological results. General categorical terminality is still proposed; the
[consolidation review](../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_REVIEW.md)
records where reusable adjunction/Cartesian material should be developed next.
Appendix G owns the formal
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
