# TypeScript Elaborator v3.2 — Book Source Contract Correction

Date: 2026-07-30
Proposal-Row: BOOK-PROSE-CONTRACT-1A1
Review-Gate: H-DTTLF-BOOK-SOURCE-CONTRACT-01
Decision-ID: D-DTTLF-BOOK-REPOSITORY-002
Parent:
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_PROPOSAL.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_PROPOSAL.md)

## Measured Conflict

The approved authored edition replaces the obsolete
`optional future elaborator` entry in `emdash2/book/expansion.json` with
`bounded TypeScript elaborator and explicit Core`. Assembly, all 110 evidence
links, typography, and 1,317 KaTeX spans pass. `book:source` alone rejects the
approved metadata because `emdash2/print/scripts/check_book.mjs` hard-codes
the retired phrase.

## Exact Correction

Change only the corresponding expected string in
`emdash2/print/scripts/check_book.mjs`:

```text
optional future elaborator
```

to:

```text
bounded TypeScript elaborator and explicit Core
```

Retain the four-layer order check and every other source, evidence,
typography, rendering, and artifact contract unchanged.

## Proportional Validation

Run only:

```bash
./scripts/pnpmw --dir emdash2/print run book:source
node emdash2/print/scripts/validate_paper.mjs --group=book
```

The already-passing assembly, evidence, typography, and KaTeX stages are not
repeated. No PDF, renderer build, kernel check, TypeScript aggregate, or
browser gate is included.

## Non-Effects And Git Boundary

This correction adds no mathematical claim, owner, parser, checker, renderer
pipeline, document source, artifact, deployment, publication, or scale work.
It permits only bounded green local checkpoints under the existing D001 Git
boundary, with human supersession retained.
