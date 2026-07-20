# m— / emdash

`emdash` is an experimental Lambdapi specification for functorial type
theory and a future proof assistant for strict/lax omega-categories,
omega-functors, omega-transformations (“transfors”), directed families, and
dependent categorical structure.

Its computational style treats coherence as typed computation: rewrite rules
select runtime normal forms, while narrowly scoped unification rules compare
proof-time presentations when neither direction should become computation.

## Headline result

The current development contains an opaque one-dimensional
walking-endomorphism directed HIT with a base `*` and a genuinely directed
loop `ell : * -> *`. A Cat-valued code, a contextual decoder, and a
directed normalization cell establish the checked carrier equivalence

```text
Hom_WalkingEnd(*,*) ≃ Nat.
```

The concrete one-object category `BNat` is a separate model, not the
definition of `WalkingEnd`. The loop is not the identity, has no right
inverse, and carries no native omega-equivalence evidence. The detailed
mathematical reading is in
`reports/EMDASH_FOUNDATIONS.md`.

## Where to start

- `emdash3_2.lp` is the active kernel and computation authority.
- `emdash3_2_walking_end_hit.lp` owns the walking HIT, Code,
  encode/decode, Nat comparison, and directed negative results.
- `emdash3_2_checks.lp` and `examples/` contain executable
  regressions and reviewer-facing examples.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`
  explains the current architecture and safe implementation workflow.
- `reports/EMDASH_FOUNDATIONS.md` is the mathematician-facing guide.
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`
  owns comment, example, and future parser notation.
- `reports/INDEX.md` indexes current plans and dated decision records.
- `AGENTS.md` contains mandatory repository-working rules.

The active one-way library extensions are:

- `emdash3_2_eq1_hom_action.lp` — native equality-valued next-hom
  action and groupoidality;
- `emdash3_2_eq1_evidence_property.lp` — evidence-property,
  retract-truncation, and finite-category object truncation;
- `emdash3_2_nat_arithmetic.lp` — reusable Nat arithmetic and sethood;
- `emdash3_2_walking_end_hit.lp` — the selected WalkingEnd
  development.

The retired D0/D1 compatibility layer and obsolete v2/v3.1 scratch material
are not active interfaces.

## Quick start

Prerequisite: `lambdapi` on `PATH`.

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
make examples
make ci
```

Useful focused commands:

```bash
scripts/probe.sh tmp/probes/name.lp
make check-warnings
make warning-summary
make audit-rules
make catalog
make toc
make health
```

Keep exploratory typechecks bounded. The current SOP explains rewrite,
unification, inferred-slot, and owner-position probing policy.

## Functorial Type Theory book

The new book, *Functorial Type Theory: Univalent Foundations for Mathematics*,
is authored in `book/` as chapter-sized Markdown sources. It leads with
the WalkingEnd/Nat theorem and then adapts the prerequisite spine of the HoTT
Book to the directed setting.

```bash
npm run install:print
npm run book:assemble
npm run book:check
npm run book:render
npm run book:release
```

`book/book.json` owns source order and metadata;
`book/evidence.json` maps checked prose claims to active declarations
and reviewer evidence. The generated
`print/public/emdash-book.md` is ignored and must not be edited by hand.
The release command produces and checks the ignored, versioned PDF declared by
the manifest; see `book/RELEASE.md` for its checksum and visual-QA policy.
See `book/README.md` and `print/README.md` for authoring and
renderer workflows.

## Status

Emdash v3.2 remains a research implementation. It does not yet claim a
finished surface parser, a complete weak omega-category metatheory, a full
computational univalence principle for every intended structure, or the full
initiality of the walking endomorphism. The living reports state these
boundaries precisely; dated reports preserve why earlier designs were chosen
or retired.
