# Adjunction From A Whole Hom Comparison: Retained Candidate

Date: 2026-09-17
Status: non-library experiment; promotion held for consumer justification
Base: `10bff3059d999b7f0f59caa9977ad13ea034a0d3`

The [living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
and [assembly ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md)
own scope and qualification. This directory preserves the exact uncommitted
candidate while keeping its declarations and rules out of active imports,
library registration and reviewer discovery. It is not a second adjunction
theory or a completed goal result.

`candidate.patch.gz` preserves the exact patch containing two candidate modules, two reviewers and
three import/registration edits. It introduces an ordinary-category
constructor into the existing Adjunction relation from a whole ProfComparison.
The existing Hom-comparison projection returns the supplied witness; unit and
counit components compute by applying the selected comparison/inverse to
identities. The native whole unit/counit heads remain in use. The other module
generalizes four evaluated DefIso cuts to arbitrary ProfComparison inputs,
with a real Prof_cat guard.

This is a new structural introduction principle. The existing interface does
not derive its body. Its input is mathematically sufficient for an ordinary
adjunction, but broader higher/profile claims are not established by the
tests. The earlier adjunction-usability macros instead introduce trusted
instances with declaration-backed operation agreements.

The whole-family reviewer applies the already declared postcomposition lift
to the new constructor. It checks interoperability; it does not derive that
lift or remove one of the existing structural assumptions. A production
consumer holding independently constructed whole Hom-comparison data has
not yet been identified. Promotion must justify that benefit, then complete
owner-position warning/SR, inference, audit, catalogue and health gates.

The exact uncompressed patch SHA-256 is:

```text
85ffe36f790b2a93073a714a1762e5fdb012e166a029df5d190021cd81c9362c
```

On the recorded baseline, check applicability from the Git root with:

```bash
gzip -dc emdash2/audits/adjunction-from-hom-comparison/candidate.patch.gz | git apply --check -
```

The compressed patch keeps superseded implementation text out of normal
source searches and preserves Git patch context whitespace byte-for-byte.
Applying the patch is an explicit experiment resumption, not part of normal
validation. In an authorized isolated checkout, apply it and run the two
focused reviewers through the standard guard, from `emdash2`:

```bash
env OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 scripts/probe.sh examples/prof_comparison_components.lp
env OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 scripts/probe.sh examples/one_cat_adjunction_introduction.lp
```

The last candidate runs passed at the default serial 2GiB/90s profile, with
warnings and subject reduction enabled:

- `prof_comparison_components-20260917-132520.log`;
- `one_cat_adjunction_introduction-20260917-132907.log`.

Logs remain in this worktree's ignored `emdash2/logs/probes/` directory.
No full promotion warning comparison or catalogue/health registration was
completed. The exact patch was checked both for reverse applicability before
removal and for forward applicability after removal. The active adjunction
mate owner and registrations were restored to their committed contents;
the independently qualified UA-1a core computation was retained.
