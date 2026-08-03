# TypeScript Elaborator v3.2 Mixed-Curry Retirement Plan

Plan-ID: `TYPESCRIPT-ELABORATOR-V3_2-MIXED-CURRY-RETIREMENT`

Status: completed and final-green under `D-DTTLF-USABILITY-083`; local
rollback-safe checkpoint follows this reviewed document state

Decision: on 2026-08-03 the user approved the exact retirement recommendation
recorded after the completed goal. The local comparison/checkpoint baseline is
`1891f809a57d4f862ac7c7f39125e1a99b6d9dd5` on
`goal/typescript-elaborator-v3.2`.

Authority: `emdash2/emdash3_2.lp`, `emdash2/emdash3_2_checks.lp`, the active
kernel SOP and Foundations, the canonical-syntax report, and the completed
mixed-introduction plan history. This cleanup does not reopen the completed
binder architecture.

## Architectural Verdict

The mixed-curry experiment is mathematically meaningful as a transposition
from sections over a variance-sensitive total context to a curried displayed
functor. It is not the fundamental introduction architecture for categorical
binders. The completed implementation instead constructs nested
`lambda^n`/`lambda^f`, compact `lambda^fd`, and compact/expanded `lambda^nd`
directly through classifier-appropriate recursive contextual compilers and
existing internal action owners.

The retained source audit establishes:

- no file under `src/v3_2` imports or constructs a mixed-curry owner;
- TypeScript tests mention `mixed_curry` or `mix_uncurried_family` only in
  negative assertions proving that direct binders do not emit them;
- the positive contextual-curry, negative contextual-curry, and specialized
  mixed-curry owners occur only in their contiguous active-kernel sections,
  their dedicated Lambdapi diagnostic area, the generated catalog, and
  historical plans; and
- the book and public canonical surface do not expose mixed curry. The
  canonical syntax explicitly makes nested binders fundamental.

Consequently the unused opaque owners and their conversion rules impose trust
and maintenance cost without a selected consumer. Git history is the archive;
keeping a live optional module would preserve that cost and is not selected.

## Exact Retirement Boundary

Remove the complete contiguous active-kernel blocks:

1. `17f. Reusable contextual curry basis`, containing
   `sigma_functord_curry_func`, `sigma_functord_curry_sec`,
   `sigma_functord_curry_fibre_func`, their opacity directive, and five
   projection/action rules; and
2. `17g. Variance-correct mixed displayed curry`, containing the transparent
   `mix_*` context presentations, `neg_sigma_functord_curry_*`,
   `mixed_curry_*`, and their dedicated projection/action rules.

Remove the matching `Mixed displayed curry` diagnostic area from
`emdash3_2_checks.lp`, ending immediately before the general
`catalog-area: auto` formation checks. Also remove the one earlier
cross-area `assertnot` comparing `Functor_catd_const_funcd` with the retired
negative-Sigma facade; after facade retirement that assertion is vacuous.
Regenerate rather than hand-edit the catalog and health report.

Preserve:

- section 17e section pullback and internal Pi action;
- generic product/curry, Sigma/Pi, pullback, totalization, and section action;
- `Unit_prof`, `Hom_catd`, `Functor_catd`, `Transf_catd`, and their internal
  object/base-arrow/higher action;
- `Functor_comp_pair_funcd` and every direct categorical binder/compiler;
- TypeScript negative assertions that direct binders do not detour through
  mixed curry; and
- historical plan analysis, augmented by a supersession/retirement record.

Do not revert commits wholesale. In particular, generic prerequisites added
near the experiments may have independent consumers and remain active.

## Recovery And Non-Claims

The exact retired implementations remain recoverable from:

- `bed022fdab970109163da8415726a5bcc1ab5a89` — variance-correct mixed curry;
- `b6f803e37ec9c1a4241ab95c45a4fc8a8d992a89` — auxiliary contextual curry
  basis; and
- the completed plan and decision history.

No `.scratchpad` copy or optional live extension is created. Retirement does
not claim that the transposition is mathematically impossible; it records
that it has no selected active consumer and is not the binder architecture.
A future concrete consumer may propose a fresh, owner-position-qualified
reintroduction against the then-current kernel.

## Validation And Checkpoint Gate

Before editing the active files, probe the exact deletions in temporary
full-file copies. Promotion requires:

1. the copied kernel and copied diagnostic suite typecheck;
2. no surviving active source/check reference to a retired symbol;
3. bounded active `make check` success;
4. warning comparison against the `1097/159` baseline, with decreases
   classified and no new warning family;
5. strict LHS audit success;
6. regenerated catalog, TOC, health, and reviewer examples;
7. one final kernel `make ci` after the bounded tranche is otherwise green;
8. exact diff and whitespace review; and
9. one local rollback-safe checkpoint containing only the retirement,
   generated reports, and synchronized plans.

Do not run the root TypeScript aggregate: no TypeScript behavior or shared
TypeScript boundary changes. Do not push, merge, publish, delete a branch, or
remove a worktree.

## Implementation Evidence

The exact full-file-copy probe and promoted active edit remove the 587-line
semantic kernel block and 915 diagnostic lines. The latter count includes the
dedicated mixed-curry area and the earlier vacuous cross-area `assertnot`. The
kernel source map additionally drops the two retired 17f/17g headings, making
the active kernel diff 589 deletions. No surviving active kernel, diagnostic,
or generated-catalog entry names a retired owner; the remaining TypeScript
occurrences are deliberately negative assertions that direct binders do not
emit the old route.

Both copied files and the promoted active kernel/check suite typecheck. The
warning inventory changes from 1,097/159 to 1,086/159. The eleven removed
unjoinable pairs are exactly nine retired `fapp1_fapp0` self-interactions and
two retired `fapp0`/`tapp0_fapp0` interactions; no warning category, rule
family, or term head is added. The strict audit remains 0 unreviewed
reconstructible slots, with 53 annotated slots across 33 intentional clauses.
The regenerated catalog contains 1,779 checks across 68 mapped areas and zero
unclassified checks, down by the retired 22-check area. The source TOC is
green at 86 headings spanning sections 0--20.

One health-generation attempt overlapped the mechanical deletion of the two
stale source-map headings and therefore observed an invalidated compiled
snapshot while entering `directed_dimension.lp`. A stable-source focused
rerun of that example passes. This is process-order evidence, not a semantic
failure. The authoritative frozen-source health generation subsequently
passes all six kernel/diagnostic targets and all 35 reviewer examples, and
writes source-metrics snapshot
`sha256:35891c71f54783d1e62c3c237e62578c34f4414d5e9e2d6bcadb6cdfd7ad1bce`.
The one final kernel CI accepts that snapshot and passes all 41 Lambdapi
targets, 39 repository tests, five document-registry tests, active-reference
and report-header lint, book evidence/typography/KaTeX/assembly checks, the
strict LHS audit, and strict catalog freshness. No root TypeScript aggregate
was run. The bounded local checkpoint is the only remaining operation.

## Decision Ledger

- **2026-08-03 — D-DTTLF-USABILITY-083 approved.** Retire the unused active
  contextual/mixed-curry packages and dedicated diagnostics, retain generic
  prerequisites and direct binders, use Git history as the archive, run the
  proportional Lambdapi gates, and checkpoint the bounded cleanup.
- **2026-08-03 — D-DTTLF-USABILITY-083 implementation final-green.** The exact
  retirement, warning comparison, inventory regeneration, stable-source
  health matrix, and one final kernel CI all pass. No TypeScript behavior,
  public surface, generic foundation, direct binder, push, merge, or
  publication changed.
