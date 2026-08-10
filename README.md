# emdash — Functorial Type Theory

emdash is a research programme and executable formalization for functorial
type theory: categorical action is part of the computational language rather
than an external structure added after the fact. The development combines
dependent type theory with categories, directed families, functors,
transfors, and higher cells, using cut-elimination-inspired operations so
that functoriality and naturality can compute.

The active development now carries that calculus into local geometry:
Cat-valued presheaves, ordinary sieves and sites, a direct fixed-site
sheafification construction, universal-property commutative algebra, affine
geometry organized by the invertibility sieve $D_R(f)$, site-relative
schemes, and a supplied projective-line presentation. These layers keep
representability, locality, and construction hypotheses explicit.

The current v3.2 edition is a checked development draft and a working,
bounded product—not a finished foundation, complete proof assistant, or claim
of global metatheory.

## Read And Review

Start with the concise
[*Functorial Type Theory: An Executable Architecture for Directed Dependency*](./docs/emdash3_2.pdf)
overview, then continue to the current development edition of
[*Functorial Type Theory: Univalent Foundations for Mathematics*](./docs/emdash-book.pdf)
([assembled Markdown](./docs/emdash-book.md)).
The active mathematical source is
[`emdash2/emdash3_2.lp`](./emdash2/emdash3_2.lp), together with the modules it
imports.

Use the
[live integrated reviewer](https://hotdocx.github.io/emdash/)
to elaborate the bounded categorical syntax, inspect explicit Core and
computation, run the three-panel research report, and read the book in the
same client-side workbench.

To run that reviewer locally after bootstrapping a fresh checkout:

```bash
./scripts/bootstrap-worktree.sh
./scripts/pnpmw run reviewer:dev
```

For a compact terminal walkthrough of the same architecture:

```bash
./scripts/pnpmw run demo:external-review
```

The browser workbench is published from `main` by GitHub Pages. It is wholly
client-side and does not require a Lambdapi process or other production
backend.

## What The Reviewer Shows

The reviewer brings four parts of the project into one place:

- an outer dependent logical framework, including a Sigma-telescope example;
- ordinary, natural, displayed-functorial, and displayed-natural categorical
  binders in their reviewed profiles;
- readable source, backend-neutral explicit emdash Core, inferred types,
  structural lowering, computation, and source-located failures; and
- the mathematical book alongside the executable examples and preserved
  minimal-Core playground.

The examples include nested functorial abstraction, a genuinely dependent
displayed chain, and a displayed-natural telescope whose named variables cross
one Sigma dependency. They are intended to expose the architecture and its
present boundary, not to simulate completion of the book's entire notation.

## AI-Native Proof And Workspace Foundation

The local TypeScript/emdash layer now also provides a source-first foundation
for AI-authored developments: immutable proof plans, stable named goals,
fingerprinted checked artifacts, exact module/fragment workspace graphs,
locked mounted-file verification with offline cache reuse, finite explicit-
dictionary selection, and stable paper/diagram/proof bindings. These features
include a checked contextual `have` whose fact stays visible as a named source
obligation even when unused, plus root-scoped typed-term `refine` templates
which expand to ordinary `have`/`exact` plans. They lower to backend-neutral
explicit Core and use the TypeScript checker; they do not require a resident
proof server, MCP round trip, or Lambdapi process.

Ask the repository itself for the exact implemented and deferred envelope:

```bash
./scripts/emdash capabilities --format text
./scripts/emdash check --format text
./scripts/emdash goals --format text
./scripts/emdash workspace check \
  --project-root /absolute/project \
  --data-root /absolute/data

# Explicitly execute the demo management module as a macro, then check only
# its materialized canonical data through the general development command.
node --require ts-node/register \
  examples/v3_2_ai_proof_development_source.ts \
  > /absolute/project/emdash.proof-development.source.json
./scripts/emdash development goals \
  --project-root /absolute/project \
  --format text
```

The legacy proof commands deliberately exercise a fixed checked proof module;
`workspace check` accepts only canonical locked workspace files; and
`development check|goals|build` accepts only the fixed canonical
proof-development file under an explicit real root. It never imports the
management module or discovers an ambient project. The capability record
states those scopes rather than presenting this qualified local foundation as
an unrestricted host-language sandbox. In the browser reviewer's evidence
view, **Check paper proof states** replays the release-pinned examples and
keeps the named open goal visibly incomplete.

The detailed trust boundary, validation history, and consumer-gated next work
are in the
[`proof-assistant and goal-graph plan`](./docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md).

## Architecture And Authority

| Layer | Present role |
| --- | --- |
| Active Lambdapi v3.2 development | Authors and checks the categorical declarations, computation rules, and proof-time comparisons. It remains the mathematical authority. |
| TypeScript surface and explicit Core | Recursively elaborates a reviewed direct-TypeScript and textual surface into backend-neutral explicit owners. |
| Generic TypeScript dependent LF | Checks explicit Core, performs conversion and bounded reduction, and runs entirely in the client for the reviewer profile. |
| Lambdapi conformance route | Optionally emits deterministic judgments and compares selected results with the active kernel. It is a development oracle, not a production backend. |

The TypeScript implementation is therefore a real small checker/evaluator,
but only for its recorded profile. Readable syntax may omit parameters that
bidirectional typing can recover; it may not invent categorical action or
external naturality evidence when no internal construction owns it.

## Current Boundaries

- The text adapter is not a parser for every notation in the book or for
  arbitrary Lambdapi source. It accepts the reviewed mathematical
  constructions and fails closed outside them.
- Displayed contexts support arbitrary finite depth in the canonical ordered
  sibling/Sigma normal form, including displayed-functorial and displayed-
  natural witnesses, together with qualified depth-generic finite
  Hom-category recursion. Arbitrary dependency or variance DAGs, general mixed
  introduction/curry, exchange across dependency, and unrestricted displayed
  coherence remain open.
- The remaining Lambdapi library has not been proven mechanically
  transferable as one batch. Bulk transfer qualification is deliberately
  deferred to a future goal.
- Direct cover completion constructs a fixed-site Cat-valued sheafification
  reflector. A commutative-ring lift, left exactness, and base-change
  semantics are not yet derived from it.
- The affine and site-relative scheme layers retain supplied structure-sheaf
  and locality capabilities. The projective-line package retains its global
  object and actual overlap; representation-independent schemes, graded
  `Proj`, and general projective space remain open.
- Groupoidal specialization/closure and general normalization, confluence,
  canonicity, consistency, and semantic soundness for the combined calculus
  are not claimed.

These are continuation boundaries, not hidden assumptions of the examples
that already run.

## Contributor Setup And Focused Commands

Node 22.13 or newer is required. The repository uses the pinned pnpm wrapper
and one workspace lockfile; Lambdapi is additionally required for formal
kernel and conformance checks.

```bash
./scripts/bootstrap-worktree.sh
```

Use the smallest gate that covers a change:

```bash
./scripts/pnpmw run reviewer:dev        # integrated local browser reviewer
./scripts/pnpmw run demo:external-review
./scripts/pnpmw run check:ts            # root TypeScript workbench
./scripts/pnpmw run kernel:check         # active Lambdapi kernel
./scripts/pnpmw run book:check           # authored book contracts
```

Repository workflow and authority are defined in [`AGENTS.md`](./AGENTS.md);
formal-kernel changes also follow
[`emdash2/AGENTS.md`](./emdash2/AGENTS.md). Renewed TypeScript work starts
from the
[`v3.2 elaborator handoff`](./docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md),
which routes to the living plans and detailed validation history.

## Related Projects

- [Arrowgram](https://github.com/hotdocx/arrowgram/) — diagrams and structured
  technical documents.
- [Hotdocx](https://hotdocx.github.io/) — browser publishing and research
  workspaces.
- [LastRevision.pro](https://LastRevision.pro/) — hosted AI workspaces and
  automation.

## Historical TypeScript Prototype

Repository history and parts of the root workbench preserve an earlier
dependent-language feasibility prototype with bidirectional elaboration,
holes, unification, rewriting, and proof-state machinery. Those generic
mechanisms remain useful evidence, but the prototype's old category-specific
design is not an authority for v3.2. The
[`elaborator handoff`](./docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md) records
what was retained, replaced, and graduated in the renewed architecture.
