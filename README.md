# emdash — Functorial Type Theory

emdash is a research programme and executable formalization for functorial
type theory: categorical action is part of the computational language rather
than an external structure added after the fact. The development combines
dependent type theory with categories, directed families, functors,
transfors, and higher cells, using cut-elimination-inspired operations so
that functoriality and naturality can compute.

The current v3.2 edition is a checked development draft and a working,
bounded product—not a finished foundation, complete proof assistant, or claim
of global metatheory.

## Read And Review

Start with the current development edition of
[*Functorial Type Theory: Univalent Foundations for Mathematics*](./docs/emdash-book.pdf).
The active mathematical source is
[`emdash2/emdash3_2.lp`](./emdash2/emdash3_2.lp), together with the modules it
imports.

After bootstrapping a fresh checkout, launch the integrated browser reviewer:

```bash
./scripts/bootstrap-worktree.sh
./scripts/pnpmw run reviewer:dev
```

For a compact terminal walkthrough of the same architecture:

```bash
./scripts/pnpmw run demo:external-review
```

The browser workbench is client-side. It does not require a Lambdapi process
at production runtime, and this repository does not yet include a remote
deployment or publication workflow for it.

## What The Reviewer Shows

The reviewer brings four parts of the project into one place:

- an outer dependent logical framework, including a Sigma-telescope example;
- ordinary, natural, displayed-functorial, and displayed-natural categorical
  binders in their reviewed profiles;
- readable source, backend-neutral explicit emdash Core, inferred types,
  structural lowering, computation, and source-located failures; and
- the mathematical book alongside the executable examples and preserved
  minimal-Core playground.

The examples include nested functorial abstraction and a genuinely dependent
displayed chain. They are intended to expose the architecture and its present
boundary, not to simulate completion of the book's entire notation.

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
- Displayed contexts demonstrate independent fibrewise siblings, genuine
  dependency, and a bounded mixed telescope. Arbitrary depth, variance,
  exchange across dependency, and unrestricted displayed coherence remain
  open.
- The remaining Lambdapi library has not been proven mechanically
  transferable as one batch. Bulk transfer qualification is deliberately
  deferred to a future goal.
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
