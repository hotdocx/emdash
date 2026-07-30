# D-DTTLF-PRODUCT-SYNTAX-001 — Categorical Text Contract Review

Date: 2026-07-29
Gate: H-DTTLF-PRODUCT-SYNTAX-01
Decision: D-DTTLF-PRODUCT-SYNTAX-001
Status: approved as proposed under the user's standing unattended delegation
Human-Supersession: any later explicit human decision supersedes this record
Reviewed-Proposal-Checkpoint:
`5e33a58` (`docs: freeze categorical text syntax contract`)

## Review

No immediate human objection followed presentation and checkpointing of the
bounded SYNTAX-RESOLVE-0B proposal in
[`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md).
The user's standing delegation therefore approves that exact contract and
comparison row with human supersession.

This decision approves only:

- the parser-independent contract recorded at `5e33a58`;
- disposable comparison of the historical Parsimmon approach with a tiny
  local lexer/recursive-descent parser over the same first-slice grammar,
  spans, and failures;
- measurement of source size, project dependency impact, browser viability,
  diagnostic precision, and binder-mode extensibility;
- deletion or exclusion from the tracked tree of both disposable spikes
  before a semantic implementation checkpoint; and
- a subsequent immutable parser-selection and integrated-implementation
  proposal.

The comparison may use temporary files and a temporary package environment
outside the repository worktree. It must not edit the workspace lockfile,
package manifests, or generated `node_modules` graph.

## Required Selected-Slice Shape

Any later implementation proposal must preserve the reviewed vertical
boundary:

```text
source string
  -> identifier/application/lambda located nodes
  -> request-local typed name resolution
  -> existing CoreCategoricalProgram.lambda/apply
  -> existing contextual compiler and checker
```

It must propose the parser, located-node implementation, recursive resolver,
tests, executable example, and ledger synchronization together. A parser-only
or resolver-only runtime checkpoint does not satisfy this decision.

The first slice remains ordinary categorical and bounded to identifiers,
parentheses, neutral whitespace application, and one outer `:^f`
abstraction. It must compare its real results with the existing direct
TypeScript witnesses, including a whole-Hom application and zero/one/two
binder-use evidence.

## Explicit Non-Authorization

This decision authorizes no:

- selected parser or parser library;
- tracked source, test, example, export, package, dependency, or lockfile
  implementation;
- standalone public located AST or second `RawExpr`/checker layer;
- outer-LF, displayed `:^fd`/`:^nd`, dependent-telescope, Pi, let, hole,
  implicit-argument, recovery, or arbitrary-depth text syntax;
- Core owner/node, categorical action case, checker/evaluator, runtime rule,
  proof-time unification rule, contextual compiler, or semantic-profile
  change;
- browser entry, UI, worker, server, GitHub Pages workflow, deployment, or
  publication;
- Lambdapi source/acquisition parser or production Lambdapi dependency;
- product/usability/scale/whole-transfer graduation; or
- push, merge, publication, release, PR, rebase, amend, reset, history
  rewrite, cleanup, branch deletion, or worktree removal.

## Validation And Git Boundary

The comparison report must make the losing alternative and its costs
explicit, freeze the exact selected implementation proposal, and receive a
separate review before tracked semantic code is added.

This review is a decision record only. It does not select or implement a
parser.
