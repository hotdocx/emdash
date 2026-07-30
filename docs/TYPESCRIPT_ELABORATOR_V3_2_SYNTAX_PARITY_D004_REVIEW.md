# D-DTTLF-PRODUCT-SYNTAX-PARITY-004 — Dependent Context Review

Date: 2026-07-30
Gate: H-DTTLF-PRODUCT-SYNTAX-PARITY-04
Decision: D-DTTLF-PRODUCT-SYNTAX-PARITY-004
Status: approved as proposed under the user's standing unattended delegation
Human-Supersession: any later explicit human decision supersedes this record
Reviewed-Proposal-Checkpoint:
`4eada97f9ee8fe284b70dea6c0548dfdb9754189`
(`docs(v3.2): freeze dependent text parity proposal`)
Proposal-Ledger-Checkpoint:
`468fe48`
(`docs(v3.2): record dependent parity proposal checkpoint`)

## Review

No immediate human objection followed presentation and local checkpointing of
the bounded `SYNTAX-PARITY-1B3` proposal in
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md).
The user's standing unattended delegation therefore approves that exact
proposal with human supersession.

The selected annotated sources are:

```text
λ^fd (a : A; b : B). a
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
```

The annotation-free forms are also in scope when the expected contract
supplies the matching grouped source families:

```text
λ^fd (a; b). a
λ^fd (a; b, c; d). fibrePair b c
```

Direct TypeScript already checks both shapes through
`displayedDependentContextLambda` and the existing recursive contextual
compiler. The parser currently rejects only the reserved semicolon
presentation.

## Exact Authorization

The implementation may only:

- retain the three private located expression node kinds and activate
  semicolon-separated immutable binding groups in the existing lambda
  payload;
- interpret commas as independent siblings at one dependency level and
  semicolons as successive displayed dependency levels;
- accept only exact group sizes `[1,1]` and `[1,2,1]`;
- require portable names unique across the complete telescope;
- retain independently optional identifier annotations for every binding;
- add one `displayed-dependent-context-functor` expected contract containing
  the matching ordered source-family groups and one target family;
- require exact group/family cardinality and check every present annotation
  positionally against the corresponding expected family;
- flatten checked groups in source order and call the existing
  `CoreCategoricalProgram.displayedDependentContextLambda` exactly once;
- extend one immutable environment with all returned callback-local tokens
  and recursively resolve the body through the existing exact `indexOf`,
  `fibrePair`, `composeCells`, and generic `apply` routes;
- prove text/direct equality for explicit Core, inferred/expected classifier,
  abstraction trace, binding/group order, and applicable object/internalized-
  arrow observations for both direct shapes;
- preserve the complete parsing, expectation, annotation, group-shape,
  profile, base, scope, recursive-body, and internal-factorization negative
  partition;
- add one immutable `displayed-mixed-telescope` reviewer preset using the same
  browser-safe adapter and checker; and
- synchronize only the syntax, reviewer, handoff, and current product-route
  ledgers.

## Required Invariants

The implementation must:

- use semicolon/comma grouping only as a checked presentation of the two
  existing direct shapes;
- pass only ordered name/family pairs to the direct program, never unchecked
  dependency flags;
- delegate profile availability, exact two/four-binding arity, family-base
  dependency derivation, target base, active-slot scope, body
  factorization, and internal categorical coherence to the existing typed
  program;
- infer omitted annotations only from immutable expected-family groups;
- never synthesize a dependent family, decompose private Core provenance, or
  guess a family presentation;
- preserve callback-once construction, callback-local token hygiene, and
  exact source spans;
- retain existing Sigma, pullback, product, pairing, reindexing, and
  internalized-cell ownership;
- accept no external equality, naturality, functoriality, or coherence
  premise;
- add no second resolver, dependency planner, action table, checker,
  evaluator, Core, or browser semantics; and
- fail closed for every context shape or body outside the reviewed direct
  envelope.

## Explicit Non-Authorization

This decision authorizes no:

- arbitrary-depth telescope, arbitrary sibling/dependency graph, three-
  binding shape, nested abstraction, or general dependent-family expression;
- unchecked dependency flag, heuristic family inference, or
  pointwise-to-coherent promotion;
- `SYNTAX-PARITY-1C` constructor route or syntax graduation;
- new mathematical owner, dependency planner, categorical-program method,
  contextual factorization case, Core node, checker/evaluator branch,
  runtime/proof/unification rule, semantic profile, transfer input, or
  Lambdapi declaration/rule;
- external naturality/coherence evidence;
- parser dependency, exported raw-syntax type theory, second elaborator, or
  alternate browser implementation;
- book prose/artifact, README, scale, deployment, publication, release, or
  repository-wide notation migration; or
- push, merge, PR, rebase, amend, reset, history rewrite, cleanup, branch
  deletion, or worktree removal.

## Validation And Git Boundary

The implementation must pass:

- annotated and annotation-free text/direct equality for the `[1,1]` and
  `[1,2,1]` shapes;
- the complete new dependent-group parsing/resolution/negative corpus;
- existing categorical text, syntax-parity, displayed-chain/chain-2A, and
  browser-reviewer tests;
- root and browser-fixture typecheck, root lint, and production build;
- a real Chromium exercise of the new mixed-telescope preset;
- a proportional aggregate regression gate without duplicating unchanged
  Lambdapi checks when no owner or transfer input changes; and
- exact staged review plus `git diff --cached --check`.

It may then receive one bounded local implementation checkpoint and one
separate synchronized-ledger checkpoint under the existing Git authority.
