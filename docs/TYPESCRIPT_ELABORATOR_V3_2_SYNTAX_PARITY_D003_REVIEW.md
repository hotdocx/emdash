# D-DTTLF-PRODUCT-SYNTAX-PARITY-003 — Independent Sibling Review

Date: 2026-07-30
Gate: H-DTTLF-PRODUCT-SYNTAX-PARITY-03
Decision: D-DTTLF-PRODUCT-SYNTAX-PARITY-003
Status: approved as proposed under the user's standing unattended delegation
Human-Supersession: any later explicit human decision supersedes this record
Reviewed-Proposal-Checkpoint:
`f53fd6885dd2fac0345bad5db257c7a66f86af15`
(`docs(v3.2): freeze sibling text parity proposal`)
Corrected-Proposal-Ledger-Checkpoint:
`e2becf20ddb7af8981c8f0979d74887b5e9651bc`
(`docs(v3.2): correct sibling proposal checkpoint identity`)

## Review

No immediate human objection followed presentation and local checkpointing of
the bounded `SYNTAX-PARITY-1B2` proposal in
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md).
The user's standing unattended delegation therefore approves that exact
proposal with human supersession.

The selected source is:

```text
λ^fd (b : B, c : C). fibrePair (FF b) (GG c)
```

The annotation-free form is also in scope when the expected contract supplies
the ordered source families:

```text
λ^fd (b, c). fibrePair (FF b) (GG c).
```

Direct TypeScript already checks this construction through
`displayedContextLambda`, `fibrePair`, and the sole existing `apply` ladder.
The parser currently fails only at the opening parenthesis after `λ^fd`.

## Exact Authorization

The implementation may only:

- retain the three private located expression node kinds while generalizing
  the private lambda payload to immutable ordered binding groups;
- represent every existing unary binder as one singleton group;
- parse one parenthesized comma-separated group containing at least two
  portable binding names with independently optional identifier annotations;
- add one `displayed-context-functor` expected contract containing the ordered
  source families and one target family;
- require exact binding/family cardinality and check every present annotation
  positionally against its expected family;
- call the existing `CoreCategoricalProgram.displayedContextLambda` exactly
  once, extend one immutable environment with all returned sibling tokens,
  and resolve the body recursively;
- recognize the exact binary `fibrePair left right` application spine and call
  the existing `CoreCategoricalProgram.fibrePair`;
- retain `CoreCategoricalProgram.apply` as the only generic categorical
  application path;
- prove text/direct equality for explicit Core, inferred/expected classifier,
  abstraction trace, binding order, and applicable object/internalized-arrow
  observations;
- preserve the complete parsing, expectation, annotation, count, base,
  profile, scope, pair-branch, and body-factorization negative partition;
- add one immutable `displayed-sibling-pairing` reviewer preset using the same
  browser-safe adapter and checker; and
- synchronize only the syntax, reviewer, handoff, and current product-route
  ledgers.

## Required Invariants

The implementation must:

- interpret commas as siblings at one dependency level;
- keep semicolons rejected and reserved for separately reviewed
  `SYNTAX-PARITY-1B3`;
- delegate common-base, target-base, dependency-plan, active-slot,
  branch-family, and recursive-factorization checks to the existing typed
  categorical program;
- avoid decomposing private Core/product provenance or guessing source
  families;
- preserve immutable callback-local tokens, exact source spans, and
  callback-once construction;
- retain the existing internal displayed product/projection/pairing owners and
  their object, arrow, and higher action;
- accept no external equality, naturality, functoriality, or coherence
  premise;
- add no second resolver, action table, checker, evaluator, Core, or browser
  semantics; and
- fail closed for every shape not selected by this review.

## Explicit Non-Authorization

This decision authorizes no:

- semicolon-separated dependency levels, genuine dependent/mixed telescope,
  nested abstraction, arbitrary depth, or `SYNTAX-PARITY-1B3` implementation;
- `SYNTAX-PARITY-1C` constructor route or syntax graduation;
- new `Product_catd` head, mathematical owner, categorical-program method,
  contextual factorization case, Core node, checker/evaluator branch,
  runtime/proof/unification rule, semantic profile, or Lambdapi
  declaration/rule;
- external naturality/coherence evidence or pointwise-to-coherent promotion;
- parser dependency, exported raw-syntax type theory, second elaborator, or
  alternate browser implementation;
- book prose/artifact, README, scale, deployment, publication, release, or
  repository-wide notation-migration change; or
- push, merge, PR, rebase, amend, reset, history rewrite, cleanup, branch
  deletion, or worktree removal.

## Validation And Git Boundary

The implementation must pass:

- exact annotated and annotation-free text/direct equality;
- the complete new sibling parsing/resolution/negative corpus;
- existing categorical text, syntax-parity, displayed-bracket, and
  browser-reviewer tests;
- root and browser-fixture typecheck, root lint, and production build;
- a real Chromium exercise of the new preset;
- a proportional aggregate regression gate without duplicating unchanged
  Lambdapi checks when no owner or transfer input changes; and
- exact staged review plus `git diff --cached --check`.

It may then receive one bounded local implementation checkpoint and one
separate synchronized-ledger checkpoint under the existing Git authority.
