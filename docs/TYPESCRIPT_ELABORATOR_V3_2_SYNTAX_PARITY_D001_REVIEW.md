# D-DTTLF-PRODUCT-SYNTAX-PARITY-001 — Modes-First Parity Review

Date: 2026-07-30
Gate: H-DTTLF-PRODUCT-SYNTAX-PARITY-01
Decision: D-DTTLF-PRODUCT-SYNTAX-PARITY-001
Status: approved as proposed under the user's standing unattended delegation
Human-Supersession: any later explicit human decision supersedes this record
Reviewed-Proposal-Checkpoint:
`d73195b833d5afcb569898df110f392344d2deac`
(`docs(v3.2): freeze syntax parity audit`)

## Review

No immediate human objection followed presentation and checkpointing of the
bounded `SYNTAX-PARITY-1A` proposal in
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md).
The user's standing delegation therefore approves that exact proposal with
human supersession.

The approved implementation may only:

- enable the already lexically accepted intrinsic binder modes `^n`, `^fd`,
  and `^nd`;
- add a `displayed-family` text-environment binding kind;
- add expected result contracts for `dependent-section`,
  `displayed-functor`, and `displayed-transfor`;
- route those modes respectively to the existing
  `CoreCategoricalProgram.dependentLambda`,
  `displayedFunctorLambda`, and `displayedTransforLambda` methods;
- retain `CoreCategoricalProgram.apply` as the only
  classifier-directed application ladder;
- recognize the exact binary application spine
  `composeCells left right` and route it to the existing `composeCells`
  method;
- accept only the direct implementation's existing finite body
  factorization envelopes:
  - section eta and indexed-section composition for `^n`;
  - identity, eta, finite nested application composition, and qualified
    weakening/reindexing for `^fd`; and
  - component eta and finite recursive `composeCells` for `^nd`;
- add focused text/direct-TypeScript equivalence and source-located negative
  evidence for those routes;
- expose the same adapter through the existing browser reviewer, with no
  browser semantic fork; and
- synchronize the syntax, reviewer, handoff, and scale/product ledgers.

The exact positive source witnesses are:

```text
λ^n  k : K. (FF k) (s k)
λ^fd a : E. GG (FF a)
λ^nd k : K. composeCells (theta k) (eta k)
```

## Required Invariants

The implementation must:

- elaborate text into the same checked categorical terms and explicit Core as
  the corresponding direct TypeScript constructions;
- preserve intrinsic binder mode separately from the optional source/family
  annotation;
- use immutable scoped tokens rather than names as semantic variables;
- preserve the existing program profiles and exact classifier/family/
  endpoint rejections;
- reject nested or multi-binder forms in this tranche rather than silently
  broadening into `SYNTAX-PARITY-1B`;
- reject pointwise data that the existing direct factorers cannot promote to
  a genuine outer functor/transformation;
- accept no external naturality, functoriality, or coherence equation;
- preserve one backend-neutral Core, checker, evaluator, contextual
  compiler, and application classifier; and
- keep Node and browser behavior on the same text adapter.

## Explicit Non-Authorization

This decision authorizes no:

- new Lambdapi declaration/rule, mathematical owner, semantic profile, Core
  node, checker/evaluator branch, runtime rule, proof rule, unification rule,
  or intrinsic;
- second raw-expression AST, parser, resolver, checker, evaluator, or
  categorical action table;
- heuristic application selection, theorem search, arbitrary naturality
  synthesis, or pointwise-to-coherent promotion;
- nested binder, dependent telescope, grouped-context, independent sibling,
  structural-constructor, general `SYNTAX-PARITY-1B`/`1C`, or arbitrary-depth
  syntax implementation;
- parser dependency, lockfile change, Lambdapi-source parser, production
  Lambdapi process, or Node-only browser dependency;
- book prose/artifact mutation, README graduation, deployment, publication,
  release, bulk scale qualification, or whole-library transfer claim; or
- push, merge, PR, rebase, amend, reset, history rewrite, cleanup, branch
  deletion, or worktree removal.

## Validation And Git Boundary

The implementation must pass:

- focused syntax-parity and existing categorical-text tests;
- focused direct semantic witnesses and exact negative-span tests;
- browser-reviewer unit and production-build checks;
- root typecheck and lint;
- the aggregate TypeScript suite, with any pre-existing baseline discrepancy
  classified rather than hidden;
- proportional live Lambdapi conformance only where the existing target
  owners are re-observed; and
- exact staged review plus `git diff --cached --check`.

It may then receive one bounded local implementation checkpoint and one
separate synchronized-ledger checkpoint under the existing Git authority.
This review is a decision record only; it does not itself implement
`SYNTAX-PARITY-1A`.
