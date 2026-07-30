# D-DTTLF-PRODUCT-SYNTAX-PARITY-002 — Contextual Index Review

Date: 2026-07-30
Gate: H-DTTLF-PRODUCT-SYNTAX-PARITY-02
Decision: D-DTTLF-PRODUCT-SYNTAX-PARITY-002
Status: approved as proposed under the user's standing unattended delegation
Human-Supersession: any later explicit human decision supersedes this record
Reviewed-Proposal-Checkpoint:
`be7000f88b08c90d24bad8a1e113fe3241d8a8ca`
(`docs(v3.2): freeze structural text parity audit`)
Proposal-Ledger-Checkpoint:
`afae6a53799849594c292be469b7ead9494bacb1`
(`docs(v3.2): record structural parity proposal`)

## Review

No immediate human objection followed presentation of the bounded,
checkpointed `SYNTAX-PARITY-1B1` proposal in
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md).
The user's standing unattended delegation therefore approves that exact
proposal with human supersession.

The measured source is:

```text
λ^fd a : E. s (indexOf a)
```

Direct TypeScript already checks this term through
`displayedFunctorLambda`, `apply`, and `indexOf`, selecting the existing
`categorical.displayed-functor-weakening` factorization. Current text fails
only with `UNKNOWN_IDENTIFIER` at the `indexOf` head.

## Exact Authorization

The implementation may only:

- retain the current identifier/application/lambda located tree;
- factor the existing exact application-spine recognizer into a
  fixed-arity helper shared by `composeCells` and `indexOf`;
- recognize the reserved unary application spine `indexOf argument`;
- resolve its argument recursively through the existing text environment;
- call the existing `CoreCategoricalProgram.indexOf` method;
- retain `CoreCategoricalProgram.apply` as the only ordinary categorical
  application path;
- prove text/direct equality for explicit Core, inferred/expected type,
  factorization rule, and internal owner observations;
- preserve exact profile, scope, arity, foreign/closed-term, and
  source/target-family failures;
- add one immutable `displayed-functor-weakening` reviewer preset using the
  same browser-safe adapter and checker; and
- synchronize only the syntax, reviewer, handoff, and product-route ledgers.

## Required Invariants

The implementation must:

- delegate active displayed-slot and profile validation to the existing typed
  categorical program rather than reproducing those semantics in text;
- treat `indexOf` as a reserved operation head only in its exact unary
  application spine;
- preserve immutable callback-local tokens and exact source spans;
- retain the existing `^fd` expected-family contract and factorer;
- accept no external equality, naturality, functoriality, or coherence
  premise;
- add no second resolver, action table, checker, evaluator, Core, or browser
  semantics; and
- fail closed for every shape not selected by this review.

## Explicit Non-Authorization

This decision authorizes no:

- new parser node, general call syntax, term declaration syntax, or parser
  dependency;
- new mathematical owner, categorical-program method, Core node,
  checker/evaluator branch, runtime/proof/unification rule, semantic profile,
  or Lambdapi declaration/rule;
- `fibrePair`, independent sibling binder, grouped context, dependent/mixed
  telescope, nested lambda, multi-binder, or arbitrary-depth syntax;
- remaining `SYNTAX-PARITY-1B2`, `1B3`, or `1C` constructor routes;
- external naturality/coherence evidence or pointwise-to-coherent
  promotion;
- book prose/artifact, README, scale, deployment, publication, release, or
  notation-migration change; or
- push, merge, PR, rebase, amend, reset, history rewrite, cleanup, branch
  deletion, or worktree removal.

## Validation And Git Boundary

The implementation must pass:

- the new structural text/direct equality and exact negative corpus;
- existing syntax-parity and categorical-text tests;
- browser-reviewer unit and production-build checks;
- root typecheck and lint;
- a proportional aggregate regression gate, without duplicating unchanged
  Lambdapi checks when no owner or transfer input changed; and
- exact staged review plus `git diff --cached --check`.

It may then receive one bounded local implementation checkpoint and one
separate synchronized-ledger checkpoint under the existing Git authority.
