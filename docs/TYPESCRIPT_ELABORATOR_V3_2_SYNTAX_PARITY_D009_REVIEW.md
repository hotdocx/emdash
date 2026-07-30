# D-DTTLF-PRODUCT-SYNTAX-PARITY-009 — Nested Ordinary Review

Date: 2026-07-30
Gate: H-DTTLF-PRODUCT-SYNTAX-PARITY-09
Decision: D-DTTLF-PRODUCT-SYNTAX-PARITY-009
Status: approved as proposed under the user's standing unattended delegation
Human-Supersession: any later explicit human decision supersedes this record
Reviewed-Proposal-Checkpoint:
`8d5671e5062910d9a1b52727db469fc582c9669c`
(`docs(v3.2): audit syntax graduation boundary`)

## Review

No immediate human objection followed presentation and checkpointing of the
bounded `SYNTAX-PARITY-1D1` correction proposal in
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md).
The user's standing unattended delegation therefore approves that exact
proposal with human supersession.

The audit proves that direct TypeScript already constructs the reviewed
exchange/currying term

```text
λ^f x : A. λ^f y : B. E y x
```

while text rejects the inner lambda with
`UNSUPPORTED_NESTED_ABSTRACTION`. This is the sole selected direct-green
parser gap before syntax graduation.

## Exact Authorization

The implementation may only:

- add an optional recursive `bodyExpected` field to the ordinary-functor
  expected contract;
- use that field only when an ordinary lambda body is another lambda;
- dispatch that body through the existing root-lambda resolver;
- let the existing outer `CoreCategoricalProgram.lambda` validate the inner
  functor classifier against the outer target category;
- support finite ordinary nesting only to the depth explicitly supplied by
  the checked expected tree; and
- prove direct/text equality for the exchange witness and exact failures for
  missing/stale expectations, wrong modes/annotations/targets, foreign
  values, scope escape, and unsupported bodies.

## Required Invariants

The text layer must not inspect or decompose category expressions, infer a
hidden nested classifier, guess an action, or add a second checker. Existing
non-nested callers and exact source spans must remain unchanged. A nested
lambda without the recursive expected contract must continue to fail closed.

## Explicit Non-Authorization

This decision authorizes no new token, located node, grammar production,
parser dependency, nested `^n`, `^fd`, or `^nd` guarantee, arbitrary
displayed context, pointwise coherence synthesis, mathematical owner,
categorical-program method, Core/checker/evaluator/runtime/proof rule,
Lambdapi input, browser preset, book, scale row, publication, or wider Git
mutation.

## Proportional Validation

The implementation must pass focused nested-ordinary and graduation-audit
tests, affected lightweight text regressions, TypeScript typecheck and lint,
and exact staged review. Aggregate and browser reruns are required only if
their specific boundary changes or the later graduation gate requires them.
