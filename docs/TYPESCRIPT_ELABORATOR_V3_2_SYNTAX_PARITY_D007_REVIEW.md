# D-DTTLF-PRODUCT-SYNTAX-PARITY-007 — Internal Action Review

Date: 2026-07-30
Gate: H-DTTLF-PRODUCT-SYNTAX-PARITY-07
Decision: D-DTTLF-PRODUCT-SYNTAX-PARITY-007
Status: approved as proposed under the user's standing unattended delegation
Human-Supersession: any later explicit human decision supersedes this record
Reviewed-Proposal-Checkpoint:
`d8bb9d0408e0a0d8346dd2bcc75bfae2d1ef44b9`
(`docs(v3.2): freeze internal action syntax slice`)
Proposal-Ledger-Checkpoint:
`71e27feaa9969de671987454147833dcc56965d5`
(`docs(v3.2): record internal action audit checkpoint`)

## Review

No immediate human objection followed presentation and local checkpointing of
the bounded `SYNTAX-PARITY-1C2B` proposal in
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md).
The user's standing unattended delegation therefore approves that exact
proposal with human supersession.

The selected first-class terms are:

```text
fullAction FF x y
cell FF p u
naturality eta p u
internalHomAction FF GG
```

Their existing direct methods compile respectively as
`functor, hom, hom, functor`. The audit also proves the required distinctions:

- `FF p u` remains an object-level transported application, not the
  internalized Hom `cell FF p u`;
- `eta x` and `eta x u` remain generic component and point application;
- `eta p u` remains rejected as generic component application;
- `naturality eta p u` constructs the existing transported internal cell;
  and
- application after `fullAction` or `internalHomAction` remains generic
  `apply`.

## Exact Authorization

The implementation may only:

- retain the existing private located expression node kinds and parser
  grammar;
- recognize the four exact fixed-arity reserved application spines above;
- resolve every operand recursively through the existing term resolver;
- call the existing `displayedFunctorFullAction`,
  `displayedFunctorInternalCell`, `displayedTransforNaturality`, and
  `displayedTransforInternalHomAction` methods;
- preserve `CoreCategoricalProgram.apply` as the only subsequent application
  route and preserve its existing expected-shape contract;
- prove text/direct equality for backend-neutral explicit Core and rich
  inferred categorical classifiers;
- preserve exact arity, classifier, foreign-value, base/fibre, endpoint, and
  profile negatives; and
- synchronize only the syntax, handoff, and current product-route ledgers.

## Required Invariants

The implementation must:

- treat each head as presentation syntax for an existing typed first-class
  term, not as a new owner or evaluator action;
- delegate every classifier, endpoint, scope, profile, and internal coherence
  judgment to the direct program;
- preserve recursive term resolution and exact source spans;
- retain `FF p u`, `eta x`, `eta x u`, and `eta p u` at their measured
  distinct boundaries;
- avoid an action table, duplicated checker, fabricated Hom boundary, or
  external naturality/functoriality evidence; and
- fail closed outside the four-operation envelope.

## Explicit Non-Authorization

This decision authorizes no:

- alias for `displayedTransforComponent` or
  `displayedTransforPoint`;
- category or displayed-family result syntax from `SYNTAX-PARITY-1C3`;
- general dependent-family expression or arbitrary-depth context syntax;
- new mathematical owner, categorical-program method, Core node,
  checker/evaluator branch, runtime/proof/unification rule, semantic profile,
  transfer input, or Lambdapi declaration/rule;
- expected-action table, parser dependency, raw-syntax layer, second
  resolver/checker, or alternate browser implementation;
- browser preset, book prose/artifact, README, scale row, deployment,
  publication, release, or repository-wide notation migration; or
- push, merge, PR, rebase, amend, reset, history rewrite, cleanup, branch
  deletion, or worktree removal.

## Validation And Git Boundary

The implementation must pass:

- exact direct/text equality for all four selected terms;
- recursive generic continuations for the full and internal-Hom actions;
- complete arity/classifier/foreign/base/fibre/endpoint/profile negatives;
- retained component, point, object-application, and rejected generic
  naturality boundaries;
- existing categorical-text and syntax-parity regression corpora;
- root typecheck and lint;
- proportional browser checks only if shared browser code changes; and
- exact staged review plus `git diff --cached --check`.

It may then receive one bounded local implementation checkpoint and one
separate synchronized-ledger checkpoint under the existing Git authority.
