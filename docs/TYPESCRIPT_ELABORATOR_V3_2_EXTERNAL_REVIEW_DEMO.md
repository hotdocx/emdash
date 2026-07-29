# Emdash v3.2 TypeScript External-Review Demo

Date: 2026-07-29
Candidate: `emdash-v3.2-external-review-1`
Input: direct typed TypeScript
Production Lambdapi dependency: none

## What This Demonstrates

The TypeScript implementation can currently execute one coherent path across
three layers:

1. an outer dependent logical framework with lambda, Pi, dependent
   Sigma-telescope data, type inference/checking, beta reduction, and
   source-located rejection;
2. ordinary categorical variables and binders whose recursive occurrences
   compile into identity, composition, pairing/evaluation, diagonal, and
   exchange structure; and
3. displayed categorical binders over one genuine dependency edge, including
   object behavior, internalized-arrow behavior, reindexing, recursive
   subexpressions, and a wrong-base diagnostic.

All three inputs are ordinary TypeScript expressions using the scoped builder
or `CoreCategoricalProgram` facade. They elaborate to backend-neutral explicit
emdash Core and run through the existing generic LF checker, evaluator, and
rewrite machinery. The demo does not spawn Lambdapi.

## Run The Curated Report

From the repository root:

```bash
./scripts/pnpmw run demo:external-review
```

On a fresh worktree, bootstrap first:

```bash
./scripts/bootstrap-worktree.sh
```

Node 22.13 or newer is required. Lambdapi is not required for the demo
command.

One local cold CLI observation took 68.59 seconds. The same three-panel
execution took 2.1 seconds inside the warmed aggregate test process. These
figures are orientation only, not a performance SLA; TypeScript startup and
module caching materially affect them.

The report prints:

- the direct TypeScript input for the outer dependent witness;
- one explicit locally nameless Core term;
- inferred and reduced dependent types;
- a beta/kernel computation trace;
- the ordinary functorial bracket and its generated structural basis;
- diagonal and exchange witnesses;
- a displayed telescope
  `k : K; a : A[k]; b : B[(k,a)]`;
- three displayed binder bodies, including recursive `FF[a]`;
- checked object, internalized-arrow, noncollapse, and reindexing results;
- wrong-family, wrong-category, and wrong-base diagnostics; and
- the exact product and deferral boundary.

The command executes real structured demo results. The formatter does not
maintain a separate mock semantic transcript.

## Readable Input Examples

### Outer dependent LF

```ts
builder.apply(
  builder.lam("section", sectionType, section =>
    piapp0(sigmaBase, telescopeFamily, section, pair)),
  s
)
```

This checks and computes the application of a section over a dependent Sigma
telescope at a dependent pair.

### Ordinary functorial binding

```text
λ x :^f A. (H x) (K x)
λ x :^f A. (D x) x
λ x :^f A. λ y :^f B. (E y) x
```

The direct TypeScript construction uses `CoreCategoricalProgram.lambda` and
`apply`. Variable occurrences are compiled recursively; the resulting Core
uses the reviewed categorical identity/composition/product/evaluation,
diagonal, and exchange basis.

### Displayed dependent binding

```text
λ a :^fd A. λ b :^fd B(a). a
λ a :^fd A. λ b :^fd B(a). b
λ a :^fd A. λ b :^fd B(a). FF[a]
```

The direct TypeScript construction uses
`displayedDependentContextLambda`. The second family is based on
`Sigma(A)`, so this is a real dependency edge rather than two independent
displayed variables. The compiler observes bound-variable occurrences below
the recursive `apply(FF, a)` subexpression and lowers them through the
existing displayed structure.

## Full Component Reports

The curated output is intentionally shorter than the component reports. Run
these to inspect every retained Core serialization and rule identifier:

```bash
./scripts/pnpmw run demo:directed-dependent
./scripts/pnpmw run demo:categorical-bracket
./scripts/pnpmw run demo:categorical-displayed-chain
```

The direct source entry points are:

- [`examples/v3_2_directed_dependent_demo.ts`](../examples/v3_2_directed_dependent_demo.ts);
- [`examples/v3_2_categorical_bracket_demo.ts`](../examples/v3_2_categorical_bracket_demo.ts); and
- [`examples/v3_2_categorical_displayed_chain_demo.ts`](../examples/v3_2_categorical_displayed_chain_demo.ts).

## Optional Advanced Higher-Action Witness

The existing next-hom action demo is useful but has a more variable
TypeScript cold-start cost, so it is not part of the default report:

```bash
./scripts/pnpmw run demo:categorical-displayed-nd-higher
```

It constructs an internal Hom action for displayed transfors, evaluates it
on a displayed transfor, evaluates the whole Hom action between two
transfors, and applies that action to a higher cell `m`.

## Validation And Formal Oracle

The TypeScript-only repository gate is:

```bash
./scripts/pnpmw run check:ts
```

The frozen MVP and directed-continuation conformance lanes use Lambdapi as an
external bounded oracle:

```bash
./scripts/pnpmw run check:conformance
./scripts/pnpmw run check:directed-conformance
```

The active Lambdapi kernel itself can be checked under the repository's
60-second exploratory bound with:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
```

These are validation/development commands. The external-review demo and the
TypeScript runtime do not invoke Lambdapi in production.

## Exact Boundary

This candidate demonstrates:

- outer dependent lambda/Pi and the selected dependent Sigma-telescope
  computation;
- recursively usable ordinary functorial variables/binders;
- direct bounded displayed functor/transfor consumers;
- independent displayed siblings and one genuine displayed dependency edge;
- structural weakening/reindexing, pairing, diagonal/swap composites, and
  checked object/internalized-arrow observations; and
- backend-neutral Core plus generic TypeScript checking/evaluation.

It does not yet claim:

- arbitrary displayed telescope depth;
- a general `:^nd` binder/coherence theorem;
- silent string-syntax application resolution;
- browser promotion of the categorical continuation;
- systematic groupoidal-DTT closure;
- complete transfer of the Lambdapi library;
- unrestricted normalization, confluence, or standalone subject reduction;
  or
- a performance or release SLA.

User-facing string syntax and browser exposure are separate measured rows in
[`TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md).
The historical Parsimmon parser is baseline grammar evidence for that audit,
not a dependency of this demo.
