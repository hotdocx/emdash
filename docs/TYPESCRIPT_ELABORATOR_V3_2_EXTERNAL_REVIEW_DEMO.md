# Emdash v3.2 TypeScript External-Review Demo

Date: 2026-07-29
Candidate: `emdash-v3.2-product-capability-2`
Inputs: direct typed TypeScript plus bounded ordinary categorical text
Production Lambdapi dependency: none
Runtime checkpoint:
`7513cbe9e0d1439b5b1250982f40cede48e9a811`

## What This Demonstrates

The TypeScript implementation currently exposes three complementary runnable
capability ingredients over one checker/evaluator architecture:

1. a curated direct-TypeScript report across:
   - an outer dependent logical framework with lambda, Pi, dependent
     Sigma-telescope data, type inference/checking, beta reduction, and
     source-located rejection;
   - ordinary categorical variables and binders whose recursive occurrences
     compile into identity, composition, pairing/evaluation, diagonal, and
     exchange structure; and
   - displayed categorical binders over one genuine dependency edge,
     including object behavior, internalized-arrow behavior, reindexing,
     recursive subexpressions, and a wrong-base diagnostic;
2. an editable ordinary categorical text adapter with recursive whitespace
   application, intrinsic `λ^f`, optional checked source annotation, exact
   source spans, and type-directed whole-Hom action; and
3. a fully client-side browser fixture containing the directed dependent-LF
   witness plus the preserved editable minimal-Core playground.

Direct construction and parsed ordinary text both elaborate to backend-neutral
explicit emdash Core and run through the existing generic LF checker,
evaluator, rewrite machinery, and categorical program. The text adapter owns
no second action table or checker. None of these product lanes spawns
Lambdapi.

These commands are not the final intended reviewer UX. The user's later
clarification requires one browser workbench that joins this exact
three-panel report, editable categorical text, the generated emdash book, and
the minimal implementation evidence. The completed combined Vite/Chromium
audit and frozen implementation proposal are in
[`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md).
Until that separately reviewed slice lands, this document is the
self-contained terminal/capability handoff rather than a claim that the
reviewer journey is already integrated.

## Runnable Product Matrix

| Command | Input and result | Exact boundary |
| --- | --- | --- |
| `./scripts/pnpmw run demo:external-review` | Fixed direct-TypeScript outer LF, ordinary categorical, and genuine displayed-chain report | Most complete semantic demonstration; not editable text |
| `./scripts/pnpmw run demo:categorical-text` | Editable strings such as `λ^f x. (H x) (K x)` checked into explicit Core | Ordinary `^f` only; no displayed/dependent text telescope |
| `./scripts/pnpmw run check:browser-directed` | Strict build/tests for the client-side dependent-LF view and minimal-Core playground | Browser contains neither categorical continuation nor categorical text |
| `./scripts/pnpmw run demo:categorical-displayed-nd-higher` | Optional direct-TypeScript object, whole-Hom, and higher-cell action | Advanced bounded witness; not a general `^nd` text binder |

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

## Run The Categorical Text Lane

The additive ordinary categorical adapter accepts text plus an immutable
typed environment and an explicit expected classifier:

```bash
./scripts/pnpmw run demo:categorical-text
```

The executable example checks:

```text
λ^f x. (H x) (K x)
λ^f x : A. F x y0
G p
```

The first form obtains its source category from the expected functor
classifier. The second resolves `A` and compares it with that expected source.
Both lower through the same existing `CoreCategoricalProgram.lambda` and
`apply` path as direct TypeScript and print equality with the direct
construction. `G p` demonstrates that neutral whitespace application can use
an expected whole-Hom action rather than being hard-wired to object action.

The adapter recognizes intrinsic `^n`, `^fd`, and `^nd` mode tokens but rejects
them before semantic construction. Their existing direct typed TypeScript
consumers do not yet have text-resolver contracts.

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
λ^f x. (H x) (K x)
λ^f x : A. F x y0
```

These are executable SYNTAX-1A text forms. The corresponding direct
TypeScript construction uses `CoreCategoricalProgram.lambda` and `apply`.
Variable occurrences are compiled recursively; the resulting Core uses the
reviewed categorical identity/composition/product/evaluation and diagonal
basis. The direct API supports a wider envelope, including nested contexts
and exchange, than this first one-root-lambda text profile.

### Displayed dependent binding through direct TypeScript

```ts
emdash.displayedDependentContextLambda(
  [
    { name: "a", family: A },
    { name: "b", family: B }
  ],
  liftedD,
  ([a]) => emdash.apply(liftedFF, a)
)
```

The second family is based on `Sigma(A)`, so this is a real dependency edge
rather than two independent displayed variables. The compiler observes
bound-variable occurrences below the recursive `apply(liftedFF, a)`
subexpression and lowers them through the existing displayed structure.

Earlier plans and kernel-development comments often summarize this family of
direct constructions with informal notation such as
`λ a :^fd A. λ b :^fd B(a). FF[a]`. That remains historical mathematical
shorthand, not accepted text input. The experimental TypeScript text design
now separates intrinsic `λ^mode` from optional `: annotation`, but final
cross-environment notation is intentionally unsettled.

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

The text-lane source is
[`examples/v3_2_categorical_text_demo.ts`](../examples/v3_2_categorical_text_demo.ts),
with its adapter in
[`src/v3_2/categorical_text.ts`](../src/v3_2/categorical_text.ts).

## Build The Client-Side Browser Lane

The selected browser fixture has a fixed directed dependent-LF view and the
preserved editable minimal-Core JavaScript playground:

```bash
./scripts/pnpmw run check:browser-directed
```

The command runs the fixture's strict TypeScript checks and Vite production
build. Its relative assets are compatible with a static project subpath such
as `https://hotdocx.github.io/emdash/`; no Pages workflow, deployment, or
publication has been added.

The browser entry is additive and does not modify the frozen minimal
`src/v3_2/browser.ts` API. It does not currently expose
`CoreCategoricalProgram`, the categorical text adapter, or the displayed
continuation. Categorical browser promotion remains behind the separately
deferred BROWSER-CATEGORICAL-0A runtime/acquisition-boundary refactor and a
later exact review.

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

Current selected product evidence:

- external-review report:
  `f1cb532a88ccca84786aa1cd5ee7cb006b1ad5fc`;
- additive directed browser:
  `7f696cea4b6a369e5db41c0d5e57e778b61fa10c`;
- ordinary categorical text adapter:
  `7513cbe9e0d1439b5b1250982f40cede48e9a811`; and
- latest aggregate after the text slice: 1,127 tests, 1,076 active passes,
  51 intentional skips, zero failures.

## Exact Boundary

This candidate demonstrates:

- outer dependent lambda/Pi and the selected dependent Sigma-telescope
  computation;
- recursively usable ordinary functorial variables/binders;
- direct bounded displayed functor/transfor consumers;
- independent displayed siblings and one genuine displayed dependency edge;
- structural weakening/reindexing, pairing, diagonal/swap composites, and
  checked object/internalized-arrow observations; and
- bounded ordinary categorical text with recursive whitespace application,
  optional checked source annotation, exact diagnostics, and whole-Hom
  expected routing;
- a client-side directed dependent-LF view and editable minimal-Core
  playground; and
- backend-neutral Core plus generic TypeScript checking/evaluation.

It does not yet claim:

- arbitrary displayed telescope depth;
- a general `^nd` binder/coherence theorem;
- text lowering for `^n`, `^fd`, `^nd`, displayed/dependent telescopes,
  nested lambdas, outer-LF terms, Pi, let, or holes;
- final agreement between experimental TypeScript `λ^mode` syntax and
  informal Lambdapi/kernel notation;
- browser promotion of the categorical continuation;
- a GitHub Pages workflow, deployment, or publication;
- systematic groupoidal-DTT closure;
- complete transfer of the Lambdapi library;
- unrestricted normalization, confluence, or standalone subject reduction;
  or
- a performance or release SLA.

The selected text and historical directed-browser rows are recorded in
[`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md)
and
[`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md).
The historical Parsimmon parser remains baseline grammar evidence; the
implemented adapter is dependency-free. The immediate product continuation
routes through the integrated reviewer plan; scale remains the top-level
architecture ledger, and one exact scale dependency may move earlier only
when a compelling reviewer witness measurably requires it.
