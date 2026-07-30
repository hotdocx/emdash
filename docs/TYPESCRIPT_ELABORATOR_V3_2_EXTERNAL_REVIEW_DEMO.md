# Emdash v3.2 TypeScript External-Review Demo

Date: 2026-07-30
Candidate: `emdash-v3.2-integrated-reviewer-1`
Inputs: direct typed TypeScript plus bounded categorical text
Production Lambdapi dependency: none
Component runtime checkpoint:
`7513cbe9e0d1439b5b1250982f40cede48e9a811`
Integrated implementation: green in the current reviewed tranche

## What This Demonstrates

The TypeScript implementation now exposes one integrated external-reviewer
workbench over the existing checker/evaluator architecture:

1. an editable categorical expression view with six presets:
   - recursive pointwise application `λ^f x. (H x) (K x)`;
   - fixed-inner evaluation `λ^f x. F x y0`; and
   - expected-type-directed whole-Hom action `G pA`;
   - natural indexed composition `λ^n k : K. (FF k) (s k)`;
   - displayed functor composition `λ^fd a : E. GG (FF a)`; and
   - coherent displayed component composition
     `λ^nd k : K. composeCells (theta k) (eta k)`;
2. an explicitly started direct-TypeScript report across:
   - an outer dependent logical framework with lambda, Pi, dependent
     Sigma-telescope data, type inference/checking, beta reduction, and
     source-located rejection;
   - ordinary categorical variables and binders whose recursive occurrences
     compile into identity, composition, pairing/evaluation, diagonal, and
     exchange structure; and
   - displayed categorical binders over one genuine dependency edge,
     including object behavior, internalized-arrow behavior, reindexing,
     recursive subexpressions, and a wrong-base diagnostic;
3. the generated current [`emdash-book.pdf`](./emdash-book.pdf), emitted by
   Vite as a fingerprinted static asset; and
4. the preserved editable minimal-Core playground.

Direct construction and parsed categorical text both elaborate to backend-neutral
explicit emdash Core and run through the existing generic LF checker,
evaluator, rewrite machinery, and categorical program. The text adapter owns
no second action table or checker. None of these product lanes spawns
Lambdapi. The categorical/report closure is loaded as a separate browser
chunk, and the full report does not execute until the reviewer selects its
explicit action.

The completed combined Vite/Chromium audit, decision, implementation record,
and exact boundary are in
[`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md).

## Runnable Product Matrix

| Command | Input and result | Exact boundary |
| --- | --- | --- |
| `./scripts/pnpmw run check:browser-reviewer` | Typechecks, lints, and builds the integrated static workbench | Primary reviewer product; deployment remains separate |
| `./scripts/pnpmw run demo:external-review` | Fixed direct-TypeScript outer LF, ordinary categorical, and genuine displayed-chain report | Most complete semantic demonstration; not editable text |
| `./scripts/pnpmw run demo:categorical-text` | The original ordinary CLI examples such as `λ^f x. (H x) (K x)` checked into explicit Core | The integrated browser additionally exposes reviewed `^n`, `^fd`, and `^nd` text presets |
| `./scripts/pnpmw run check:browser-directed` | Exact compatibility alias of `check:browser-reviewer` | Historical command name only |
| `./scripts/pnpmw run demo:categorical-displayed-nd-higher` | Optional direct-TypeScript object, whole-Hom, and higher-cell action | Advanced bounded witness; not a general `^nd` text binder |

## Run The Integrated Browser

Start the local reviewer workbench from the repository root:

```bash
./scripts/pnpmw --dir emdash-template --ignore-workspace exec vite
```

Then open the URL printed by Vite. The intended review path is:

1. choose or edit a categorical expression and select **Elaborate and
   check**;
2. inspect its explicit Core, inferred type, expected type, and structural
   lowering—or its source-located rejection;
3. open **Research evidence**, select **Run full research report**, and
   inspect the outer-LF, ordinary, and displayed witnesses;
4. open the fingerprinted emdash book from the same view; and
5. optionally use the preserved **Minimal Core playground** to exercise the
   generic LF checker directly.

No backend is required. The page does not acquire active Lambdapi source or
run a Lambdapi process.

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

The categorical adapter accepts text plus an immutable
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

The same adapter now also accepts:

```text
λ^n  k : K. (FF k) (s k)
λ^fd a : E. GG (FF a)
λ^nd k : K. composeCells (theta k) (eta k)
```

The intrinsic binder mode is mandatory; the `: category/family` annotation
is separately optional when the request's expected classifier supplies it.
These forms route to the existing dependent-section, displayed-functor, and
displayed-transformation builders. Pointwise data that cannot be internally
factored into a genuine coherent outer construction remains rejected.

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

## Build The Client-Side Reviewer

The selected browser fixture now contains the editable ordinary text view,
explicit three-panel report, generated book link, and preserved minimal-Core
playground:

```bash
./scripts/pnpmw run check:browser-reviewer
```

The command runs root typecheck and lint, fixture typechecking, and the Vite
production build. Its relative assets are compatible with a static project
subpath such as `https://hotdocx.github.io/emdash/`; no Pages workflow,
deployment, or publication has been added.

The browser imports only the narrow reviewer entry. It does not expose an
arbitrary `CoreCategoricalProgram` or the Node-only acquisition adapter to
editable JavaScript. The frozen minimal `src/v3_2/browser.ts` API and manifest
remain byte-for-byte unchanged.

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

- integrated reviewer proposal/review:
  `f94d770b2fe91ac43352b9848c350fd258000db4` /
  `7d65de7`;
- external-review report:
  `f1cb532a88ccca84786aa1cd5ee7cb006b1ad5fc`;
- additive directed browser:
  `7f696cea4b6a369e5db41c0d5e57e778b61fa10c`;
- original ordinary categorical text adapter:
  `7513cbe9e0d1439b5b1250982f40cede48e9a811`;
- syntax-parity audit/review:
  `d73195b833d5afcb569898df110f392344d2deac` /
  `55161be`; and
- focused integrated reviewer test: eight checks, eight passes, zero
  failures, including direct-TypeScript equality for all six presets;
- focused syntax-parity corpus: eight checks, eight passes, zero failures;
- complete TypeScript aggregate after parity: 1,149 tests, 1,098 active
  passes, 51 intentional skips, and zero failures;
- Vite production build after syntax parity: 140 modules, a 116.78 kB-gzip
  initial script and a 159.58 kB-gzip lazy reviewer chunk; and
- real Chromium execution of the displayed-natural preset
  `λ^nd k : K. composeCells (theta k) (eta k)`, producing an accepted
  explicit-Core/checker result with zero console errors or warnings. The
  earlier integrated-reviewer checkpoint separately exercised the
  source-located rejection, full three-panel report, emitted PDF link, and
  minimal-Core checker.

## Exact Boundary

This candidate demonstrates:

- outer dependent lambda/Pi and the selected dependent Sigma-telescope
  computation;
- recursively usable ordinary functorial variables/binders;
- direct bounded displayed functor/transfor consumers;
- independent displayed siblings and one genuine displayed dependency edge;
- structural weakening/reindexing, pairing, diagonal/swap composites, and
  checked object/internalized-arrow observations; and
- bounded categorical text across `^f`, `^n`, `^fd`, and `^nd`, with
  recursive whitespace application, optional checked annotation, exact
  diagnostics, whole-Hom expected routing, and typed recursive cell
  composition;
- an integrated client-side reviewer with editable categorical text,
  explicit research report, generated book, and editable minimal-Core
  playground; and
- backend-neutral Core plus generic TypeScript checking/evaluation.

It does not yet claim:

- arbitrary displayed telescope depth;
- arbitrary/general `^nd` coherence beyond component eta and finite typed
  vertical composition;
- text lowering for displayed/dependent telescopes, contextual `indexOf`
  weakening, general structural constructors, nested lambdas, outer-LF
  terms, Pi, let, or holes;
- final agreement between experimental TypeScript `λ^mode` syntax and
  informal Lambdapi/kernel notation;
- full displayed/dependent categorical text parity beyond the reviewed
  single-binder modes;
- a GitHub Pages workflow, deployment, or publication;
- systematic groupoidal-DTT closure;
- complete transfer of the Lambdapi library;
- unrestricted normalization, confluence, or standalone subject reduction;
  or
- a performance or release SLA.

The selected text, historical directed-browser, and integrated reviewer rows
are recorded in
[`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md)
and
[`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md).
The historical Parsimmon parser remains baseline grammar evidence; the
implemented adapter is dependency-free. The immediate product continuation
remains the dedicated
[`syntax-parity plan`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md):
the modes-first `1A` route is implemented, while `1B` inventories
context/telescope and displayed structural syntax and `1C` covers remaining
selected mathematical constructors. Parsing remains deterministic; typed
resolution and internal factorization may fail closed without heuristic
action or naturality synthesis. After exact parity graduation, the product
route proceeds to the theorem-led book and repository graduation plan. Bulk
scale remains deferred; one exact scale dependency may move earlier only
when a compelling reviewer witness measurably requires it.
