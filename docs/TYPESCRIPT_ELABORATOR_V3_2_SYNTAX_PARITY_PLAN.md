# TypeScript Elaborator v3.2 — User-Syntax Parity Plan

Date: 2026-07-30
Plan-ID: TS-ELAB-V3.2-SYNTAX-PARITY
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md`](./TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md),
[`TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md)
Status: `SYNTAX-PARITY-0A` inventory implemented and focused-green;
`H-DTTLF-PRODUCT-SYNTAX-PARITY-01 /
D-DTTLF-PRODUCT-SYNTAX-PARITY-001` approved as proposed by a separate
immutable unattended review with human supersession; `SYNTAX-PARITY-1A` is
final-green and checkpointed at
`2e7cc3c44802a5218858ca6747e7591d3bfc4859`; `SYNTAX-PARITY-1B0`
is an executable, focused-green, zero-behavior-delta audit checkpointed at
`be7000f88b08c90d24bad8a1e113fe3241d8a8ca`, with a bounded
`SYNTAX-PARITY-1B1` proposal approved exactly as proposed by a separate
immutable unattended review with human supersession; `SYNTAX-PARITY-1B1` is
final-green and checkpointed at
`9f663555a1edbedcb99e97f1271154ff36913f05`;
`SYNTAX-PARITY-1B2` is now an executable, focused-green,
zero-behavior-delta audit with a deeply frozen non-self-authorizing
independent-sibling proposal checkpointed at
`f53fd6885dd2fac0345bad5db257c7a66f86af15`; a separate immutable unattended
D003 review approves it exactly as proposed with human supersession; the
bounded implementation is final-green at exact local checkpoint
`ba34771074363f4c5b33814269b8822d4d2362bb`; `SYNTAX-PARITY-1B3` is now a
focused-green zero-behavior-delta audit with a deeply frozen
non-self-authorizing D004 proposal checkpointed at
`4eada97f9ee8fe284b70dea6c0548dfdb9754189`; a separate immutable unattended
D004 review now approves it exactly as proposed with human supersession; the
bounded 1B3 implementation is final-green at exact local checkpoint
`3dcf25ec008bb3d30723e3251c222e88acc216a3`; `SYNTAX-PARITY-1C0` is a
focused-green zero-behavior-delta residual-constructor audit with a deeply
frozen non-self-authorizing D005 proposal checkpointed at
`487ed014c210ab8426b27c40241b2de0f2f1dc4e`.
Selected-Successor:
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md)

## Objective And Human Priority

After the integrated reviewer is green, bring the end-user text surface into
measured parity with the mathematical constructions already exposed by the
direct typed TypeScript API. The first audit must prioritize the already
implemented natural, displayed functorial, and displayed natural modes
represented experimentally as `lambda^n`, `lambda^fd`, and `lambda^nd`.
After syntax graduation, the current product goal proceeds to the
reader-facing book/repository graduation plan. Bulk scale qualification stays
pending for a future persistent goal rather than automatically resuming here.

Here and below `lambda^mode` denotes the Unicode or ASCII intrinsic binder
head, such as `λ^nd` or `\^nd`. It does not revive the earlier temporary
notation in which the mode looked like part of a mandatory type annotation.
The domain or family annotation remains separately optional whenever
bidirectional expected information can recover it.

The target of parity is not arbitrary JavaScript syntax and is not every
possible callback program. It is the mathematical construction surface
accepted by the scoped TypeScript categorical programs:

- binders and bound-variable occurrences;
- typed categorical applications and their existing action selection;
- supported ordinary and displayed contextual constructors;
- supported dependent-context presentations; and
- the corresponding explicit-Core/checker/evaluator results and diagnostics.

The audit must make that target finite and testable before proposing a
runtime change.

## Settled Architecture

The text frontend remains an adapter into the existing implementation:

```text
source text
  -> private located name-bearing syntax
  -> immutable name/scope resolution
  -> existing classifier-directed categorical program
  -> existing recursive contextual lowering/factorization
  -> backend-neutral explicit emdash Core
  -> existing checker, conversion, evaluator, and runtime
```

There is no second `RawExpr` dependent type theory, categorical action table,
checker, evaluator, Core, or browser-only semantic implementation.

The current direct TypeScript callback APIs remain useful implementation
boundaries. A text binder resolves a source name to the same scoped token that
the callback receives and then recursively constructs the body through the
same typed program. The parser need not and cannot reproduce arbitrary
JavaScript control flow; parity means that the same supported mathematical
term can be constructed from text.

## Parsing, Elaboration, And Factorization Are Distinct

The implementation may expose one public `elaborate...Text` operation, but
its diagnostics and tests must preserve three conceptual phases.

### 1. Deterministic parsing

The grammar recognizes identifiers, grouping, application, binder heads,
optional annotations, and later selected telescope forms. Parsing is
deterministic and source-located. Parsimmon could express the same grammar,
but the already selected dependency-free recursive-descent implementation
is sufficient; a parser library would not solve the semantic steps below.

Malformed text is a parsing failure. A syntactically valid binder mode can
parse even when the current semantic profile does not yet implement it.

### 2. Typed resolution and application selection

Names resolve through an immutable typed environment. The subject
classifier, argument classifier, binder mode, and bidirectional expected
classifier select the existing `fapp*`, `tapp*`, component, whole-Hom, or
other reviewed action through the current program.

This selection must not be heuristic. If the available typed information does
not determine one supported action, the resolver must either require a
source annotation or reject the expression with an exact ambiguity/
unsupported-shape diagnostic. A conversion budget exhaustion is likewise a
diagnostic, never permission to guess.

### 3. Internal categorical factorization

Some categorical binder bodies must be recursively factored back into genuine
outer functors or transformations. This is a finite structural compilation
over the constructions already supported by the direct TypeScript surface.
It is not general theorem search.

For example, the current displayed-transformation factorer recognizes:

- a component of an already coherent closed `Transfd`; and
- recursively typed vertical composition of such components.

It then returns the corresponding genuine outer transformation. Arbitrary
pointwise data is rejected because component types alone do not construct
naturality. Adding a textual `lambda^nd` route must preserve that exact
invariant.

## Internalization Invariant

The frontend must never request or accept an external naturality square,
functoriality equation, or coherence witness from the user merely to turn
pointwise data into a categorical term. Object action, arrow action, and
higher action must be owned by sufficiently internalized emdash
constructions.

The existing TypeScript name `CoreCategoricalAbstractionEvidence` denotes
immutable lowering/inspection trace data: body IR, result IR, usage,
selected rule, and prerequisites. It is not an external proof premise.
New documentation and APIs should prefer terms such as *abstraction lowering
trace*, *occurrence metadata*, or *factorization trace* when the distinction
matters. A later mechanical rename may be proposed separately; it is not a
semantic prerequisite.

Consequently:

- text resolution may call an existing internally coherent constructor;
- a recursive factorer may recover an outer construction from a reviewed
  finite component grammar;
- unsupported bodies fail closed; and
- general automatic naturality synthesis remains outside the parser and this
  plan.

## Current Measured Starting Point

`src/v3_2/categorical_text.ts` currently owns a private three-node located
tree:

- identifier;
- left-associated whitespace application; and
- one intrinsic-mode lambda with an optional identifier annotation.

Its parser accepts an alphabetic mode suffix. Its resolver currently lowers
only `^f`; `^n`, `^fd`, and `^nd` reach the semantic
`UNSUPPORTED_BINDER_MODE` boundary. Ordinary application delegates
recursively to `CoreCategoricalProgram.apply`, and the root expected action
shape is forwarded only to the root application.

The direct typed surface is substantially wider. Existing reviewed evidence
includes, among other bounded profiles:

- ordinary functorial abstraction with recursive variable occurrence;
- indexed natural section abstraction and section composition;
- independent displayed siblings;
- displayed functor abstraction over identity, eta, finite composition, and
  qualified weakening/reindexing;
- stable displayed evaluation;
- one genuine displayed dependency edge and one mixed
  `a; b,c; d` telescope;
- displayed transformation eta and recursive component composition; and
- a separate displayed-transformation next-Hom/higher-action consumer.

This list is orientation, not the parity inventory. The audit must locate the
actual exported constructors, capability gates, expected classifier data,
profiles, positive tests, and fail-closed boundaries from current code.

## Completed `SYNTAX-PARITY-0A` Result

The executable, deeply frozen audit now lives in
`src/v3_2/categorical_text_parity_audit.ts`, with its focused witnesses in
`tests/v3_2_categorical_text_parity_audit_tests.ts`. It classifies all **68**
public `CoreCategoricalProgram` methods exactly once across **14**
mathematical-capability rows:

| Classification | Rows | Interpretation |
| --- | ---: | --- |
| already text-complete | 1 | Ordinary `lambda`/`^f` already has a checked text route. |
| mechanical syntax route | 1 | The six ordinary structural constructors need only a deterministic structural spelling and direct routing. |
| typed resolver seam | 9 | The direct mathematical operation exists; text needs a finite binding, expected-classifier, or structural-form contract. |
| semantic capability absent | 1 | Arbitrary contexts and general coherence synthesis are not direct-TypeScript capabilities and therefore are not parser work. |
| deliberately non-textual host behavior | 2 | Closed declaration construction and inspection/compilation remain host APIs rather than expression syntax. |

The audit also proves the following boundary without changing runtime
behavior:

- the lexer/parser already accepts the alphabetic intrinsic modes `^n`,
  `^fd`, and `^nd`;
- each currently reaches the exact resolver-side
  `UNSUPPORTED_BINDER_MODE` boundary;
- the corresponding direct `dependentLambda`,
  `displayedFunctorLambda`, and `displayedTransforLambda` operations execute
  under their reviewed profiles;
- recursive displayed-cell composition executes through the existing
  `composeCells` owner; and
- `CoreCategoricalProgram.apply` remains the one classifier-directed
  application ladder. The text frontend does not acquire a second action
  table.

The 68-method inventory is intentionally broader than the first
implementation tranche. It separates the already available single-binder
semantics from later dependent-context and explicit-constructor presentation
work rather than making “parity” an open-ended claim.

## Proposed Gate `H-DTTLF-PRODUCT-SYNTAX-PARITY-01`

Decision `D-DTTLF-PRODUCT-SYNTAX-PARITY-001` proposes
`SYNTAX-PARITY-1A`, the smallest dependency-closed product slice:

- enable intrinsic modes `n`, `fd`, and `nd`;
- route only to `dependentLambda`, `displayedFunctorLambda`,
  `displayedTransforLambda`, `composeCells`, and the existing `apply`;
- add a `displayed-family` environment binding kind and expected result kinds
  for dependent sections, displayed functors, and displayed
  transformations;
- recognize the fixed binary application spine
  `composeCells left right` and route it to the existing direct method; and
- preserve the direct finite factorization grammars and exact fail-closed
  behavior.

The exact positive witnesses are:

```text
λ^n  k : K. (FF k) (s k)
λ^fd a : E. GG (FF a)
λ^nd k : K. composeCells (theta k) (eta k)
```

The proposal must reject wrong annotations/profiles/endpoints,
non-adjacent cell composition, pointwise data that is not internally
factorable, and nested or multi-binder forms deferred to
`SYNTAX-PARITY-1B`. Text and direct TypeScript must produce equal explicit
Core and equal abstraction/factorization observations. Node and browser must
use the same adapter.

This proposal adds no mathematical owner, Core node, checker/evaluator
branch, external coherence evidence, Lambdapi declaration/rule, or second
semantic frontend. Its executable object reports zero semantic delta and is
non-self-authorizing. The separate immutable
[`D-DTTLF-PRODUCT-SYNTAX-PARITY-001` review](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_D001_REVIEW.md)
now approves the exact frozen scope under the user's standing unattended
delegation, with any later explicit human decision superseding it.

After `1A`, the measured continuation is:

1. `SYNTAX-PARITY-1B` — nested/dependent contexts and displayed/fibred
   structural forms;
2. `SYNTAX-PARITY-1C` — the remaining selected mathematical constructor
   spellings; and
3. `SYNTAX-PARITY-GRADUATE-1` — freeze the exact text/direct-TypeScript
   parity envelope and route to the book/repository graduation plan.

## `SYNTAX-PARITY-1A` Implementation Result

The modes-first implementation preserves the existing three-node private
located tree. `categorical_text.ts` now:

- accepts `displayed-family` entries in the immutable host environment;
- distinguishes expected ordinary functors, dependent sections, displayed
  functors, and displayed transformations;
- dispatches intrinsic `^f`, `^n`, `^fd`, and `^nd` heads to the existing
  direct typed builders;
- checks optional category or displayed-family annotations against the
  bidirectional expected contract;
- retains `CoreCategoricalProgram.apply` as the only generic action selector;
  and
- recognizes exactly the fixed binary
  `composeCells outer inner` application spine and calls the existing typed
  cell-composition method.

The implemented recursive text envelope is:

| Mode | Implemented body evidence |
| --- | --- |
| `^n` | section eta and indexed-section application/composition |
| `^fd` | displayed identity, eta, and finite nested displayed-functor composition |
| `^nd` | displayed-component eta and finite recursive typed `composeCells` composition |

Every exact positive source compiles to the same backend-neutral explicit
Core, inferred/expected type, and abstraction rule as its direct TypeScript
counterpart. Exact negatives cover wrong annotation kind, wrong
category/family, wrong expected mode, unavailable profile, wrong endpoint,
non-adjacent cell composition, non-internalizable pointwise data, nested
abstraction, and unreviewed modes.

The integrated browser reviewer now exposes six immutable presets: the
original three ordinary/action examples plus the exact `^n`, `^fd`, and
`^nd` witnesses. Each preset creates only its smallest existing reviewed
program profile, and Node/browser both call the same text adapter.

### Measured weakening boundary

The audit's `qualified-weakening-reindexing` phrase described the upper bound
of the existing direct `displayedFunctorLambda` factorer. During
implementation, the exact weakening body

```text
λ^fd a : E. s (indexOf a)
```

was rechecked. At the `1A` checkpoint its direct TypeScript construction was
green, but text could not construct the contextual `indexOf(a)` operation
from identifier/application syntax alone. The inventory already classified
`indexOf` with displayed and fibred structural constructors in
`SYNTAX-PARITY-1B`; therefore `1A` did not silently add another operation
spine. This was a presentation boundary, not a missing kernel owner or
factorization algorithm. The separately audited and reviewed `1B1`
continuation below now closes exactly that seam.

The implementation adds no mathematical owner, Core node,
checker/evaluator branch, semantic profile, runtime/proof/unification rule,
external coherence premise, parser dependency, or Lambdapi change.

Final validation is green:

- the focused text/inventory/parity/browser corpus passes 35/35;
- root typecheck and lint pass;
- the browser reviewer production build passes with 140 transformed modules;
- real Chromium accepts the exact `^nd` preset and reports zero console
  errors or warnings; and
- the complete TypeScript aggregate passes 1,149 tests: 1,098 active passes,
  51 intentional skips, and zero failures.

No proportional live-Lambdapi rerun was triggered because this tranche
changes no Lambdapi source, transferred declaration/rule, signature catalog,
semantic profile, or Core owner; its terms continue through already reviewed
owners and the existing checker.

## `SYNTAX-PARITY-1B0` Structural Audit And Proposed Gate

The executable, deeply frozen audit in
`src/v3_2/categorical_text_structural_audit.ts` measures the smallest
remaining displayed-structure seam:

```text
λ^fd a : E. s (indexOf a)
```

The direct TypeScript term is already green. It compiles through
`displayedFunctorLambda`, `apply`, and `indexOf`, selects
`categorical.displayed-functor-weakening`, and retains the internal
`section-pullback` and `sigma-first-projection` owners. The text term fails
only because `indexOf` is not yet a recognized operation head:

```text
UNKNOWN_IDENTIFIER at columns 16–23
```

This is therefore a presentation seam, not a missing dependent/category
construction, factorization rule, or kernel feature.

The audit splits the formerly broad `1B` row:

1. `SYNTAX-PARITY-1B1` — contextual `indexOf` and displayed weakening;
2. `SYNTAX-PARITY-1B2` — independent displayed sibling binders and
   `fibrePair`; and
3. `SYNTAX-PARITY-1B3` — bounded genuine dependent and mixed displayed
   telescopes.

This split prevents the deterministic unary operation route from being
blocked on the genuinely design-sensitive multi-binder presentation.

### Proposed gate `H-DTTLF-PRODUCT-SYNTAX-PARITY-02`

Decision `D-DTTLF-PRODUCT-SYNTAX-PARITY-002` proposes only
`SYNTAX-PARITY-1B1`:

- retain the existing identifier/application/lambda located tree;
- factor exact fixed-arity application-spine recognition so it is shared
  with the existing `composeCells` route;
- recognize the reserved unary spine `indexOf argument`;
- route it to the existing `CoreCategoricalProgram.indexOf`;
- delegate profile, scope, and active-slot validation to that typed method;
- retain `CoreCategoricalProgram.apply` as the only ordinary application
  path;
- prove text/direct equality for the exact weakening witness;
- preserve exact failures outside an active displayed slot, under an
  unavailable profile, for wrong arity/closed/foreign arguments, and for
  wrong expected families; and
- add one integrated-reviewer preset using the same browser-safe text adapter.

The proposal authorizes no parser node, mathematical owner, program method,
Core/checker/runtime rule, coherence premise, Lambdapi change, multi-binder
syntax, `fibrePair`, dependent telescope, or `1C` constructor. Its five
focused audit tests pass, and typecheck/lint are green. The separate
[`D-DTTLF-PRODUCT-SYNTAX-PARITY-002` review](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_D002_REVIEW.md)
now approves only this exact scope under the user's standing unattended
delegation, with any later explicit human decision superseding it.

## `SYNTAX-PARITY-1B1` Implementation Result

The implementation preserves the private three-node located tree and
refactors only its resolver-side operation-spine inspection:

- one generic fixed-arity application-spine helper now recognizes the
  already reviewed `composeCells` binary head and the new `indexOf` unary
  head;
- `indexOf argument` resolves its argument recursively and calls the existing
  `CoreCategoricalProgram.indexOf`;
- active-slot, profile, and ownership checks remain solely in that typed
  method; and
- every non-reserved application still routes through the existing
  `CoreCategoricalProgram.apply`.

Both

```text
λ^fd a : E. s (indexOf a)
λ^fd a. s (indexOf a)
```

compile to the same explicit Core and classifier evidence as direct
TypeScript, select `categorical.displayed-functor-weakening`, and retain
`section-pullback` plus `sigma-first-projection`. Exact negatives cover the
unavailable profile, wrong target family, closed and foreign terms, and
missing/extra arguments.

The integrated reviewer now has a seventh `Displayed weakening` preset using
the same adapter and checker. Its production build remains at 140 transformed
modules; initial JavaScript is 429.10 kB / 116.78 kB gzip and the lazy
reviewer is 724.67 kB / 159.77 kB gzip. Real Chromium accepts the exact
weakening source and reports zero console errors or warnings.

Final proportional validation is green:

- the combined existing text, 1A parity, 1B0 audit, 1B1 implementation, and
  browser-reviewer corpus passes 39/39;
- root and fixture typecheck plus root lint pass;
- the production browser build passes; and
- no live Lambdapi rerun is triggered because no owner, transfer input,
  profile, or Lambdapi source changed.

The complete 1,149-test root aggregate immediately preceding this bounded
resolver-only continuation remains the repository regression baseline. This
slice adds ten focused audit/implementation checks and reruns every affected
text/browser suite rather than repeating the unchanged 15-minute semantic
corpus.

## `SYNTAX-PARITY-1B2` Independent-Sibling Audit And Proposed Gate

The executable, deeply frozen audit in
`src/v3_2/categorical_text_sibling_audit.ts` measures the next direct/text
boundary:

```text
λ^fd (b : B, c : C). fibrePair (FF b) (GG c)
```

The corresponding direct TypeScript construction is already green:

```text
displayedContextLambda(
  [{name: "b", family: B}, {name: "c", family: C}],
  P(D,Q),
  ([b,c]) => fibrePair(FF(b),GG(c))).
```

It selects `categorical.displayed-context-bracket`, records one
shared-minimal-base sibling group, and lowers through the existing displayed
left/right projections, generic displayed composition, and displayed pairing
owner. The active kernel uses the transparent fibrewise product family and
fixed-base universal-property owners; there is no `Product_catd` head to
introduce. Object, base-arrow, internalized-arrow, and higher coherence remain
inside those existing constructions.

The present text failure is earlier and exact: the private parser expects one
identifier after `λ^fd` and rejects the opening parenthesis at columns 6–7.
This is therefore a multi-binding presentation seam, not a missing categorical
construction.

### Selected scalable notation

The proposed separator semantics are:

- commas bind independent siblings at one dependency level;
- semicolons separate successive dependency levels, but remain rejected until
  the separately gated `SYNTAX-PARITY-1B3` row.

Thus the annotated and bidirectionally inferred forms are:

```text
λ^fd (b : B, c : C). fibrePair (FF b) (GG c)
λ^fd (b, c). fibrePair (FF b) (GG c).
```

Nested unary syntax such as `λ^fd b. λ^fd c. ...` is not selected: it does not
present the direct API's independent sibling block or its fibrewise-product
context. A host-method-call spelling is also unnecessary. The text adapter
must receive the ordered source families through immutable expected typing
information; it must not decompose private Core provenance or guess a product
presentation.

### Proposed gate `H-DTTLF-PRODUCT-SYNTAX-PARITY-03`

Decision `D-DTTLF-PRODUCT-SYNTAX-PARITY-003` proposes only
`SYNTAX-PARITY-1B2`:

- keep the private located language at three node kinds while generalizing
  the lambda payload to immutable ordered binding groups;
- treat existing unary binders as singleton groups;
- parse exactly one parenthesized comma-separated group of at least two
  portable names with independently optional annotations;
- add one bidirectional `displayed-context-functor` expectation containing
  the ordered source families and target family;
- require the number and optional annotations to agree with that expectation;
- invoke the existing `displayedContextLambda` once, extend one immutable
  environment with all sibling tokens, and resolve the body recursively;
- recognize only the exact binary `fibrePair left right` spine and call the
  existing typed method;
- keep all other application in the sole existing `apply` ladder; and
- add one integrated-reviewer preset through the same browser-safe adapter.

The direct program remains responsible for common-base, target-base,
dependency-plan, active-slot, branch-family, and recursive-factorization
checks. Exact negatives cover malformed/singleton/duplicate groups, expected
arity and annotation mismatch, cross-base families, wrong expectation or
mode, invalid `fibrePair` arity/scope/base, semicolon-dependent telescopes,
nested abstraction, and unsupported bodies.

The proposal adds no mathematical owner, `Product_catd`, Core node,
categorical-program method, checker/evaluator branch, factorization case,
runtime/proof rule, external coherence premise, Lambdapi change, parser
dependency, or second semantic frontend. `SYNTAX-PARITY-1B3` remains a
separate review even though the private group representation is deliberately
compatible with adding semicolon-separated dependency levels later.

The five focused executable audit tests pass, as do root typecheck and lint.
The recovery baseline immediately before this zero-behavior-delta audit also
passes all 1,159 TypeScript tests: 1,108 active passes, 51 intentional skips,
and zero failures. No proportional Lambdapi check is triggered because the
proposal changes no active source, transferred declaration/rule, Core owner,
or semantic profile.

The separate
[`D-DTTLF-PRODUCT-SYNTAX-PARITY-003` review](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_D003_REVIEW.md)
now approves only this exact 1B2 scope under the user's standing unattended
delegation, with any later explicit human decision superseding it.

## `SYNTAX-PARITY-1B3` Dependent-Context Audit And Proposed Gate

The executable, deeply frozen audit in
`src/v3_2/categorical_text_dependent_audit.ts` measures the final selected
context-presentation seam. The existing direct program already accepts
exactly two dependent shapes:

```text
a : A; b : B
a : A; b : B, c : C; d : D
```

The first is one genuine displayed dependency edge. The second is the
reviewed three-level mixed telescope with independent middle siblings. Their
direct rules are respectively
`categorical.displayed-dependent-context-bracket` and
`categorical.displayed-mixed-dependent-context-bracket`. Family bases and
source order drive the existing dependency planner; the caller supplies no
dependency flags. Object, internalized-arrow, reindexing, and recursive-body
behavior are already owned by `displayedDependentContextLambda` and its
Sigma/pullback/product/pairing prerequisites.

The selected text forms are:

```text
λ^fd (a : A; b : B). a
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c

λ^fd (a; b). a
λ^fd (a; b, c; d). fibrePair b c
```

Commas retain their 1B2 meaning—independent siblings at one dependency
level. Semicolons begin the next displayed dependency level. The parser
currently reaches exactly the first semicolon and rejects it at columns
12–13 with the intentionally installed 1B3 boundary. This is a presentation
seam, not a missing dependent-context algorithm.

Decision `D-DTTLF-PRODUCT-SYNTAX-PARITY-004` proposes only:

- activate semicolon-separated immutable `bindingGroups` in the existing
  private lambda payload, adding no located node kind;
- require portable names unique across the complete telescope;
- accept only the direct program's exact group sizes `[1,1]` and `[1,2,1]`;
- add one `displayed-dependent-context-functor` expected contract containing
  matching ordered source-family groups and one target family;
- check optional annotations positionally; annotation omission uses the
  expected families and does not synthesize or decompose family expressions;
- flatten checked groups in source order and invoke the existing
  `displayedDependentContextLambda` exactly once;
- extend one immutable callback environment with all returned tokens and
  resolve the body through the existing recursive `indexOf`, `fibrePair`,
  `composeCells`, and generic `apply` routes; and
- add one `displayed-mixed-telescope` reviewer preset through the same
  browser-safe adapter and checker.

The direct program remains responsible for profile availability, exact
two/four-binding arity, family bases, dependency-plan derivation, target
base, slot scope, body factorization, and internal categorical coherence.
The text frontend neither asserts dependency flags nor promotes arbitrary
pointwise data.

Exact negatives cover empty or trailing dependency levels, duplicates across
levels, wrong group counts/cardinalities, annotation kind/family mismatch,
wrong mode or expected contract, predecessor profiles, wrong middle/deepest/
target bases, reordered siblings, unsupported three-binding or deeper
shapes, escaped/foreign slots, unsupported bodies, nested abstractions, and
general dependent-family syntax.

The proposal adds no mathematical owner, dependency planner, categorical
program method, contextual factorization case, Core node, checker/evaluator
branch, runtime/proof rule, semantic profile, transfer input, Lambdapi
declaration/rule, external coherence premise, or second frontend. Arbitrary
depth stays a real direct-capability boundary rather than parser work.

The five focused executable audit tests, root typecheck, and lint pass. The
audit changes no runtime behavior. Its separate exact gate is:

> Approve `H-DTTLF-PRODUCT-SYNTAX-PARITY-04 /
> D-DTTLF-PRODUCT-SYNTAX-PARITY-004` as proposed: implement only the
> semicolon/comma presentation of the existing `[1,1]` and `[1,2,1]`
> displayed dependent-context shapes, their grouped expected-family contract,
> recursive existing-method resolution, complete negative partition, and one
> mixed-telescope reviewer preset; add no arbitrary-depth/general
> dependent-family syntax, new semantic owner/rule/profile, external
> coherence premise, Lambdapi change, scale work, book work, publication, or
> wider Git authority?

## `SYNTAX-PARITY-1B3` Implementation Result

The implementation activates exactly the reviewed private presentation:

- commas retain the 1B2 meaning of independent siblings within one level;
- semicolons separate successive dependency levels;
- only group sizes `[1,1]` and `[1,2,1]` reach typed dependent resolution;
- one grouped expected-family contract checks every optional annotation
  positionally;
- resolution flattens the checked groups in source order and invokes the
  existing `displayedDependentContextLambda` exactly once; and
- every body continues through the existing recursive identifier,
  `indexOf`, `fibrePair`, `composeCells`, and generic `apply` routes.

Annotated and annotation-free forms compile to the same explicit Core as
direct TypeScript. Permanent evidence covers every mixed-telescope slot,
recursive application beneath a closed displayed functor, object action,
internalized-arrow action, malformed levels, duplicate names, expected
group/annotation/mode mismatch, predecessor profiles, wrong bases/targets,
escaped bodies, and nested-abstraction rejection.

The ninth reviewer preset exposed one packaging seam: the program's historical
CommonJS lazy load for the already reviewed `fibred-displayed-chain-2a`
closure was not executable in a browser. The correction does not duplicate or
weaken the transfer:

- `compileCoreCategoricalDisplayedChain2aClosureRuntime` compiles the same
  frozen declarations and subject-checked nine-rule runtime without executing
  the Node-loaded D-017/scale ledger validator;
- the ordinary Node/evidence transfer entry point first revalidates the scale
  engine and D-017 ledgers, then returns that identical cached compilation;
  and
- `CoreCategoricalProgram` statically consumes only the browser-safe checked
  runtime entry point.

Thus historical authorization validation remains a Node evidence concern,
while the client product executes the reviewed mathematical data through the
same generic checker/runtime. No owner, declaration, rule, profile, Core node,
checker branch, evaluator branch, dependency planner, factorization case, or
Lambdapi source changed.

Final proportional evidence is green:

- the focused dependent text corpus passes 7/7;
- the corrected affected text/direct/reviewer corpus passes 75/75;
- the browser-safe versus review-validating transfer identity corpus passes
  6/6;
- all eight historical usability/fibred/displayed graduation suites pass
  75/75;
- the integrated reviewer passes 8/8, including direct-TypeScript equality
  for all nine presets and its Node-free browser closure;
- root and fixture typecheck, root lint, and the production browser build
  pass at 141 modules, 429.29 kB / 116.82 kB gzip initial JavaScript, and
  745.30 kB / 164.73 kB gzip lazy reviewer JavaScript; and
- real Chromium accepts
  `λ^fd (a : A; b : B, c : C; d : D). fibrePair b c` with zero console
  errors or warnings.

The unchanged long direct `DISPLAYED-CHAIN-2A` semantic corpus was measured
as unsuitable for this presentation-only proportional gate after remaining
CPU-active beyond eleven minutes; the focused dependent text, transfer,
historical graduation, reviewer, build, and real-browser gates cover the
changed boundary. No live Lambdapi rerun is triggered because this slice
changes no mathematical source or transferred semantic input.

## `SYNTAX-PARITY-1C0` Residual Constructor Audit

The executable post-1B3 audit in
`src/v3_2/categorical_text_constructor_audit.ts` reclassifies the remaining
mathematical-constructor surface before adding behavior. It confirms:

- the private located tree still needs no new node kind;
- `indexOf`, `fibrePair`, and `composeCells` are the only reserved operation
  heads presently routed before generic application;
- `compose G F` therefore fails exactly with `UNKNOWN_IDENTIFIER` on
  `compose`, while direct `composeFunctors(G,F)` is green;
- all six ordinary structural term constructors are already owned and typed
  by the direct program;
- displayed/fibred term constructors need a finite argument-kind audit, not a
  new action table; and
- category/displayed-family-valued constructors need one checked result-kind
  contract over the same parser and program, not a second AST, checker, or
  dependent-family inference algorithm.

The audit refines 1C into four finite rows:

| Row | Exact responsibility |
| --- | --- |
| `SYNTAX-PARITY-1C1` | Six ordinary structural term heads: `id`, `compose`, `pair`, `map`, `pi1`, and `pi2` |
| `SYNTAX-PARITY-1C2` | Remaining selected displayed/fibred term constructors after an explicit family/category/term/Hom-boundary argument-kind audit |
| `SYNTAX-PARITY-1C3` | Category and displayed-family result constructors through one typed result contract over the same located parser |
| `SYNTAX-PARITY-GRADUATE-1` | Freeze the exact mathematical-expression target and classify host context construction/inspection as textual or deliberately non-expression behavior |

This split prevents two opposite errors: it does not stop at six convenient
ordinary heads and falsely call that complete parity, and it does not turn
host fixture/inspection methods into expression grammar merely because they
are public TypeScript methods.

### Proposed gate `H-DTTLF-PRODUCT-SYNTAX-PARITY-05`

Decision `D-DTTLF-PRODUCT-SYNTAX-PARITY-005` proposes only
`SYNTAX-PARITY-1C1`:

- recognize the exact fixed-arity reserved spines
  `id A`, `compose G F`, `pair F H`, `map F P`, `pi1 B C`, and `pi2 B C`;
- add no grammar production or located node;
- resolve term arguments recursively through the existing resolver;
- resolve category arguments only as checked immutable category bindings in
  this row;
- call the existing `identityFunctor`, `composeFunctors`, `functorPair`,
  `productMap`, `productLeftProjection`, and `productRightProjection`
  methods;
- retain the direct program as the sole classifier/endpoint/profile
  authority and generic `apply` as the only non-reserved application path;
- prove equal explicit Core and inferred functor classifiers against all six
  direct constructions; and
- add no reviewer preset, because the existing editable workbench already
  accepts arbitrary source and another frozen preset would add product
  ceremony rather than capability evidence.

Exact negatives cover arity, category-versus-term kinds, foreign values,
composition endpoint mismatch, pair source mismatch, and profile
unavailability. The proposal adds no category/family result syntax,
displayed/fibred constructor syntax, mathematical owner, program method,
Core/checker/evaluator/runtime branch, expected-action table, parser
dependency, Lambdapi input, browser preset, book prose, scale row, or
publication.

Five focused executable tests, root typecheck, and lint pass. The audit
changes no runtime behavior. Its separate exact gate is:

> Approve `H-DTTLF-PRODUCT-SYNTAX-PARITY-05 /
> D-DTTLF-PRODUCT-SYNTAX-PARITY-005` as proposed: implement only the six
> frozen ordinary structural term heads through their existing typed program
> methods, recursive term resolution, checked category identifiers, direct
> equality and exact negatives; add no category/family-valued syntax,
> displayed/fibred constructor syntax, semantic owner/rule/profile,
> Lambdapi change, reviewer preset, book/scale work, publication, or wider
> Git authority?

## SYNTAX-PARITY-0A — Dependency-Ready Inventory And Design Audit

After the integrated-reviewer checkpoint, inspect every public or
product-relevant direct TypeScript categorical construction and record one
row per mathematical capability:

1. owning module and method;
2. required profile/capability;
3. input classifier and expected classifier;
4. scoped bindings introduced;
5. ordinary/displayed dependency and variance;
6. object-, arrow-, and higher-action ownership;
7. recursive body grammar already accepted by the direct implementation;
8. proposed text spelling;
9. whether the existing located tree is sufficient;
10. whether resolution is a mechanical route into an existing method;
11. exact positive equivalence witness against direct TypeScript; and
12. exact negative, ambiguity, or unsupported-shape witness.

Classify each row as exactly one of:

- **already text-complete** — current syntax and resolver cover it;
- **mechanical syntax route** — existing semantics need only grammar,
  environment, expected-classifier, or method routing;
- **typed resolver seam** — the semantic construction exists, but the current
  callback-only API needs a small parser-independent expected/scoping
  contract before text can call it cleanly;
- **semantic capability absent** — direct TypeScript itself does not yet
  support the construction, so this is not parser work; or
- **deliberately non-textual host behavior** — arbitrary JavaScript behavior
  with no mathematical syntax-parity obligation.

The audit must pay special attention to:

- `^n`, `^fd`, and `^nd` binders;
- nested binders and dependent telescope family resolution;
- optional annotations versus intrinsic binder modes;
- ordinary and displayed application at object and arrow levels;
- whole-Hom and higher-action expected routing;
- reindexing, weakening, pairing, and dependent-context constructors;
- contravariant positions; and
- exact factorization failure for pointwise-but-not-internalizable bodies.

The output is an executable/deeply frozen inventory plus a bounded
implementation proposal. The audit may add tests and proposal data but must
not add grammar or runtime behavior before a separate review.

## Expected Feasibility

The syntax portion is high-confidence and largely mechanical:

- the parser already reads arbitrary alphabetic intrinsic modes;
- binder tokens already provide hygienic scoped occurrences;
- direct constructors already prove the semantic lowering;
- application already enters one classifier-directed program; and
- every located node can retain exact source spans.

The remaining work is not expected to require a new kernel or frontend
architecture. The main engineering work is to expose enough typed expected
information to the resolver, recursively resolve dependent annotations under
earlier binders, and map each bounded callback construction to a deterministic
text form.

The audit may nevertheless find a real semantic absence. If so, it must
classify that row as absent and route it to the relevant usability/kernel
plan rather than hiding it in parser logic. One specifically required scale
owner may move earlier only through the existing measured, separately
reviewed selective-scale policy.

## Proposed Graduation Evidence

A later syntax-parity implementation is not complete merely because new
strings parse. For every promoted row it must demonstrate:

- source text and direct TypeScript compile to equal explicit Core;
- inferred and expected classifiers agree;
- object/arrow/higher observations match the direct capability where
  applicable;
- recursive occurrence and nested subexpression behavior are covered;
- unsupported modes, profiles, families, variances, and pointwise coherence
  fail at exact spans;
- browser and root entry points use the same text adapter;
- no external naturality evidence is accepted;
- no Node, parser-dependency, Lambdapi-source, or checker/Core semantic delta
  occurs unless separately proposed; and
- focused, aggregate, browser, and proportional Lambdapi conformance gates
  pass.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| SYNTAX-PARITY-0A | **complete; focused-green** | REVIEWER-INTEGRATE-1A and current direct TypeScript surface | Executable/deeply frozen 68-method/14-capability inventory, classification, direct semantic witnesses, exact negative boundary, and bounded proposal |
| H-DTTLF-PRODUCT-SYNTAX-PARITY-01 / D-DTTLF-PRODUCT-SYNTAX-PARITY-001 | **approved as proposed; immutable unattended review with human supersession** | SYNTAX-PARITY-0A and checkpoint `d73195b` | Review permits only the frozen `SYNTAX-PARITY-1A` three-mode/application/cell-composition scope |
| SYNTAX-PARITY-1A | **final-green at `2e7cc3c44802a5218858ca6747e7591d3bfc4859`** | approved D001 review | `^n`, `^fd`, `^nd`, immutable displayed-family/expected contracts, existing direct-builder routes, exact `composeCells`, six browser presets, negative boundaries, and 1,149-test aggregate |
| SYNTAX-PARITY-1B0 | **focused-green, zero behavior delta at `be7000f88b08c90d24bad8a1e113fe3241d8a8ca`** | final-green `SYNTAX-PARITY-1A` | Executable contextual-index measurement, exact 1B1/1B2/1B3 split, and bounded non-self-authorizing proposal |
| H-DTTLF-PRODUCT-SYNTAX-PARITY-02 / D-DTTLF-PRODUCT-SYNTAX-PARITY-002 | **approved as proposed; immutable unattended review with human supersession** | checkpointed `SYNTAX-PARITY-1B0` | Authorizes only the frozen `indexOf`/weakening 1B1 route and one reviewer preset |
| SYNTAX-PARITY-1B1 | **final-green at `9f663555a1edbedcb99e97f1271154ff36913f05`** | approved D002 review | Fixed unary `indexOf` spine through the existing typed method, exact text/direct weakening equality, negatives, seventh reviewer preset, and 39/39 proportional gate |
| H-DTTLF-PRODUCT-SYNTAX-PARITY-03 / D-DTTLF-PRODUCT-SYNTAX-PARITY-003 | **approved as proposed; immutable unattended review with human supersession** | checkpointed 1B2 proposal at `f53fd6885dd2fac0345bad5db257c7a66f86af15` | Authorizes only the frozen comma sibling group, ordered-family expected contract, exact `fibrePair`, and one reviewer preset |
| SYNTAX-PARITY-1B2 | **final-green at `ba34771074363f4c5b33814269b8822d4d2362bb`; audit/proposal at `f53fd6885dd2fac0345bad5db257c7a66f86af15`** | approved D003 review | One comma sibling group, optional positional family annotations, ordered-family expected contract, existing `displayedContextLambda`/`fibrePair` routes, eighth reviewer preset, 64/64 proportional gate, production build, and real Chromium |
| SYNTAX-PARITY-1B3 | **final-green at `3dcf25ec008bb3d30723e3251c222e88acc216a3`; audit/proposal at `4eada97f9ee8fe284b70dea6c0548dfdb9754189`** | final-green 1B2 and approved D004 review | Exact semicolon/comma `[1,1]`/`[1,2,1]` presentations, grouped expected families, existing dependent-context route, complete negatives, browser-safe reviewed runtime split, ninth reviewer preset, production build, and real Chromium |
| H-DTTLF-PRODUCT-SYNTAX-PARITY-04 / D-DTTLF-PRODUCT-SYNTAX-PARITY-004 | **approved as proposed; immutable unattended review with human supersession** | checkpointed 1B3 audit/proposal | Authorizes only semicolon dependency levels for the two existing direct shapes and one mixed-telescope reviewer preset |
| SYNTAX-PARITY-1C0 | **focused-green zero-behavior audit at `487ed014c210ab8426b27c40241b2de0f2f1dc4e`** | final-green `SYNTAX-PARITY-1B3` | Executable residual constructor inventory, exact 1C1/1C2/1C3 split, six direct-green ordinary witnesses, and bounded non-self-authorizing D005 proposal |
| H-DTTLF-PRODUCT-SYNTAX-PARITY-05 / D-DTTLF-PRODUCT-SYNTAX-PARITY-005 | pending separate exact review | checkpointed 1C0 audit/proposal | Would authorize only six ordinary structural term heads over existing typed methods |
| SYNTAX-PARITY-1C1 | gated | checkpointed 1C0 and approved D005 review | `id`, `compose`, `pair`, `map`, `pi1`, and `pi2` with direct/text equality and exact negatives |
| SYNTAX-PARITY-1C2 | gated | final-green 1C1 plus a separate exact audit/review | Remaining selected displayed/fibred term constructors with finite typed argument contracts |
| SYNTAX-PARITY-1C3 | gated | final-green 1C2 plus a separate exact audit/review | Category and displayed-family result constructors over the same parser/checker architecture |
| SYNTAX-PARITY-GRADUATE-1 | gated | completed reviewed parity rows | Freeze exact text/direct-TypeScript parity and residual semantic rather than parser gaps |
| SELECTIVE-SYNTAX-SCALE-* | conditional, none selected | a measured parity row requiring one missing active owner plus separate review | Promote only a named dependency required by a compelling text/reviewer witness |
| BOOK-DELTA-0A | selected successor after syntax graduation | SYNTAX-PARITY-GRADUATE-1 | Route to the book/repository plan’s capability-oriented delta audit; do not turn syntax implementation history into book prose |

## Explicit Non-Authorization

This plan currently authorizes no:

- new mathematical owner, runtime rule, proof rule, unification rule, Core
  node, checker/evaluator branch, or semantic profile;
- arbitrary pointwise-to-functor or pointwise-to-transformation promotion;
- external naturality/coherence witness API;
- heuristic action selection or theorem search;
- second parser, exported raw syntax type theory, checker, evaluator, or
  categorical action table;
- parser dependency or lockfile change;
- claim that every JavaScript callback has a textual equivalent;
- final repository-wide Lambdapi/TypeScript notation migration;
- Lambdapi-source acquisition parser;
- bulk transfer, groupoidal closure, book prose/artifact mutation, deployment,
  or publication; or
- push, merge, PR, release, rebase, amend, reset, history rewrite, cleanup,
  branch deletion, or worktree removal.

## Git And Persistent-Goal Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Existing authority permits bounded green local checkpoints only in the
dedicated goal branch/worktree after synchronized ledgers, exact staged-diff
review, and `git diff --cached --check`.

## Persistent `/goal` Launch Prompt

```text
Continue the next dependency-ready reviewed row routed by
docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md, with
docs/TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md as the
selected post-syntax product route,
docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md retained as the
future architecture-qualification ledger, and
docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md as the recovery entry.

Recover current code/tests, all worktrees and ancestry, staged and unstaged
state, active authorities, and living decision ledgers before acting.
Preserve the integrated reviewer and all completed semantic checkpoints.

Treat parity as parity with mathematical constructions exposed by the direct
typed TypeScript API, not arbitrary JavaScript callback behavior. Keep
parsing deterministic, use immutable scoped resolution and existing
classifier-directed programs, and distinguish parsing, typed elaboration,
and internal categorical factorization. Never guess an application action or
promote arbitrary pointwise data to coherent categorical data.

Recover the completed SYNTAX-PARITY-0A inventory, final-green
SYNTAX-PARITY-1A/1B implementations, and focused-green zero-behavior
SYNTAX-PARITY-1C0 residual-constructor audit. Do not reimplement those rows.
Preserve commas as independent siblings at one dependency level and
semicolons as successive dependency levels only for exact direct group sizes
`[1,1]` and `[1,2,1]`. Checkpoint the 1C0 audit/proposal if needed, obtain or
record its separate exact D005 review, then implement only the approved 1C1
ordinary structural heads. Do not silently add 1C2 displayed/fibred or 1C3
category/family-result behavior. A missing direct semantic capability belongs
in the relevant usability/kernel plan, not in parser heuristics.

After exact syntax graduation, route to the capability-delta and
reader-narrative rows in the book/repository graduation plan. Keep bulk
WalkingEnd/HIT, batch, and whole-transfer graduation pending for a future
goal unless one exact dependency is required by the selected reader-facing
example and separately reviewed.

Existing Git authority permits only bounded green local checkpoints in the
dedicated goal worktree after synchronized ledgers and exact staged-diff
review. Do not push, merge, publish, deploy, release, amend, rebase, reset,
rewrite history, delete branches/worktrees, or perform unrelated cleanup.
```

## Change Log

- **2026-07-30 — `SYNTAX-PARITY-1C0` residual constructors audited.**
  Reclassified the post-1B3 mathematical surface into six mechanical ordinary
  term heads, a separately gated displayed/fibred term row, a separately
  gated category/family-result row, and graduation-time host-operation
  classification. Direct execution confirms all six ordinary targets are
  green while text fails exactly at the unknown `compose` head. Froze a
  bounded non-self-authorizing D005 proposal with no browser preset or
  semantic delta. Five focused tests, typecheck, and lint pass; exact local
  audit/proposal checkpoint:
  `487ed014c210ab8426b27c40241b2de0f2f1dc4e`.
- **2026-07-30 — `SYNTAX-PARITY-1B3` implemented and final-green.** Added
  exact semicolon dependency levels for only `[1,1]` and `[1,2,1]`, grouped
  expected families, positional optional annotations, recursive existing-body
  resolution, and the ninth mixed-telescope reviewer preset. Chromium exposed
  and the implementation corrected one Node-only closure-loading seam by
  separating checked browser runtime compilation from historical ledger
  revalidation; both paths return the same compilation. Focused dependent,
  transfer, historical graduation, reviewer, type/lint, production-build,
  and real-Chromium gates are green. No mathematical or Lambdapi semantic
  input changed. Exact local implementation checkpoint:
  `3dcf25ec008bb3d30723e3251c222e88acc216a3`.
- **2026-07-30 — D004 separately approved under unattended delegation.**
  After no immediate human objection to the checkpointed dependent-context
  proposal, recorded an immutable, human-supersedable review authorizing only
  exact `[1,1]` and `[1,2,1]` semicolon/comma presentations, their grouped
  expected-family contract, recursive existing-method resolution, complete
  negative partition, and one mixed-telescope reviewer preset. Arbitrary
  depth and every semantic addition remain withheld.
- **2026-07-30 — `SYNTAX-PARITY-1B3` dependent-context presentation
  audited.** Executably confirmed that the direct two-level genuine edge and
  `a; b,c; d` mixed telescope are already internally coherent, while text
  fails exactly at the reserved semicolon. Froze semicolons as successive
  dependency levels, retained commas for siblings, selected only direct group
  sizes `[1,1]` and `[1,2,1]`, and proposed a grouped expected-family
  contract plus one reviewer preset. Five focused tests, typecheck, and lint
  pass with zero behavior delta. Exact local audit/proposal checkpoint:
  `4eada97f9ee8fe284b70dea6c0548dfdb9754189`.
- **2026-07-30 — `SYNTAX-PARITY-1B2` implemented and final-green.** Added
  exactly one parenthesized comma sibling group, positional optional family
  annotations, the ordered-family expected contract, and the exact binary
  `fibrePair` spine. Resolution calls the existing
  `displayedContextLambda` once and otherwise retains the sole typed `apply`
  ladder. Annotated, annotation-free, direct-TypeScript, object, and
  applicable internalized-arrow observations agree; malformed groups,
  semicolon dependency levels, counts, annotations, bases, modes, scope,
  arity, and recursive branch typing fail closed. The affected nine-suite
  corpus passes 64/64, root/browser typecheck and lint pass, the 140-module
  production build passes, and real Chromium accepts the eighth reviewer
  preset with zero console errors or warnings. No Core owner, checker,
  evaluator, runtime/proof rule, semantic profile, transfer input, or
  Lambdapi source changed. Exact local implementation checkpoint:
  `ba34771074363f4c5b33814269b8822d4d2362bb`.
- **2026-07-30 — D003 separately approved under unattended delegation.**
  After no immediate human objection to the checkpointed sibling proposal,
  recorded an immutable, human-supersedable review authorizing only one comma
  sibling group, the ordered-family expected contract, exact `fibrePair`, and
  one reviewer preset. Semicolon dependency levels and all semantic additions
  remain withheld.
- **2026-07-30 — `SYNTAX-PARITY-1B2` sibling presentation audited.**
  Executably confirmed that the mapped independent-sibling direct term is
  already internally coherent and text currently fails only at the
  parenthesized binder group. Selected commas for independent siblings,
  reserved semicolons for 1B3 dependency levels, rejected nested-unary and
  host-method spellings, and froze a bounded non-self-authorizing D003
  proposal. The audit changes no parser/resolver or semantic behavior. Exact
  local audit/proposal checkpoint:
  `f53fd6885dd2fac0345bad5db257c7a66f86af15`.
- **2026-07-30 — `SYNTAX-PARITY-1B1` implemented and final-green.**
  Recognized only the exact unary `indexOf` spine through the existing typed
  method, retained one generic fixed-arity spine utility and one ordinary
  application ladder, proved direct/text weakening equality and exact
  failures, and added the seventh reviewer preset. The 39-test proportional
  corpus, typecheck/lint, production build, and Chromium exercise are green;
  no Core/kernel/Lambdapi semantics changed. Exact local implementation
  checkpoint: `9f663555a1edbedcb99e97f1271154ff36913f05`.
- **2026-07-30 — D002 separately approved under unattended delegation.**
  After no immediate human objection to the checkpointed proposal, recorded
  an immutable, human-supersedable review approving only the unary
  `indexOf`/weakening route and one reviewer preset. Multi-binder context and
  remaining constructor syntax stay withheld.
- **2026-07-30 — `SYNTAX-PARITY-1B0` measured and split.** Confirmed that
  `λ^fd a : E. s (indexOf a)` is already semantically green and that text
  fails only at the unrecognized `indexOf` head. Froze the narrow
  non-self-authorizing 1B1 proposal and separated independent siblings and
  genuine dependent/mixed telescopes into 1B2/1B3. Five focused tests,
  typecheck, and lint pass; no behavior changed. Exact audit/proposal
  checkpoint: `be7000f88b08c90d24bad8a1e113fe3241d8a8ca`.
- **2026-07-30 — `SYNTAX-PARITY-1A` final-green and checkpointed.** Added
  the three reviewed intrinsic-mode routes, displayed-family/expected
  contracts, exact `composeCells` routing, direct/text equivalence and
  fail-closed evidence, and three corresponding browser presets. Preserved
  the private located tree, one application classifier, and all Core/kernel
  semantics. Measured that textual `indexOf` weakening belongs to the
  already scheduled structural/context row `1B`, rather than silently
  broadening `1A`. Focused 35/35, browser production/Chromium, and aggregate
  1,149/1,149 gates are green. Exact local implementation checkpoint:
  `2e7cc3c44802a5218858ca6747e7591d3bfc4859`.
- **2026-07-30 — D001 separately approved under unattended delegation.**
  After no immediate human objection to the checkpointed proposal, recorded
  an immutable, human-supersedable review approving only the three existing
  single-binder modes, the existing application ladder, and direct
  `composeCells` routing. Nested/dependent contexts and remaining structural
  syntax stay outside `SYNTAX-PARITY-1A`.
- **2026-07-30 — `SYNTAX-PARITY-0A` completed and first gate frozen.**
  Classified all 68 public categorical-program methods exactly once in 14
  executable capability rows. Confirmed that `^n`, `^fd`, and `^nd` already
  parse and fail only at the semantic mode boundary, while their direct
  internalized builders and recursive cell composition are green. Proposed
  the bounded, non-self-authorizing `SYNTAX-PARITY-1A` modes-first slice and
  separated later context/constructor parity into `1B` and `1C`.
- **2026-07-30 — Book/repository graduation selected after syntax parity.**
  The current product goal now proceeds from exact text/direct-TypeScript
  parity to a capability-oriented, theorem-led book update and consolidated
  repository introduction. Bulk scale rows remain pending in their ledger
  for a future goal rather than automatically resuming after this plan.
- **2026-07-30 — Syntax parity selected as the next product-facing task.**
  Recorded the user's clarification that the desired post-reviewer task is to
  synchronize text with the mathematical constructions already exposed by
  the direct TypeScript API, especially existing `^n`, `^fd`, and `^nd`
  capabilities, before deferred bulk scale work.
- **2026-07-30 — Parsing and internalization boundary clarified.** Parsing is
  deterministic; syntactically valid input may later fail typed resolution
  or internal factorization. Application selection uses classifiers and
  expected information rather than heuristics. Existing abstraction
  “evidence” is lowering trace metadata, not an external naturality premise,
  and general coherence theorem synthesis remains outside the parser.
