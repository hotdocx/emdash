# TypeScript Elaborator v3.2 — User Syntax And Recursive Resolution Plan

Date: 2026-07-29
Plan-ID: TS-ELAB-V3.2-USER-SYNTAX
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`](./TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md)
Supersedes: no typed TypeScript construction API, existing contextual
compiler, checker, Core, parser/acquisition decision, or usability envelope
Status: active design subplan; SYNTAX-0A architecture audit complete;
the selected browser-directed product slice is complete and
SYNTAX-RESOLVE-0B is approved exactly as proposed under
D-DTTLF-PRODUCT-SYNTAX-001 with human supersession; SYNTAX-PARSER-0C is the
completed measurement; the dependency-free tiny parser is selected in the
frozen H-DTTLF-PRODUCT-SYNTAX-02 implementation proposal, now approved
exactly under D-DTTLF-PRODUCT-SYNTAX-002 with human supersession; the user's
H-DTTLF-PRODUCT-SYNTAX-03 / D-DTTLF-PRODUCT-SYNTAX-003 correction separates
intrinsic `λ^mode` capability from an optional `: annotation`; no located tree
or resolver landed as unused runtime infrastructure; SYNTAX-1A is implemented
and final-green at exact local checkpoint
`7513cbe9e0d1439b5b1250982f40cede48e9a811`; the user's later integrated
product correction promotes browser joining of this exact ordinary syntax
through
[`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md);
that integration is now implemented and focused/browser-green, and the
user's latest priority selects the dedicated
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md)
audit for existing `^n`, `^fd`, `^nd`, and other direct-TypeScript
mathematical capabilities before deferred bulk scale

## Purpose And Meaning Of Usability

The intended goal is not merely nicer punctuation. In ordinary dependent type
theory, a bound variable may occur recursively inside a typed expression, and
ordinary application syntax is resolved from the type of the function. The
emdash categorical layer should offer the analogous experience while
respecting its richer action structure:

- object versus arrow and higher-cell arguments;
- functorial, natural, object-only, displayed-functor, and displayed-natural
  abstraction capabilities;
- covariant and contravariant positions;
- `fapp*`, `tapp*`, internalized Hom, displayed, and higher action; and
- weakening, contraction, exchange, pairing, evaluation, reindexing, and
  dependent telescope structure generated from recursive occurrence.

A string parser can expose this behavior, but tokenization does not create it.
The existing recursive categorical contextual compiler already owns the
substantive lowering for its reviewed envelope. This plan adds a located
source adapter to that path; it must not restart the semantics in a second
`RawExpr` checker.

Explicit typed TypeScript calls such as `lambda`,
`displayedDependentContextLambda`, `apply`, and `fibrePair` remain supported
first-class end-user input. Text syntax is additive.

## Existing Semantic Architecture

### Outer LF

`CoreLfScopedBuilder` is a HOAS-style construction API whose callbacks execute
once and whose stored representation is first-order. It supports scoped:

- Core embedding and owner application;
- generic calls and explicit/implicit application;
- `Pi`, lambda, and let;
- binder modes; and
- lowering to the existing locally nameless explicit Core.

The builder does not itself replace the generic LF checker. It constructs the
same `KernelExpression` checked by the existing LF/checker path.

### Categorical layer

`CoreCategoricalProgram` exposes branded typed categories, displayed families,
terms, Hom boundaries, and contextual slot tokens. Its `apply` delegates to
the existing typed application classifier. Its abstraction APIs include:

- ordinary `lambda`;
- dependent indexed `dependentLambda`;
- independent displayed-sibling `displayedContextLambda`;
- the reviewed one-edge and exact mixed four-binding
  `displayedDependentContextLambda`;
- bounded direct `displayedFunctorLambda` (`^fd`-equivalent); and
- bounded coherent `displayedTransforLambda` (`^nd`-equivalent).

The underlying first-order contextual IR already contains slot references,
closed Core terms, typed application, typed pair, cell composition,
categorical abstraction, classifiers, free-slot usage, and provenance. Its
recursive compiler generates explicit structural/action terms and fails
closed when the requested action is outside the active profile.

The ordinary compiler already handles the important nontrivial form:

```text
λ^f x. F x y0
```

where `x` occurs inside the subject of an inner application and `y0` is
closed. It lowers recursively through evaluation, product pairing, identity,
and constant structure. No explicit source-level bracket around `F x` is
needed.

The displayed compiler now handles independent siblings, stable evaluation,
one genuine dependency edge, the exact `a; b,c; d` mixed telescope, recursive
coherent component composition, and one next-Hom observation. These are real
but bounded capabilities; syntax must not advertise arbitrary depth, arbitrary
mixed variance, or general `^nd` coherence.

## Historical Parsimmon Evidence

Commit `6cb146364dfdaa299e95d3aa72a33da78e64c5e7` contains the former 162-line
`src/parser.ts` based on `parsimmon@^1.18.1`. It demonstrates that a compact
combinator grammar can cover:

- `let`, lambda, Pi, and right-associated arrows;
- explicit/implicit typed binder groups;
- left-associated explicit/implicit application;
- identifiers, `Type`, holes, and parentheses;
- whitespace/token handling; and
- recursive parsing under a list of in-scope binder names.

It is useful baseline evidence, not current architecture. It constructs the
retired named/HOAS `Term`, substitutes names through `replaceFreeVar`, and
uses mutable global definition and fresh-hole state. Those properties must
not be restored. Parsimmon itself is neither prohibited nor selected merely
because the older parser used it.

## SYNTAX-0A — Completed Architecture Audit

### A syntax tree is necessary but must remain syntactic

Any parser must temporarily represent identifier occurrences, binder
spelling, application association, parentheses, and source ranges. Calling
that representation a located syntax tree does not make it a second typed
Core. The boundary is:

```text
source text
  -> small located, name-bearing syntax
  -> recursive resolution through existing typed programs
  -> existing contextual IR / scoped LF builder
  -> backend-neutral explicit Core
  -> existing checker/evaluator
```

The located syntax layer may contain only source concepts:

- identifier;
- application spine;
- lambda/Pi/let where supported;
- binder name, annotation, plicity, and requested capability notation;
- parentheses and a small number of explicit surface constructors; and
- exact source span.

It may not contain Core owner IDs selected by a duplicate checker, inferred
semantic classifiers, rewrite rules, metavariable solutions, or its own
definitional equality.

### Vertical-integration constraint

The parser-independent contract is a planning and comparison boundary, not an
instruction to commit a dormant second AST. The first semantic implementation
must land these pieces together:

```text
editable source string
  -> located lexical nodes
  -> recursive resolution
  -> existing CoreCategoricalProgram calls
  -> a real CoreCategoricalTerm checked by the existing compiler
```

The located nodes may be tested directly while implementing that slice, but
they must not first ship as an isolated public model with no text consumer.
Likewise, a parser-only checkpoint must not return an apparently elaborated
term. Direct typed TypeScript remains the semantic reference and supported
API before, during, and after the text slice.

### Resolution is recursive but not a second type theory

The resolver must recurse over subexpressions because variable occurrences may
appear anywhere in the supported typed grammar. It performs three bounded
jobs:

1. lexical name resolution against an immutable host-supplied environment and
   callback-bound tokens;
2. selection of the existing outer-LF or categorical construction API from
   the requested layer and expected classifier; and
3. forwarding exact source spans and any necessary expected action shape to
   that existing API.

All classification, scoping, contextual occurrence analysis, action
lowering, Core checking, conversion, rewriting, and proof-time unification
remain owned by existing modules.

### Host-supplied typed environment

A text parser cannot infer what a project-specific identifier denotes merely
from its spelling. The public adapter therefore needs an immutable typed
environment whose entries are already-owned values, for example:

```text
A   -> categorical category
B   -> categorical category or displayed family
F   -> categorical term
y0  -> categorical term
T   -> outer-LF builder term
```

The environment must preserve program/builder identity and reject foreign
terms exactly as the existing APIs do. It replaces the old parser's mutable
`globalDefs`; it is not a global registry.

Nested resolution extends the environment with the exact callback token
provided by `CoreLfScopedBuilder` or `CoreCategoricalProgram`. Thus parsed
names compile through the same token identity, usage counting, and De Bruijn
lowering as direct TypeScript callbacks.

### Expected information is a legitimate bidirectional seam

Several categorical abstractions require a target category or displayed
family before their body is lowered. For example, `lambda` currently receives
both source and target categories, and displayed contextual abstraction
receives a target family. A source-only resolver should not guess these from
owner names.

The initial API should therefore check a parsed expression against an
explicit expected surface classifier supplied by the host. This is
bidirectional *routing* into existing typed constructors, not a second
bidirectional typechecker. A later measured seam may synthesize a target from
an already typed body, but it is not required for the first sound adapter.

### Silent application

Whitespace application should create one neutral located application node.
Resolution then uses the already typed subject and argument:

| Resolved subject/argument | Existing owner of the result |
| --- | --- |
| outer LF Pi / LF term | `CoreLfScopedBuilder.apply` and the existing LF checker |
| ordinary functor / object or Hom boundary | `CoreCategoricalProgram.apply` and its application table |
| ordinary transformation / point or Hom boundary | the same categorical classifier/action ladder |
| displayed functor / indexed or closed fibre object | the existing displayed application judgments |
| displayed transformation / point, object, arrow, or higher boundary | the bounded existing component/higher APIs and classifier |

Expected shape remains available when the subject classifier does not uniquely
select an action. Genuine ambiguity must produce a source-located diagnostic;
the parser must not select an arbitrary `fapp*` or `tapp*` spelling.

Explicit application annotations may later be added as disambiguation, but
ordinary whitespace remains the canonical surface application node.

### Binder capability and annotation are independent

Earlier kernel-development discussions used provisional forms such as:

```text
λ x :^o X. body
λ a :^f A. body
λ k :^n K. body
λ a :^fd E. body
λ k :^nd K. body
```

Those forms put capability information in an annotation-like position. That
is useful informal/historical evidence, but it conflates three independent
pieces of a source abstraction:

1. the intrinsic abstraction capability or mode;
2. the bound name; and
3. an optional domain, family, or classifier annotation.

The experimental TypeScript text adapter therefore uses:

```text
λ^f  x. body
λ^f  x : A. body
λ^n  k. body
λ^fd a : E. body
λ^nd k : K. body
```

and equivalent ASCII heads such as `\^f`. The mode is never inferred merely
from an omitted domain annotation: it selects the abstraction judgment to be
formed. An expected classifier may supply the domain/family, making the
annotation optional; when written, the annotation is resolved and checked
against that expectation. Thus `λ^f x. body` is ordinary bidirectional
checking, while `λ^f x : A. body` adds a checked source annotation.

This separation applies to `f`, `n`, `fd`, `nd`, and any later reviewed
capability, but it does not make those modes semantically interchangeable.
Each mode still needs its own expected-classifier and coherent lowering
contract. In particular:

- outer-LF binding and categorical object-only capability must not be
  conflated merely because an earlier draft used `o`;
- `^fd` lowers through coherent displayed-functor construction, not a
  pointwise family of arbitrary functions;
- `^nd` accepts only the reviewed coherent envelope and cannot synthesize
  missing naturality from point data; and
- owners such as `fapp*_func`, `tapp*_func`, evaluation, and internalized Hom
  contribute action cases but do not automatically define new binder modes.

The first text slice recognizes mode tokens lexically but accepts only `^f`
semantically. The other spellings fail closed until their existing typed
constructors receive reviewed resolver contracts.

This is not a repository-wide notation migration. Existing Lambdapi comments,
mathematical telescope notation such as `x :^n K`, and historical demo text
remain provisional evidence. They are not silently rewritten or interpreted
as the finalized product grammar. A later notation-consolidation gate must
compare the TypeScript surface, Lambdapi development conventions, outer-LF
binding, categorical object-only binding, plicity, and displayed dependency
after the relevant modes have executable evidence.

### Dependent telescopes

For a parsed displayed telescope, the resolver should first resolve each
family in source order and derive dependencies from its typed base, then call
the existing contextual APIs:

- independent same-base siblings use `displayedContextLambda`;
- the reviewed one-edge chain and exact mixed four-binding telescope use
  `displayedDependentContextLambda`;
- direct one-variable coherent displayed functor/transfor forms use their
  dedicated bounded APIs when their expected classifier selects them.

The parser supplies no manual “independent” or “dependent” flag that could
contradict the typed families. Unsupported depth or shape fails at the
existing program boundary with the parsed source span.

### Source diagnostics

Every located node maps directly to `CoreCategoricalSourceSite` or a Core
`SourceSpan`. Diagnostics should preserve:

- file/source label;
- start and end line/column;
- binder or application detail;
- existing categorical/LF error code; and
- a causal chain when a parser/resolver error wraps an existing error.

Parsing failure, unknown identifier, expected-layer mismatch, foreign
program/builder value, ambiguous action, and unsupported active-profile
action must remain distinguishable.

## Representative Qualification Matrix

The first semantic syntax implementation must not be accepted for parsing one
hard-coded demo string. It should qualify recursive resolution with at least:

1. ordinary open/open recursion:
   `λ^f x. (H x) (K x)`;
2. ordinary open/closed nested evaluation:
   `λ^f x : A. F x y0`;
3. one displayed dependency edge with recursive outer and inner occurrences:
   `λ^fd a : A. λ^fd b : B(a). FF[a]`;
4. one independent displayed sibling pair or contraction case;
5. one arrow/Hom-boundary application proving that whitespace is not hard
   wired to object action; and
6. negative unknown-name, wrong expected classifier, ambiguous/missing action
   shape, and unsupported-telescope cases with exact spans.

The first implementation may select a smaller profile only if the omitted
cases are explicitly staged and the implemented cases still exercise genuine
recursive subexpression resolution.

## SYNTAX-RESOLVE-0B — Frozen Contract Proposal

### First vertical slice

The first implementation is deliberately an **ordinary categorical** text
adapter. It proves the disputed recursive-variable and silent-application
architecture without claiming the outer-LF, displayed-telescope, or complete
notation surface. Its grammar is:

```text
expression   ::= lambda | application
lambda       ::= lambda-head whitespace identifier annotation? "." expression
lambda-head  ::= ("λ" | "\\") "^" mode
mode         ::= ASCII-letter+
annotation   ::= whitespace? ":" whitespace? identifier
application  ::= atom atom*
atom         ::= identifier | "(" expression ")"
```

Whitespace between atoms creates one neutral left-associated application
spine. The parser never emits `fapp*`, `tapp*`, evaluation, pairing, weakening,
contraction, or exchange owner names.

This slice supports one outer `^f` lambda per elaboration request and
arbitrarily recursive identifier/application/parenthesis subexpressions in
its body. A syntactically nested lambda is parsed, then rejected with an exact
unsupported-expectation diagnostic until a recursive expected-classifier
contract is separately frozen. This restriction does not prevent the first
slice from qualifying:

```text
λ^f x. (H x) (K x)
λ^f x : A. F x y0
F p
```

where `p` may be a typed whole-Hom boundary. The first two expressions prove
recursive open/open and open/closed occurrence lowering; the third proves
that whitespace application is not hard-wired to object action.

### Public adapter contract

The implementation may refine TypeScript spelling during the separate
implementation review, but it must preserve this semantic shape:

```ts
type CoreCategoricalTextBinding =
    | { readonly name: string;
        readonly kind: 'category';
        readonly value: CoreCategoricalCategory }
    | { readonly name: string;
        readonly kind: 'term';
        readonly value: CoreCategoricalTerm }
    | { readonly name: string;
        readonly kind: 'hom-boundary';
        readonly value: CoreCategoricalHomBoundary };

type CoreCategoricalTextExpected =
    | { readonly kind: 'term';
        readonly applicationShape?: CoreCategoricalExpectedShape }
    | { readonly kind: 'ordinary-functor';
        readonly source: CoreCategoricalCategory;
        readonly target: CoreCategoricalCategory };

interface CoreCategoricalTextRequest {
    readonly source: string;
    readonly sourceFile?: string;
    readonly environment:
        readonly CoreCategoricalTextBinding[];
    readonly expected: CoreCategoricalTextExpected;
}

function elaborateCoreCategoricalText(
    program: CoreCategoricalProgram,
    request: CoreCategoricalTextRequest
): CoreCategoricalTerm;
```

The adapter copies the readonly entry list into one request-local lexical
environment, rejects duplicate names deterministically, and never mutates
caller data or program state. Each value remains branded by its existing
program; foreign values are rejected by the existing program methods.
Callback extension binds the exact `CoreCategoricalSlotToken` supplied by
`program.lambda`, never a fabricated variable or De Bruijn index.

For a lambda request, the intrinsic mode is always present. The
`ordinary-functor` expectation supplies the exact source and target categories
required by `program.lambda`. If a source annotation is present, it must
resolve to a category and compare equal to that expected source through the
existing program comparison/checking boundary, not label equality. If it is
omitted, the resolver uses the expected source directly; this is bidirectional
checking, not parser-owned type inference. A lambda under `kind: 'term'`, an
application/identifier under an inapplicable functor expectation, or a nested
lambda without a reviewed recursive expectation fails closed.

For application, the resolver first resolves the subject and then every
argument recursively. It calls `program.apply` once per argument, passing a
Hom-boundary value as a boundary and all other admissible values as terms.
The optional `applicationShape` is forwarded only where the request supplies
it; no syntax or local lookup table guesses an `fapp*`/`tapp*` owner.

### Located-node and diagnostic contract

The internal located union has only `identifier`, `application`, and `lambda`
nodes plus offsets and one normalized `SourceSpan`. Parentheses affect
association and span coverage but do not become semantic nodes. Identifier
and binder names follow the existing safe-identifier restriction.

One exported `CoreCategoricalTextError` preserves:

- phase: `parsing` or `resolution`;
- stable code;
- exact source span and source label;
- a concise detail string; and
- an optional underlying `CoreCategoricalProgramError` or frontend error.

The frozen first-slice codes distinguish at least:

- unexpected token/end and invalid identifier;
- duplicate environment name;
- unknown identifier;
- expected category, term, or admissible application argument;
- missing or incompatible abstraction expectation;
- unsupported binder mode or nested abstraction; and
- underlying categorical rejection.

Line and column positions are one-based and end positions are exclusive. The
resolver passes the originating node span into every `program.lambda` and
`program.apply` call so downstream errors retain source location.

### Executable acceptance matrix

The implementation review must freeze concrete fixtures before code lands.
At minimum, the green slice must prove:

1. parsed `(H x) (K x)` is definitionally equal to the current direct
   TypeScript pointwise witness and has the same explicit Core;
2. parsed `F x y0` is equal to the direct nested-evaluation witness;
3. parsed Hom-boundary application selects the same existing whole-action
   path as direct `program.apply`;
4. a binder used zero, once, and twice retains current weakening, identity,
   and contraction evidence;
5. unknown names, duplicate host names, category/term mismatch, malformed
   input, nested lambda, and an unsupported/ambiguous action fail with exact
   spans;
6. no new checker, Core owner/node, runtime/proof rule, global registry, or
   Lambdapi dependency exists;
7. the module is Node-builtin-free and can enter a later additive browser
   entry without a server; and
8. the aggregate root TypeScript gate remains green.

Displayed `^fd`/`^nd`, dependent telescopes, outer-LF text, let/Pi/holes,
implicit arguments, recovery, editor services, and browser UI are explicit
later rows. The current direct TypeScript demonstrations remain the
qualification oracle for those rows.

### Decision gate

`H-DTTLF-PRODUCT-SYNTAX-01 /
D-DTTLF-PRODUCT-SYNTAX-001` proposes only:

1. this parser-independent contract;
2. disposable, uncommitted comparison of Parsimmon and a tiny local parser
   against the exact first-slice grammar and span cases; and
3. a subsequent separately reviewed parser-selection/implementation
   proposal in which parser, located nodes, resolver, tests, example, and
   ledger land together.

Approval does not select a parser, add a dependency, implement syntax, enter
the browser, widen categorical semantics, or alter Lambdapi. Losing spike
files must be outside the tracked tree or removed before any checkpoint.

## Parser Technology Alternatives

### Parsimmon

Advantages:

- proven small grammar organization in this repository's history;
- concise left/right-associative combinators;
- useful baseline diagnostics; and
- naturally browser-compatible.

Costs:

- reintroduces a dependency and lockfile change;
- its old name-threading/HOAS construction must be completely replaced; and
- exact spans and recovery may require custom wrappers.

### Small hand-written lexer plus Pratt/recursive-descent parser

Advantages:

- no dependency;
- precise ranges and binder-mode tokens;
- explicit control of whitespace application and error recovery; and
- easy separation of lexical syntax from semantic resolution.

Costs:

- more local parser code and tests;
- greater risk of gradually rebuilding a general language; and
- precedence/binder maintenance becomes repository-owned.

### Tagged template

Advantages:

- natural TypeScript interpolation of already typed values;
- avoids a global textual identifier environment for interpolated terms; and
- can retain source strings for diagnostics.

Costs:

- binder occurrences still require lexical name resolution;
- editor/browser input is less direct;
- interpolation/source offsets complicate diagnostics; and
- it does not eliminate the need for a small syntax representation.

### Direct typed TypeScript only

This remains valid and is the semantic reference path. It has excellent type
identity and no parsing ambiguity, but it does not provide a conventional
editable expression surface.

### Current recommendation

Do not select the library before approving the resolver contract. Then build
two disposable parser-only spikes over the same located-node tests:

1. a Parsimmon grammar informed by the historical code; and
2. a tiny lexer/Pratt or recursive-descent grammar.

Measure source size, dependency/lock impact, span quality, browser viability,
failure diagnostics, and ease of binder-mode extension. Delete the losing
spike before semantic checkpointing. Neither spike may implement typing, and
neither may land without the resolver and user-visible adapter.

## SYNTAX-PARSER-0C — Completed Comparison

### Method

Two disposable JavaScript parsers implemented the exact first-slice grammar
outside the tracked worktree:

- Parsimmon `1.18.1`, using the current documented `createLanguage`,
  `node`, and `parse` APIs; and
- one direct character cursor with recursive-descent lambda/application/atom
  methods.

Both received the same four valid inputs and eight invalid inputs. The valid
corpus included Unicode and ASCII lambdas, multiline whitespace, nested
open/open application, open/closed application, and a bare application. The
invalid corpus covered empty input, missing binder/period/parenthesis,
unsupported mode, trailing punctuation, and non-portable identifiers. Both
produced the same left-associated summaries, valid one-based line/column
ranges, and the same failure offsets. Neither prototype implemented name
resolution or typing.

Both were then bundled independently as browser ES modules with Vite
`5.4.21`. Measurements are observations from this disposable run, not
performance guarantees:

| Measure | Parsimmon | Tiny local parser |
| --- | ---: | ---: |
| parser-only source | 1,657 bytes / 63 nonblank lines | 2,960 bytes / 112 nonblank lines |
| Vite ES bundle | 24,615 bytes | 2,526 bytes |
| gzip bundle | 7,094 bytes | 856 bytes |
| 10,000 parses of the four-input corpus | 207.14 ms | 32.13 ms |
| project runtime dependencies | `parsimmon` | none |
| TypeScript support | separate `@types/parsimmon` or local declaration | native |

The installed Parsimmon package itself contained five files / 56,063 bytes
(approximately 80 KiB on disk) and no bundled `types` entry. Registry
inspection found `parsimmon@1.18.1` and `@types/parsimmon@1.10.9` as the
current packages. Both bundles were Node-builtin-free and browser-buildable.

The timing difference is immaterial at human editor scale. The meaningful
tradeoff is that Parsimmon expresses the grammar in roughly half the source,
while the tiny parser avoids two package/lock concerns, produces an
approximately eight-times-smaller gzip slice, and gives direct ownership of
stable diagnostic codes and exact token spans. Parsimmon's `node` API is
pleasant and remains a credible later choice if a substantially larger
grammar makes combinators cheaper than local maintenance.

Both disposable versions require one production correction: parenthesized
nodes must explicitly extend their covered source range through the closing
parenthesis while retaining the inner semantic node. The frozen
implementation tests include that range and multiline end-exclusive
positions.

### Selection

Select the tiny dependency-free lexer/recursive-descent parser for the first
ordinary categorical slice. This is not a general policy against parser
libraries. It is the lower-cost choice for the presently frozen three-node
grammar, the static-browser product direction, and the requirement to expose
stable source-located diagnostics without changing the lockfile.

The entire temporary comparison directory and its generated package graph
must be removed after these observations are recorded. No spike source is
copied into production verbatim; production TypeScript is implemented under
the exact proposal below.

## SYNTAX-NOTATION-0D — Human Correction To The First Slice

`H-DTTLF-PRODUCT-SYNTAX-03 /
D-DTTLF-PRODUCT-SYNTAX-003` records the user's direct clarification during
the still-uncommitted SYNTAX-1A implementation:

- abstraction capability is intrinsic to the binder head: `λ^f`, `λ^n`,
  `λ^fd`, or `λ^nd`;
- the bound name follows that head;
- `: A` is a separate annotation and is optional when the bidirectional
  expected classifier supplies the required source/family;
- an explicit annotation is checked, not trusted;
- omitted annotation never permits the resolver to infer or guess the binder
  capability; and
- parsing a mode token does not implement that mode's semantic lowering.

This correction supersedes only the old first-slice spelling and
mandatory-annotation wording in D-DTTLF-PRODUCT-SYNTAX-001/002. It does not
broaden the approved semantic profile, public API, checker boundary, browser
surface, or Git effects. The exact implemented ordinary forms are:

```text
λ^f x. body
λ^f x : A. body
\^f x. body
\^f x : A. body
```

The resolver continues to require
`expected: { kind: 'ordinary-functor', source, target }`. With no annotation,
`source` is passed directly to the existing `program.lambda`. With an
annotation, the named category must compare equal to `source`, after which
the expected source remains authoritative for construction.

The same syntactic separation is the working hypothesis for `^n`, `^fd`, and
`^nd`, but their annotation shapes and expected-classifier trees remain later
reviewed semantic rows. Outer-LF lambda versus categorical object-only lambda
also remains open. This correction deliberately does not normalize every
informal Lambdapi/kernel comment or historical plan example. Final
cross-environment notation consolidation is deferred until executable
evidence covers the relevant modes.

## SYNTAX-1A — Frozen Integrated Implementation Proposal

### Decision gate

`H-DTTLF-PRODUCT-SYNTAX-02 /
D-DTTLF-PRODUCT-SYNTAX-002` proposes the following exact integrated slice.
It is not self-authorizing merely because parser selection is complete.

### Source and public API

Add one Node-independent
`src/v3_2/categorical_text.ts` module exporting:

- `CORE_CATEGORICAL_TEXT_REVISION`;
- `CoreCategoricalTextBinding`;
- `CoreCategoricalTextExpected`;
- `CoreCategoricalTextRequest`;
- `CoreCategoricalTextErrorCode`;
- `CoreCategoricalTextError`; and
- `elaborateCoreCategoricalText`.

The public request and result retain the SYNTAX-RESOLVE-0B contract. The
located syntax union and parser class remain module-private so the repository
does not acquire a second public term language. The implementation exports
only the adapter's typed boundary and diagnostics.

The implementation uses the existing portable identifier grammar
`[A-Za-z][A-Za-z0-9_]*`. It accepts `λ` and `\`, recognizes a located binder
head such as `λ^f` or `\^f`, and rejects every mode except `^f` with a stable
diagnostic. The mode is intrinsic and mandatory. A separate `: category`
annotation is optional because the ordinary-functor expectation already
supplies the source; when present, it is checked against that source.
Whitespace application remains neutral and left-associated. Parentheses
change association and extend source coverage but do not become a semantic
node.

The adapter:

1. copies and validates the readonly host bindings into a request-local map;
2. parses exactly one expression and consumes all input;
3. resolves identifiers recursively, extending one lambda body with the
   exact callback token returned by `program.lambda`;
4. uses the expected source when the annotation is omitted, or compares an
   explicit annotation category with it using `program.compareCategories`,
   requiring `status: 'equal'`;
5. calls only `program.lambda` and `program.apply` for semantic construction;
6. forwards a term expectation's optional application shape only to the root
   application node, never indiscriminately to nested applications; and
7. wraps existing categorical failures without changing their code,
   provenance, or cause.

The initial resolver rejects a nested lambda with
`UNSUPPORTED_NESTED_ABSTRACTION`; recursive expected-classifier trees remain
a later exact design row. It also rejects categories in term positions and
terms/boundaries in annotation positions before calling the program. Merely
recognizing `^n`, `^fd`, and `^nd` does not authorize their semantic lowering.

The exact stable text-error code union is:

```text
UNEXPECTED_TOKEN
UNEXPECTED_END
INVALID_IDENTIFIER
DUPLICATE_BINDING
UNKNOWN_IDENTIFIER
EXPECTED_CATEGORY
EXPECTED_TERM
EXPECTED_ARGUMENT
MISSING_ABSTRACTION_EXPECTATION
INCOMPATIBLE_ABSTRACTION_EXPECTATION
UNSUPPORTED_BINDER_MODE
UNSUPPORTED_NESTED_ABSTRACTION
CATEGORICAL_REJECTION
```

Every error carries phase, code, one `SourceSpan`, detail, and optional
underlying error. Positions are one-based and end-exclusive, including
multiline input and zero-width parse failures at end of input.

### Executable consumer and tests

Add:

- `examples/v3_2_categorical_text_demo.ts`;
- package command `demo:categorical-text`;
- `tests/v3_2_categorical_text_tests.ts`, wired into
  `tests/main_tests.ts`; and
- the new module in the root `src/v3_2/index.ts` development barrel.

The example prints the source text, checked explicit Core, inferred type,
structural prerequisites, equality with the direct TypeScript construction,
and one source-located negative diagnostic. It covers at least:

```text
λ^f x. (H x) (K x)
λ^f x : A. F x y0
F p
```

Focused tests must additionally cover Unicode/ASCII equivalence, multiline
and parenthesized spans, full-input consumption, zero/one/two binder uses,
omitted-annotation recovery from the expected source, explicit-annotation
checking, all frozen error codes that can arise in this slice, foreign terms,
root-only expected-shape forwarding, exact explicit-Core equivalence, and the
absence of Node builtin imports or project dependency/lock changes.

### Exact non-effects

The slice does not:

- modify `CoreCategoricalProgram`, its contextual compiler, or application
  table;
- add a checker, Core node/owner, runtime/proof/unification rule, or semantic
  profile;
- add Parsimmon, `@types/parsimmon`, or any package/lock change;
- support outer-LF or displayed/dependent text binders;
- settle the final repository-wide notation or rewrite provisional Lambdapi
  binder/telescope notation;
- export the located syntax union;
- enter `browser.ts`, `browser_directed.ts`, or the browser fixture;
- add a GitHub Pages workflow, backend, worker, deployment, or publication;
- change Lambdapi source or acquisition; or
- claim general syntax, usability, browser, scale, or whole-transfer
  graduation.

After a separate approval, implementation may make one bounded green local
checkpoint followed by a distinct ledger checkpoint under the existing Git
authority. No broader Git operation is authorized.

## SYNTAX-1A Completion Evidence

The corrected integrated slice is implemented through the existing typed
categorical program and is final-green:

- `src/v3_2/categorical_text.ts` owns only a private located
  identifier/application/lambda tree, cursor parser, immutable typed
  environment, recursive resolver, and source-located adapter diagnostics;
- `λ^f x. body` takes its source from the required expected ordinary-functor
  classifier, while `λ^f x : A. body` resolves and compares `A` before using
  the same expected source;
- `^n`, `^fd`, and `^nd` are parsed as intrinsic modes and rejected with
  `UNSUPPORTED_BINDER_MODE` before any unsupported semantic construction;
- neutral whitespace application delegates each step to the existing
  `program.apply`, and root expected action shape is forwarded only to the
  root application;
- the public barrel, `demo:categorical-text` command, README, and aggregate
  test runner expose the slice without entering the frozen deployed browser
  profile.

Validation:

- focused categorical-text suite: 13 pass, zero fail;
- Unicode and ASCII heads, omitted and explicit annotation, recursive
  open/open and open/closed application, whole-Hom action, zero/one/two use,
  exact spans, all reachable frozen error classes, foreign terms, and
  dependency absence: pass;
- actual `demo:categorical-text`: pass, with exact explicit-Core equality
  against direct TypeScript construction and a source-located negative;
- root typecheck and lint: pass;
- aggregate `check:ts`: 1,127 tests, 1,076 pass, 51 intentional skips, zero
  fail;
- bounded active Lambdapi `make -C emdash2 check`: pass; and
- package dependencies, lockfile, Core/checker/evaluator/action table,
  Lambdapi sources, and browser entries: zero delta.

The aggregate wall time is intentionally not recorded: the user confirmed
that concurrent OBS and other heavy applications made that run atypical.

## Proposed Sequence

```text
SYNTAX-0A architecture audit (complete)
  -> SYNTAX-RESOLVE-0B freeze parser-independent located nodes,
     environment, expected-classifier, and recursive resolver contract
  -> separate D-SYNTAX-001 review
  -> SYNTAX-PARSER-0C compare Parsimmon and tiny-parser spikes (complete)
  -> H-DTTLF-PRODUCT-SYNTAX-02 exact implementation proposal
  -> separate D-DTTLF-PRODUCT-SYNTAX-002 review
  -> SYNTAX-NOTATION-0D apply direct human correction separating
     intrinsic λ^mode from optional : annotation
  -> SYNTAX-1A land tiny parser + located nodes + resolver + example
     together through existing APIs (complete and final-green)
  -> SYNTAX-BROWSER-1B join it to the frozen integrated reviewer proposal
  -> SYNTAX-GRADUATE-1 record the exact supported grammar/usability envelope
     in the runnable integrated reviewer handoff
  -> SYNTAX-PARITY-0A inventory the complete mathematical direct-TypeScript
     target and freeze a bounded ^n/^fd/^nd-first proposal
  -> after exact parity graduation, route to the theorem-led book/repository
     graduation plan; retain bulk scale for a future goal
```

Browser joining remains a separate reviewed product boundary and is now
final-green at `18ca2547bb2f5795127a6589d0531bba87317f19`. The resolver and
parser remain Node-independent input adapters. The next selected task is not
arbitrary grammar expansion: it is measured parity with the existing
mathematical direct-TypeScript construction surface under the dedicated
syntax-parity plan.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| SYNTAX-0A | complete | PRODUCT-DEMO-1B and current contextual programs | Historical parser audit, current semantic-seam inventory, resolver architecture, qualification matrix, and alternatives |
| SYNTAX-RESOLVE-0B | approved exactly as proposed under D-DTTLF-PRODUCT-SYNTAX-001 with human supersession; proposal checkpoint `5e33a58` | SYNTAX-0A and selected product priority | Deeply frozen parser-independent types/API/diagnostic/qualification contract; no standalone runtime AST |
| SYNTAX-PARSER-0C | complete | D-DTTLF-PRODUCT-SYNTAX-001 | Parsimmon and tiny-parser parsed/rejected the same corpus; both browser-build; measurements above select the dependency-free tiny parser |
| SYNTAX-NOTATION-0D | complete as direct human correction D-DTTLF-PRODUCT-SYNTAX-003; synchronization active | approved D-DTTLF-PRODUCT-SYNTAX-002 implementation, before its runtime checkpoint | Intrinsic `λ^mode`, optional checked `: annotation`, expected-source recovery, mode-specific semantic gates, and deferred repository-wide notation consolidation |
| SYNTAX-1A | complete and final-green at `7513cbe9e0d1439b5b1250982f40cede48e9a811` under D-DTTLF-PRODUCT-SYNTAX-002 as corrected by direct human D-DTTLF-PRODUCT-SYNTAX-003; proposal checkpoint `6766eba` | parser-selection/implementation review and SYNTAX-NOTATION-0D | Tiny parser, private located-node implementation, immutable environment, recursive ordinary categorical resolver, tests, and executable example landed as one user-visible slice |
| SYNTAX-BROWSER-1B | final-green under D-DTTLF-PRODUCT-REVIEWER-001/002/003 at `18ca2547bb2f5795127a6589d0531bba87317f19` | reviewed parser plus measured browser profile | Editable ordinary categorical input in the integrated reviewer without a second checker or server |
| SYNTAX-GRADUATE-1 | documentation and runnable product scope final-green at `18ca2547bb2f5795127a6589d0531bba87317f19` | selected syntax rows | Exact grammar, intrinsic-mode/optional-annotation boundary, binder/action matrix, diagnostics, browser interaction, and deferrals |
| SYNTAX-PARITY-0A | complete at `d73195b`; separately reviewed under D-DTTLF-PRODUCT-SYNTAX-PARITY-001 at `55161be` | current direct TypeScript construction surface | Executable 68-method/14-capability API-to-text inventory, deterministic routing classification, equivalence/negative corpus, and bounded `^n`/`^fd`/`^nd`-first proposal |
| SYNTAX-PARITY-1A | final-green at `2e7cc3c44802a5218858ca6747e7591d3bfc4859` | approved parity D001 review | Intrinsic `^n`, `^fd`, `^nd`, optional checked category/family annotation, direct-builder routing, recursive typed `composeCells`, exact diagnostics, six integrated-reviewer presets, and a zero-failure 1,149-test aggregate |
| SYNTAX-PARITY-1B | pending separate bounded proposal/review | completed `SYNTAX-PARITY-1A` | Nested/dependent contexts plus displayed/fibred structural forms, including the textual `indexOf` seam required by weakening |
| BOOK-DELTA-0A | selected after syntax-parity graduation | exact text/direct-TypeScript boundary | Hand the completed syntax envelope to the dedicated theorem-led book/repository graduation plan |

## Clarified Parity And Internalization Boundary

The new parity target is every mathematical construction already exposed by
the direct typed TypeScript API, not arbitrary JavaScript callback control
flow. Grammar parsing remains deterministic. A valid located term may still
fail during typed resolution or recursive categorical factorization.

No semantic heuristic is selected:

- subject, argument, binder mode, and expected classifiers choose existing
  application judgments;
- unresolved ambiguity requires an annotation or produces a diagnostic;
- current `^fd`/`^nd` factorers recognize finite recursive grammars of
  internally coherent constructors; and
- general discovery of a naturality proof for arbitrary pointwise data is
  outside the parser.

The existing `CoreCategoricalAbstractionEvidence` records lowering,
occurrence, selected-rule, and prerequisite trace data. It is not an
externally supplied coherence premise. The dedicated parity plan makes this
terminology and the parse/elaborate/factor distinction normative for the next
audit.

## Feasibility Assessment

The architecture is feasible and no kernel redesign is indicated:

- callback-bound tokens already give hygienic recursive occurrences;
- the contextual IR already stores first-order usage and provenance;
- `apply` already classifies ordinary and reviewed displayed actions;
- direct typed constructors prove the target semantic path; and
- every parser node can carry an exact source span.

The low-risk work is tokenization, names, spans, ordinary application chains,
and routing into already supported constructors. The material risks are:

- target/expected classifier design for categorical lambdas;
- syntax for layer versus variation without overloading `^o`;
- honest representation of bounded rather than arbitrary `^fd`/`^nd`;
- contravariant and higher-action ambiguity;
- dependent telescope family resolution under earlier bindings; and
- keeping a parser library choice from hardening into a second semantic AST.

These risks are localized frontend API questions. They do not falsify the LF,
categorical kernel, or contextual-compilation architecture.

## Exact Non-Effects

Until a later row is separately approved, this plan adds no:

- parser dependency, lockfile change, or exported located syntax;
- new checker, unifier, evaluator, Core node, owner, or rule;
- new categorical binder capability;
- arbitrary-depth displayed or general `^nd` claim;
- Lambdapi-source acquisition parser;
- browser promotion; or
- scale-graduation claim.

## Git Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Existing authority permits bounded green local checkpoint commits only in
the dedicated goal branch/worktree after exact staged-diff inspection and
ledger synchronization.

No push, merge, PR, publication, release, rebase, amend, reset, history
rewrite, branch/worktree deletion, or unrelated cleanup is authorized.

## Persistent `/goal` Launch Prompt

```text
Continue the next dependency-ready reviewed row routed by
docs/TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md and, after the integrated
reviewer checkpoint,
docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md, then
docs/TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md, while
retaining the product, usability, fibred-context, future scale, and handoff
plans as authority and recovery context.

Treat usability as recursive typed variable occurrence and type-directed
categorical action, not merely tokenization. Preserve direct typed TypeScript,
the existing scoped LF builder, categorical contextual compiler,
backend-neutral explicit Core, and single checker/evaluator.

A text frontend may use a small located name-bearing syntax representation,
but it must resolve recursively into existing typed programs and must not own
definitional equality, action semantics, Core owners, or a second checker.
Keep the host environment immutable and typed, propagate exact source spans,
require expected information where the existing sound API needs it, and fail
closed on ambiguity or unsupported profile shapes.

Keep intrinsic abstraction capability (`λ^f`, `λ^n`, `λ^fd`, `λ^nd`) separate
from an optional checked domain/family annotation. Do not infer the capability
from an expected classifier, and do not claim the experimental TypeScript
spelling has already standardized informal Lambdapi/kernel notation.

Treat syntax parity as parity with mathematical direct-TypeScript
constructions, not arbitrary JavaScript behavior. Keep parsing deterministic,
route applications through existing classifier-directed programs, and keep
internal factorization separate from parsing. Do not guess naturality or
conflate user syntax with Lambdapi-source acquisition.

After parity graduation, update the book and repository presentation through
their dedicated reader-facing plan. Keep bulk scale qualification pending for
a future goal rather than resuming it automatically.

The user's standing unattended delegation permits separate approval of a
narrowly frozen dependency-ready proposal after no immediate response, with
human supersession and the Git checkpoint SOP. It does not authorize a
broader grammar, semantic feature, dependency, browser, or Git effect.
```

## Change Log

- **2026-07-30 — Reader-facing successor recorded.** Exact syntax parity now
  hands the current product goal to the theorem-led book/repository graduation
  plan. Remaining bulk scale rows stay pending for a future goal.
- **2026-07-30 — Direct-TypeScript syntax parity selected next.** The user
  clarified that after the integrated reviewer and before deferred bulk scale,
  text should be synchronized with mathematical constructions already exposed
  by the target TypeScript API, especially `^n`, `^fd`, and `^nd`. Added a
  dedicated audit/plan route. Parsing is deterministic; typed resolution and
  internal factorization may reject valid syntax without heuristic action or
  naturality synthesis.
- **2026-07-30 — SYNTAX-BROWSER-1B promoted into the integrated reviewer.**
  The user's direct product clarification supersedes indefinite browser
  deferral for the already final-green ordinary `^f` adapter. The measured
  combined Vite/Chromium probe succeeds after isolating Node-only acquisition
  hashing. The new proposal changes no grammar or semantic action; displayed
  modes and final notation remain gated.
- **2026-07-29 — SYNTAX-GRADUATE-1 completed through the product handoff.**
  The approved documentation-only D-DTTLF-PRODUCT-GRADUATE-001 row exposes
  the exact ordinary `^f` command and input examples, separates direct typed
  displayed consumers from unsupported displayed text, records
  `^n`/`^fd`/`^nd` as fail-closed, and preserves both browser joining and final
  TypeScript/Lambdapi notation as deferred. No syntax or runtime behavior
  changed.
- **2026-07-29 — Corrected SYNTAX-1A implemented and final-green.** Added the
  dependency-free private located parser and recursive resolver, root export,
  `demo:categorical-text`, focused tests, aggregate wiring, and user-facing
  documentation. The exact ordinary inputs `λ^f x. (H x) (K x)` and
  `λ^f x : A. F x y0` compile identically to their direct TypeScript
  witnesses; `G p` follows the existing expected whole-Hom action. Thirteen
  focused tests, typecheck, lint, the actual demo, the 1,127-test aggregate,
  and bounded active Lambdapi check pass. No dependency/lock, Core/checker/
  evaluator/action-table, Lambdapi, or browser-entry delta occurred. Exact
  local implementation checkpoint:
  `7513cbe9e0d1439b5b1250982f40cede48e9a811`.
- **2026-07-29 — D-DTTLF-PRODUCT-SYNTAX-003 human correction recorded.**
  During the uncommitted SYNTAX-1A implementation, the user clarified that
  functorial, natural, displayed-functorial, and displayed-natural capability
  belongs intrinsically on the abstraction head (`λ^f`, `λ^n`, `λ^fd`,
  `λ^nd`), whereas `: A` is a separate generally optional annotation. Updated
  the experimental TypeScript grammar and resolver contract so the existing
  expected ordinary-functor classifier supplies an omitted source and checks
  an explicit one. This does not implement the deferred modes or settle the
  final cross-environment notation; earlier informal `x :^mode A` evidence is
  preserved rather than bulk rewritten.
- **2026-07-29 — D-DTTLF-PRODUCT-SYNTAX-002 recorded.** After no immediate
  objection to the exact checkpointed implementation proposal, applied the
  user's standing unattended delegation with human supersession. The
  separate immutable review authorizes only the integrated dependency-free
  ordinary categorical text slice and its bounded green local checkpoints.
- **2026-07-29 — SYNTAX-PARSER-0C completed and SYNTAX-1A proposed.**
  Disposable Parsimmon and direct recursive-descent parsers produced the same
  syntax and failure offsets over the frozen corpus and both Vite-built for a
  browser. Parsimmon used less source, while the tiny parser required no
  dependencies or typings, emitted 856 bytes gzip versus 7,094 bytes, and
  gives direct stable-diagnostic control. Selected the tiny parser for the
  first slice and froze H-DTTLF-PRODUCT-SYNTAX-02 /
  D-DTTLF-PRODUCT-SYNTAX-002 around one integrated parser/resolver/example
  implementation. No production code or package change is yet authorized.
- **2026-07-29 — D-DTTLF-PRODUCT-SYNTAX-001 recorded.** After no immediate
  objection to the exact checkpointed proposal, applied the user's standing
  unattended delegation with human supersession. The separate immutable
  review authorizes only disposable parser comparison and a later frozen
  implementation proposal; it selects no parser and adds no runtime code or
  dependency.
- **2026-07-29 — SYNTAX-RESOLVE-0B frozen as
  H-DTTLF-PRODUCT-SYNTAX-01.** Converted the audit into an exact ordinary
  categorical first-slice contract: identifiers, parentheses, neutral
  whitespace application, and one `:^f` abstraction; request-local typed
  bindings; explicit expected routing; recursive resolution through the
  existing program; exact spans; and direct-TypeScript equivalence tests.
  Corrected the sequencing so a located tree/resolver cannot land as dormant
  infrastructure: the selected parser, nodes, resolver, tests, and executable
  example must enter together after a disposable parser comparison and a
  separate implementation review. This proposal selects no parser or
  dependency and changes no runtime behavior.
- **2026-07-29 — SYNTAX-0A completed.** Compared the historical Parsimmon
  grammar with the active scoped LF builder and categorical contextual
  programs. Selected a parser-independent located syntax plus recursive
  resolver as the only acceptable text boundary, with an immutable typed
  host environment and expected-classifier seam. Recorded silent-application,
  binder-capability, dependent-telescope, source-span, and qualification
  requirements. Parsimmon versus a tiny parser remains a measured later
  choice; no implementation, dependency, or semantic change is authorized.
