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
SYNTAX-RESOLVE-0B is the next proposal boundary; the contract below freezes
design and qualification requirements, but no located tree or resolver may
land as unused runtime infrastructure before the selected parser joins it in
one separately reviewed user-visible vertical slice

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
- bounded direct `displayedFunctorLambda` (`:^fd`-equivalent); and
- bounded coherent `displayedTransforLambda` (`:^nd`-equivalent).

The underlying first-order contextual IR already contains slot references,
closed Core terms, typed application, typed pair, cell composition,
categorical abstraction, classifiers, free-slot usage, and provenance. Its
recursive compiler generates explicit structural/action terms and fails
closed when the requested action is outside the active profile.

The ordinary compiler already handles the important nontrivial form:

```text
λ x :^f A. F x y0
```

where `x` occurs inside the subject of an inner application and `y0` is
closed. It lowers recursively through evaluation, product pairing, identity,
and constant structure. No explicit source-level bracket around `F x` is
needed.

The displayed compiler now handles independent siblings, stable evaluation,
one genuine dependency edge, the exact `a; b,c; d` mixed telescope, recursive
coherent component composition, and one next-Hom observation. These are real
but bounded capabilities; syntax must not advertise arbitrary depth, arbitrary
mixed variance, or general `:^nd` coherence.

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

### Binder notation is capability syntax, not a Core-owner enumeration

Provisional forms such as:

```text
λ x :^o X. body
λ a :^f A. body
λ k :^n K. body
λ a :^fd E. body
λ k :^nd K. body
```

combine abstraction layer, plicity, variation, polarity, cell level, and
displayed dependency. They do not each name a primitive Core binder or one
kernel owner. In particular:

- outer-LF binding and categorical object-only capability must not be
  conflated merely because a draft spelling uses `o`;
- `:^fd` lowers through coherent displayed-functor construction, not a
  pointwise family of arbitrary functions;
- `:^nd` accepts only the reviewed coherent envelope and cannot synthesize
  missing naturality from point data; and
- owners such as `fapp*_func`, `tapp*_func`, evaluation, and internalized Hom
  contribute action cases but do not automatically define new binder modes.

The exact spelling remains revisable independently of the semantic adapter.

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
   `λ x :^f A. (H x) (K x)`;
2. ordinary open/closed nested evaluation:
   `λ x :^f A. F x y0`;
3. one displayed dependency edge with recursive outer and inner occurrences:
   `λ a :^fd A. λ b :^fd B(a). FF[a]`;
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
expression  ::= lambda | application
lambda      ::= ("λ" | "\\") identifier ":^f" identifier "." expression
application ::= atom atom*
atom        ::= identifier | "(" expression ")"
```

Whitespace between atoms creates one neutral left-associated application
spine. The parser never emits `fapp*`, `tapp*`, evaluation, pairing, weakening,
contraction, or exchange owner names.

This slice supports one outer `:^f` lambda per elaboration request and
arbitrarily recursive identifier/application/parenthesis subexpressions in
its body. A syntactically nested lambda is parsed, then rejected with an exact
unsupported-expectation diagnostic until a recursive expected-classifier
contract is separately frozen. This restriction does not prevent the first
slice from qualifying:

```text
λ x :^f A. (H x) (K x)
λ x :^f A. F x y0
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

For a lambda request, the parsed annotation must resolve to the exact source
category supplied by the `ordinary-functor` expectation; the expectation
supplies the target category already required by `program.lambda`. Category
agreement uses the existing program comparison/checking boundary, not label
equality. A lambda under `kind: 'term'`, an application/identifier under an
inapplicable functor expectation, or a nested lambda without a reviewed
recursive expectation fails closed.

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

Displayed `:^fd`/`:^nd`, dependent telescopes, outer-LF text, let/Pi/holes,
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

## Proposed Sequence

```text
SYNTAX-0A architecture audit (complete)
  -> SYNTAX-RESOLVE-0B freeze parser-independent located nodes,
     environment, expected-classifier, and recursive resolver contract
  -> separate D-SYNTAX-001 review
  -> SYNTAX-PARSER-0C compare Parsimmon and tiny-parser spikes
  -> separate parser-selection review
  -> SYNTAX-1A land selected parser + located nodes + resolver + example
     together through existing APIs
  -> SYNTAX-BROWSER-1B optionally join it to a reviewed browser profile
  -> SYNTAX-GRADUATE-1 record the exact supported grammar/usability envelope
```

Browser joining is deliberately later. The resolver and parser should be
Node-independent, but a browser UI is a separate product boundary.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| SYNTAX-0A | complete | PRODUCT-DEMO-1B and current contextual programs | Historical parser audit, current semantic-seam inventory, resolver architecture, qualification matrix, and alternatives |
| SYNTAX-RESOLVE-0B | proposed as H-DTTLF-PRODUCT-SYNTAX-01 / D-DTTLF-PRODUCT-SYNTAX-001 | SYNTAX-0A and selected product priority | Deeply frozen parser-independent types/API/diagnostic/qualification contract; no standalone runtime AST |
| SYNTAX-PARSER-0C | gated | separate review of 0B | Disposable Parsimmon versus tiny-parser measurement over identical syntax/span tests; no tracked losing spike |
| SYNTAX-1A | gated | separate parser-selection/implementation review | Selected parser, located-node implementation, immutable environment, recursive ordinary categorical resolver, tests, and executable example land as one user-visible slice |
| SYNTAX-BROWSER-1B | deferred | reviewed parser and browser profile | Editable browser input without a second checker or server |
| SYNTAX-GRADUATE-1 | pending | selected syntax rows | Exact grammar, binder/action matrix, diagnostics, performance observation, and deferrals |

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
- syntax for layer versus variation without overloading `:^o`;
- honest representation of bounded rather than arbitrary `:^fd`/`:^nd`;
- contravariant and higher-action ambiguity;
- dependent telescope family resolution under earlier bindings; and
- keeping a parser library choice from hardening into a second semantic AST.

These risks are localized frontend API questions. They do not falsify the LF,
categorical kernel, or contextual-compilation architecture.

## Exact Non-Effects

Until a later row is separately approved, this plan adds no:

- dependency or lockfile change;
- parser or exported located syntax;
- new checker, unifier, evaluator, Core node, owner, or rule;
- new categorical binder capability;
- arbitrary-depth displayed or general `:^nd` claim;
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
docs/TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md, while retaining the
product, usability, fibred-context, scale, and handoff plans as authority and
recovery context.

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

Do not select Parsimmon, a hand-written parser, tagged templates, or browser
joining before the applicable measured row and separate review. Do not
conflate user syntax with Lambdapi-source acquisition.

The user's standing unattended delegation permits separate approval of a
narrowly frozen dependency-ready proposal after no immediate response, with
human supersession and the Git checkpoint SOP. It does not authorize a
broader grammar, semantic feature, dependency, browser, or Git effect.
```

## Change Log

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
