# TypeScript/emdash Structures, Classes, And Instance Synthesis Plan

Date: 2026-08-08

Plan-ID: TS-EMDASH-CLASSES

Status: active living architecture and implementation ledger; STRUCT-PARAM-1
and STRUCT-NAMED-2 are final-green; the exact CLASS-SCHEMA-3 contract is
frozen and approved for implementation

Branch: `goal/typescript-emdash-classes-v1`

Worktree: `/home/user1/emdash1-classes-v1`

Baseline: `66a61edb6299671934871ba468b4004ec077ecdf`
(`elaborator: graduate AI-native local foundation`)

## Executive Decision

The selected target is a **Lean-comparable authoring envelope over explicit
emdash Core**, not a clone of Lean's parser, kernel, tactic framework, or
inductive-declaration machinery.

Structures, classes, inheritance, instance declarations, named scopes, and
instance synthesis are direct-TypeScript management and elaboration features.
They lower to ordinary parameterized declarations, constructors, projections,
rewrite rules, and explicit dictionary arguments. They add no class,
structure, inheritance, or synthesis constructor to trusted Core. The small
TypeScript checker/evaluator remains unaware of typeclasses and checks the
fully explicit result. Deterministic Lambdapi emission remains an optional
conformance route rather than the production implementation of search.

The intended architecture is:

```text
typed *.emdash.ts declarations and proof source
                       |
        structure/class schemas + immutable scopes
                       |
        deterministic bounded evidence synthesis
                       |
             explicit, meta-free Core
                 /             \
      TypeScript checker    optional Lambdapi emitter/oracle
```

This is the practical compatibility target: an ordinary Lean development
whose organization depends on parameterized records, class hierarchies, local
instances, superclass inference, priorities, and recursive instance premises
should translate directly at the semantic level. Its declarations are written
with typed TypeScript builders rather than parsed Lean declaration text.

## Goal

Make TypeScript/emdash practical for AI-authored multi-file proof
developments by supplying:

- parameterized and dependent structures;
- stable named-field construction and projection handles;
- classes as structures plus search metadata;
- multiple inheritance with canonical shared ancestors;
- portable local, imported, global, and named instance scopes;
- deterministic recursive synthesis with complete traces;
- general call elaboration that inserts evidence at class-marked implicit
  binders; and
- publishable packages and hosted research-workspace integration after the
  local semantic boundary is qualified.

An AI agent should normally see a compact `synth(...)` request in source and
be able to inspect a stable resolution trace when it is nontrivial. The
checked artifact must contain the selected explicit dictionary term, so no
long-lived editor, MCP server, process registry, or hidden search state owns
proof meaning.

## Governing Authorities

Read and preserve these authorities in order:

1. `emdash2/emdash3_2.lp`, the active mathematical and computational
   specification;
2. the active extensions and workflow in `emdash2/AGENTS.md`;
3. `emdash2/emdash3_2_checks.lp`;
4. `emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
5. `emdash2/reports/EMDASH_FOUNDATIONS.md`;
6. `emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
7. `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and the active plans it
   routes to;
8. `docs/TYPESCRIPT_EMDASH_AI_NATIVE_WORKSPACE_AND_PROOF_PLAN.md` for the
   explicit-Core, source/artifact, workspace, and synthesis boundaries;
9. `docs/RECORD_STRUCTURE_USABILITY_V3_2_PLAN.md` for the completed
   unparameterized dependent-structure slice; and
10. this plan for the forward structures/classes/synthesis implementation.

The stale category-specific root prototype is implementation evidence only.
It must not become a second v3.2 mathematical authority, and the retired
`D0`/`D1` compatibility API must not be recreated.

## Reviewed Baseline

### Structure macro

`src/v3_2/lf_structure_macro.ts` already provides a useful outer-LF macro:

- a callback-once direct-TypeScript field builder;
- dependent field types referencing earlier fields;
- one opaque carrier and one injective constructor;
- named projections;
- one ordered subject-reducing runtime beta per projection;
- deterministic Lambdapi fragment emission; and
- fail-closed scope, provenance, collision, forward-reference, and escaped-
  binder diagnostics.

Its carrier is currently always declared at `TYPE`. The constructor returns
the bare carrier, projections accept the bare carrier, and the runtime beta
patterns carry only field captures. Structure parameters are therefore a
real missing semantic layer, not a spelling change.

### Dictionary synthesis

`src/v3_2/lf_dictionary_synthesis.ts` deliberately implements a much smaller
contract than typeclass search:

- the caller supplies the complete finite candidate list;
- the target is closed and meta-free;
- candidates are exact installed free declarations;
- every candidate is independently checked;
- zero matches is missing, one match succeeds, and multiple matches are a
  hard ambiguity; and
- there is no discovery, recursive premise search, scope hierarchy, priority,
  backtracking, local binder evidence, or process I/O.

`src/v3_2/lf_dictionary_authoring.ts` derives and fills only the first leading
implicit binder of one global call. It is evidence that synthesis can remain
outside Core, but it is not the eventual general call elaborator.

### AI-native boundary

The completed AI-native foundation already establishes the correct product
contract:

- canonical source is a reviewable file;
- verified state is deterministic derived evidence;
- explicit Core is the semantic boundary;
- transport such as MCP, HTTP, browser, or hosted execution is optional;
- easy transitions remain compact; and
- difficult transitions expose stable diagnostics and traces.

This plan extends that boundary; it does not replace it.

### Lean reference semantics

The local Lean 4 source at `/home/user1/lean4-source-code` and the official
reference establish the user-facing comparison target:

- a class is structurally close to a structure but is registered for
  synthesis;
- class parents and method receivers use instance-implicit arguments;
- structures may be parameterized and dependent;
- inheritance separates physical parent representation, ancestral field
  identity, generated parent projections, and name-resolution order;
- overlapping diamonds share ancestor data rather than duplicating it;
- C3 linearization controls inherited name/default resolution;
- instance search is indexed, recursive, scoped, priority-aware, tabled, and
  bounded; and
- input, output, and semi-output parameter roles influence when search may
  proceed.

Relevant primary references:

- <https://lean-lang.org/doc/reference/latest/Type-Classes/Class-Declarations/>
- <https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/>
- <https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/>
- <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/>
- <https://lean-lang.org/doc/api/Lean/Structure.html>

Lean is a behavioral comparison and acceptance-corpus source. Its parser,
implementation layout, recency tie-breaks, tactic infrastructure, and kernel
are not imported architecture.

### Lambdapi/Elpi reference

Deducteam/Lambdapi PRs
[#1378](https://github.com/Deducteam/lambdapi/pull/1378) and
[#418](https://github.com/Deducteam/lambdapi/pull/418) validate one important
partition: class and instance metadata may feed a separate proof-search
engine which fills implicit evidence, while the logical framework receives
ordinary terms. They may later inform an optional Elpi provider or
conformance experiment.

They do not supply the selected TypeScript product implementation. The
TypeScript resolver must work without Lambdapi or Elpi and must emit explicit
evidence before either backend is invoked.

## Non-Goals

This plan does not authorize or promise:

- parsing structure, class, instance, inductive, or theorem declarations;
- a Lean source parser or Lean binary/API compatibility;
- a new Core node or trusted checker branch for records or typeclasses;
- a process-global mutable instance registry;
- treating `unif_rule` as a typeclass engine;
- a general Prolog engine or unbounded theorem search;
- a general end-user `inductive` declaration frontend;
- positivity checking, generated eliminators, generated recursion, or
  automatic deriving;
- Lean tactic compatibility;
- accidental same-name field merging;
- order-sensitive silent choice between genuinely distinct equal-ranked
  solutions;
- arbitrary rewrite rules being classified as safe merely because they
  typecheck; or
- mandatory Lambdapi, MCP, network, or hosted execution.

## Mechanism Partition And Trust Boundary

Keep three mechanisms distinct:

1. **Runtime rewrite/computation** is part of the explicit checked module and
   evaluator semantics.
2. **Proof-time unification rules** influence conversion/unification at their
   reviewed owners.
3. **Instance synthesis** searches a finite immutable registry snapshot for a
   term, then submits the selected explicit term to the ordinary checker.

Instance search cannot certify a term. Registration validates provider types;
resolution constructs evidence; the Core checker remains the authority for
the result. Search traces and TypeScript types are ergonomic evidence only.

## Architecture

### A. Parameterized dependent structures

Extend the existing callback-once builder with parameters declared before
fields. A parameter has:

- a stable ordinal and binder name;
- a type which may depend only on earlier parameters;
- an explicit carrier binder mode;
- an explicit constructor binder mode; and
- an explicit projection binder mode.

The separate modes are intentional. They prevent the macro from assuming
that the carrier, constructor, and projections quantify a parameter with the
same plicity or variance. The carrier-result application always follows the
carrier binder plicity.

The generated package is:

```text
carrier    : Π carrier-parameters, TYPE
constructor:
  Π constructor-parameters, Π fields, carrier carrier-parameters
projectionᵢ:
  Π projection-parameters,
  Π record : carrier carrier-parameters,
  field-typeᵢ[parameters, earlier projections record]

projectionᵢ parameters
  (constructor parameters fields)  ↪  fieldᵢ
```

Parameter and field dependencies are lowered locally-namelessly for each
generated context. Runtime-rule variables include parameter captures followed
by field captures, with their dependent types reconstructed in source order.
Unparameterized callers remain exact.

The macro must continue to generate no eta, eliminator, recursion principle,
positivity claim, source inductive node, or hidden kernel declaration.

### B. Named construction and private layout

Add a named construction helper after parameterization is stable. It accepts
parameter applications plus a field map keyed by stable field handles, checks
that every required field appears exactly once, orders the arguments
canonically, and returns an ordinary constructor application.

Generated constructor position is not a durable public record layout. This
allows inheritance storage to evolve without breaking authoring source.

### C. Class schemas

A class is a parameterized structure plus immutable authoring metadata:

- stable class ID and generated structure handle;
- parameter roles (`input`, later `output` and `semi-output`);
- stable field/method IDs;
- direct-parent specifications and substitutions;
- canonical ancestor identities and projection terms; and
- generated superclass instance providers.

An instance-implicit source binder remains an ordinary implicit Core binder
plus metadata consumed by the call elaborator. Core plicity remains
`explicit | implicit`; no third trusted binder kind is needed.

### D. Multiple inheritance and ancestor sharing

The first representation semantically flattens an inheritance graph into one
canonical field telescope:

- each ancestral field identity has one canonical slot;
- a field identity is based on its declaring schema and stable field ID, not
  spelling alone;
- generated conversions reconstruct direct and transitive parents from those
  slots;
- every route through a diamond reconstructs a common ancestor from the same
  slots; and
- generated representation remains private.

C3-style linearization determines inherited unqualified name lookup and later
default resolution. An inconsistent hierarchy fails closed. Unrelated
same-spelled fields require qualification, renaming, or an explicit
`share`/`identify` declaration whose types are definitionally checked. A
Lean-translation helper may turn compatible same-name overlap into that
explicit mapping, but the core schema never merges by spelling accidentally.

Superclass providers are generated only for nonredundant canonical ancestor
paths. Distinct diamond paths must normalize to the same evidence or be
designated as the same canonical ancestor provider.

### E. Portable instance declarations and scopes

An instance declaration records checked immutable metadata:

- stable provider ID and provenance;
- generic ordinary parameters;
- recursively synthesized instance premises;
- result class head;
- priority;
- visibility and named scope; and
- explicit provider term or term builder.

Search receives a registry snapshot and an explicit scope. The scope contains
lexical/local evidence, explicitly opened named scopes, imported providers,
and global providers. It never discovers candidates by enumerating mutable
host state.

The initial precedence is:

```text
local > explicitly opened/named > imported/global
```

Within a tier, higher priority is considered first. A deterministic provider
ID orders diagnostics but does not silently decide between two genuinely
different equal-ranked successes.

### F. Deterministic recursive resolver

Resolution should:

1. validate the target class application and input-role readiness;
2. index candidates by exact class head;
3. unify a provider result with the requested target;
4. instantiate its ordinary parameters;
5. recursively solve its instance premises in the same immutable scope;
6. assemble an explicit provider application;
7. check the result against the target; and
8. return the term plus a complete stable trace.

The resolver is tabled by normalized goal plus scope fingerprint, detects
cycles, and enforces explicit depth/size/fuel bounds. Public outcomes are:

```text
solved | missing | stuck | ambiguous | limit-exceeded
```

Distinct equal-ranked successful evidence is ambiguous unless the terms are
definitionally equal or are canonical projections of the same shared
ancestor. Higher priority may intentionally select one provider. Explicit
arguments and explicit scope control remain the escape hatch.

Implement all-input matching first. Design parameter-role metadata from the
start, but defer output/semi-output inference and stuck/resume behavior until
an exact consumer requires them.

### G. General call elaboration

Replace the leading-only dictionary helper with a binder-walking elaborator
which:

- consumes explicit and ordinary implicit arguments;
- substitutes each accepted argument into later binder types;
- recognizes class-marked implicit binders at arbitrary positions;
- creates a source-visible synthesis request;
- resolves it under the supplied scope; and
- returns one ordinary explicit Core application plus synthesis traces.

Canonical source may retain compact `synth(...)` requests. Canonical checked
artifacts retain the selected explicit evidence. No unresolved search request
crosses the Core-checker boundary.

### H. Curated inductives and HITs

The proof assistant may expose useful inductive types and directed or
categorical HITs without implementing a general inductive declaration
frontend.

Curated standard-library packages should carry versioned declarations,
constructors, eliminators, computation rules, provenance, digests, and
available metatheoretic evidence. Natural numbers, finite families, equality,
lists/options where needed, truncations, quotients, and selected categorical
HITs are library artifacts rather than products of a universal command.

Expert users may add hand-written outer-LF declarations and rewrite rules
under an explicit `trusted-extension`/`unsafe-extension` profile. The profile
must state that successful checking does not by itself establish consistency,
confluence, normalization, positivity, or semantic justification.

### I. Package boundary

Do not publish the private repository-root workbench. The unscoped npm name
`emdash` is already occupied by an unrelated package. Subject to npm scope
ownership, the first distributable boundary should be:

- `@emdash/core`: browser-safe Core, checker/evaluator, and curated public
  subpath exports such as `./authoring` and `./workspace`;
- `@emdash/cli`: Node workspace/check/artifact commands; and
- later `@emdash/stdlib`: versioned curated inductive/HIT/algebra/category
  artifacts.

Packages contain built JavaScript and `.d.ts` files, use a strict public
export map, do not require `ts-node`, and pass a packed-install consumer test.
Publishing uses npm trusted publishing/OIDC and provenance. A git-ignored
token is neither moved nor read as part of normal publication.

### J. GetPaidX/LastRevision and Arrowgram

`emdash1` owns proof semantics, packages, and checked artifacts.
`closerfans` owns GetPaidX/LastRevision hosted files, workspace lifecycle,
runtime/build/publish operations, and additive/versioned MCP/API adapters.
`arrowgram` owns diagram and research-document rendering which consumes
emdash artifacts.

The first hosted template should be a pure-TypeScript
`emdash_research_workspace` or `emdash_proof_workspace`. The existing
GetPaidX controller images use Node 20 while this workspace requires Node
22.13 or newer; use a compatible new controller/template boundary rather than
silently breaking existing templates. A Lambdapi-equipped profile is optional
for conformance and advanced development, not required for ordinary hosted
checking.

Published or in-review MCP operations must remain compatible. Proof-oriented
operations are additive, versioned adapters over generic source read/write,
check, and artifact retrieval. Files, locks, and content-addressed artifacts
remain authoritative rather than MCP session state.

Cross-repository implementation starts only after the local package and a
packed consumer are green. Each sibling repository gets its own status/SOP
inspection and branch before edits.

## Lean-Comparable Compatibility Matrix

| Capability | Target | Boundary |
| --- | --- | --- |
| Parameterized/dependent structures | first-class | direct TS macro to ordinary LF declarations |
| Named record construction/projections | first-class | authoring helpers; private generated layout |
| Classes and methods | first-class | structure plus metadata; explicit Core evidence |
| Multiple inheritance | first-class | strict C3 lookup plus canonical flattened slots |
| Shared diamond ancestors | first-class | one ancestral identity and canonical conversions |
| Local/global/named scoped instances | first-class | immutable explicit registry snapshots |
| Recursive instance premises | first-class | bounded tabled resolver |
| Priorities | first-class | tier then numeric priority |
| Ambiguity diagnostics and traces | first-class | stable machine-readable evidence |
| Output/semi-output parameters | later | metadata now; inference after all-input search |
| Defaults and record updates | later | named-layout authoring layer |
| Default instances/coercions | later | consumer-gated separate policies |
| Declaration text parsing | non-goal | expressions/terms only may use text parsing |
| General inductive declarations | non-goal | curated stdlib plus explicit trusted extensions |
| Lean tactics/ABI/source compatibility | non-goal | semantic authoring compatibility only |

## First Acceptance Corpus

The first end-to-end hierarchy is the algebraic diamond:

```text
Mul α
One α
Semigroup α extends Mul α
MulOneClass α extends Mul α, One α
Monoid α extends Semigroup α, MulOneClass α
```

It must demonstrate:

- parameterized structures and classes;
- multiple inheritance;
- exactly one shared `Mul α` ancestor;
- named-field construction;
- generated direct and transitive parent projections;
- a local `Monoid α` dictionary synthesizing `Semigroup α`,
  `MulOneClass α`, `Mul α`, and `One α`;
- definitionally equal or canonical evidence for both diamond routes to
  `Mul α`;
- at least one generic provider with a recursive instance premise;
- stable missing, ambiguity, cycle, and bounded-search traces; and
- explicit generated Core accepted by the TypeScript checker.

After that synthetic acceptance corpus, `struct_cov_sieve` is the first
mathematical consumer of parameter modes. Category/Functor/Adjunction class
consumers come later because multiple legitimate structures on one carrier
make explicit local scope discipline especially important.

## Implementation Ledger

| Row | State | Dependency-ready outcome |
| --- | --- | --- |
| ARCH-0 | complete | Architecture, comparison target, trust boundary, non-goals, and acceptance corpus recorded here. |
| STRUCT-PARAM-1 | complete | The existing macro now has dependent parameter telescopes and explicit carrier/constructor/projection modes while preserving unparameterized declarations, rules, order, and emission. |
| STRUCT-NAMED-2 | complete | Stable owner-aware handles and order-independent named parameter/field assignments now lower to one deeply frozen ordinary constructor call. |
| CLASS-SCHEMA-3 | in progress | The audited schema-only contract is frozen and approved; implement serializable class/parameter/method/ordered-parent metadata while parentful layouts remain explicitly unlowered. |
| CLASS-INHERIT-4 | pending | Add strict C3 lookup, canonical field identities, explicit sharing, and algebraic-diamond conversions. |
| SYNTH-SCOPE-5 | pending | Add immutable provider declarations and local/named/imported scope snapshots. |
| SYNTH-RECURSE-6 | pending | Add exact-head recursive tabled search, priorities, limits, ambiguity policy, and traces. |
| CALL-SYNTH-7 | pending | Generalize call elaboration to arbitrary class-marked implicit binders. |
| ALGEBRA-GRADUATE-8 | pending | Qualify the complete algebraic diamond and one recursive provider. |
| MATH-CONSUMER-9 | pending | Qualify `struct_cov_sieve`, then select one category/Functor/Adjunction consumer. |
| PARAM-ROLES-10 | gated | Add output/semi-output and stuck/resume only after an exact consumer audit. |
| STDLIB-11 | gated | Define curated inductive/HIT artifact and trusted-extension profiles. |
| PACKAGE-12 | gated | Publishable `@emdash/*` package boundaries and packed-consumer evidence. |
| HOSTED-13 | gated | Add compatible GetPaidX template/API adapters and Arrowgram consumption after PACKAGE-12. |

Only one row is implemented at a time. A later row may be repartitioned by a
recorded audit, but must not silently broaden an earlier checkpoint.

## STRUCT-PARAM-1 Frozen First Tranche

The first implementation is intentionally bounded:

1. Add `parameter(...)` to the callback-once structure builder.
2. Require parameters to precede all fields.
3. Permit a parameter type to reference only earlier parameters.
4. Permit every field type to reference parameters and earlier fields.
5. Require explicit carrier, constructor, and projection binder modes.
6. Generate parameterized carrier, constructor, projections, and beta rules.
7. Expose immutable parameter handles in the expansion handle.
8. Preserve existing unparameterized declarations, rules, source order, and
   Lambdapi emission exactly; the public handle gains only an additive empty
   parameter list.
9. Add focused positive tests for dependency, mode differences, Core checking,
   subject reduction, deterministic Lambdapi emission, and caller-input
   immutability.
10. Add fail-closed tests for a parameter after a field, foreign parameter
    tokens, duplicate binder names, and invalid modes. Callback order makes a
    future-parameter token unconstructible in the first place.

This tranche adds no class metadata, inheritance, named construction,
resolver recursion, parser route, Core node, or kernel rule.

## STRUCT-PARAM-1 Completion Record

`STRUCT-PARAM-1` is final-green on 2026-08-08. The implementation:

- adds one callback-scoped `parameter(...)` declaration before fields;
- gives each parameter explicit carrier, constructor, and projection binder
  modes;
- lowers dependent parameter and field types separately in every generated
  binder context;
- applies the carrier with carrier plicity, the constructor with constructor
  plicity, and projections with projection plicity;
- includes parameter captures and their dependent types in every generated
  projection beta;
- exposes immutable parameter handles while leaving existing
  unparameterized declaration/rule/order/emission output exact;
- rejects parameters after fields, duplicate parameter binders, invalid mode
  triples, and foreign parameter expressions; and
- preserves caller-owned mode objects and freezes only returned artifacts.

The acceptance fixture deliberately uses two dependent parameters whose
plicities differ among carrier, constructor, and projection binders. Its
generated declarations and rules are checked by the ordinary TypeScript LF
compiler, its betas reduce to the selected field under the ordinary runtime,
and its deterministic emitted fragment is accepted by Lambdapi. The callback
order makes a future-parameter token unavailable by construction.

Exact validation:

- `node --require ts-node/register --test
  tests/v3_2_lf_structure_macro_tests.ts`: 13 executable tests passed, two
  opt-in Lambdapi tests skipped;
- `timeout 90s env EMDASH_RUN_LAMBDAPI_STRUCTURE_PROBES=1 node --require
  ts-node/register --test tests/v3_2_lf_structure_macro_tests.ts`: 15/15
  passed, including both unparameterized and parameterized Lambdapi
  fragments;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint for the macro and focused suite: passed;
- `git diff --check`: passed; and
- the one required changed-shared-boundary `./scripts/pnpmw run check:ts`:
  1,516 tests across 228 suites, 1,462 passed, 54 intentionally skipped,
  zero failures. It took approximately 34 minutes and must be carried forward
  rather than rerun for unchanged boundaries.

No `emdash2/` source, active kernel owner, runtime rule, proof rule, Core node,
parser, browser entry, package boundary, or sibling repository changed. The
bounded generated-fragment probe was the relevant Lambdapi conformance gate;
the unchanged active-kernel aggregate was not rerun. The rollback-safe
checkpoint is the local commit containing this completion record and the
message `elaborator: add parameterized structure telescopes`.

`STRUCT-NAMED-2` followed as the next dependency-ready row. Its audit and
proposal were frozen separately before implementation so that named
construction did not absorb class metadata or inheritance.

## STRUCT-NAMED-2 Audit And Frozen Contract

The 2026-08-08 continuation audit found:

- `CoreLfStructureHandle` is consumed only by the focused structure suite;
  no production source currently relies on its exact nested shape;
- `constructorTerm` is a transfer-IR global head, while `kernelCall` operates
  only after compilation and would place this authoring helper on the wrong
  side of the explicit-Core boundary;
- named construction values may legitimately be open locally nameless
  transfer expressions, so the helper cannot require closed terms or invent
  a checking context;
- field constructor plicity is not currently retained by projection handles,
  while parameter handles already retain their three owner-specific modes;
  and
- the existing declaration compiler/checker is the right authority for value
  types after the helper has assembled an ordinary transfer expression.

The selected additive API is:

```ts
constructCoreLfNamedStructure({
  structure: expansion.handle,
  parameters: [
    { parameter: expansion.handle.parameters[0], value: A },
  ],
  fields: [
    { field: expansion.handle.projections[1], value: proof },
    { field: expansion.handle.projections[0], value: operation },
  ],
})
```

Its exact contract is:

1. Parameter and projection handles carry the stable declaring-carrier
   symbol. Projection handles additionally carry the original field binder
   mode.
2. The input contains explicit arrays of parameter and field assignments.
   Their source order is irrelevant.
3. A supplied handle is matched structurally against the selected structure's
   canonical handle at its ordinal. This accepts deterministic copied data but
   rejects a handle from another structure.
4. Every parameter and every field must occur exactly once. Missing,
   duplicate, foreign, malformed, and non-term assignments fail at stable
   source-like paths.
5. Canonical constructor argument order is all parameters by ordinal followed
   by all fields by ordinal.
6. Parameter argument plicity comes from each parameter's constructor mode;
   field argument plicity comes from the recorded field mode. The caller never
   supplies either plicity.
7. Ordinary `type`, `bound`, `global`, `call`, `pi`, and `lambda` transfer
   expressions are cloned without mutating or freezing caller data. Runtime
   `capture` and `wildcard` syntax is rejected.
8. The result is one deeply frozen ordinary `CoreLfTransferExpression` whose
   head is the generated constructor. It contains no named-construction node
   and crosses no trusted boundary.
9. Correct value types are checked only when the returned term is installed
   or checked in its actual context. The helper claims completeness and
   deterministic ordering, not independent dependent typechecking.
10. The focused corpus covers unparameterized and parameterized structures,
    deliberately reversed input order, distinct plicities, open-term cloning,
    caller immutability, ordinary LF compilation, and every fail-closed
    assignment class.

The frozen error classes are `INVALID_CONSTRUCTION`, `FOREIGN_ARGUMENT`,
`DUPLICATE_ARGUMENT`, and `MISSING_ARGUMENT`, with exact paths distinguishing
parameters from fields. This tranche adds no class/schema metadata,
inheritance, defaults, updates, synthesis, parser route, Core node, kernel
rule, browser export, or sibling-repository change.

The proposal gate `H-TS-EMDASH-CLASSES-NAMED-001` is approved under the
user-authorized unattended-review delegation, with immediate human
supersession. The proposal checkpoint records the pre-implementation
backtracking boundary. Because the exported structure authoring surface
changes, one root `check:ts` is required only after the focused tranche is
otherwise green; the resulting aggregate is then carried forward. No
repository-wide `check:all` or unchanged active-kernel aggregate is required.

## STRUCT-NAMED-2 Completion Record

`STRUCT-NAMED-2` is final-green on 2026-08-08. The implementation:

- adds stable declaring-carrier ownership to parameter and projection
  handles, while projections also retain their original constructor-field
  mode;
- adds `constructCoreLfNamedStructure(...)` as a transfer-IR authoring helper
  over explicit named parameter and field assignments;
- structurally accepts deterministic copies of canonical handles while
  rejecting malformed or foreign ownership at stable paths;
- rejects missing and duplicate assignments independently for parameters and
  fields;
- derives plicity from the selected canonical handles and emits arguments in
  parameter-then-field ordinal order, independent of caller order;
- clones ordinary open transfer terms, rejects runtime-only capture/wildcard
  syntax, preserves all caller-owned values, and deeply freezes the returned
  constructor call; and
- leaves dependent value typing to the ordinary LF compiler/checker at the
  actual installation context.

The positive corpus constructs both unparameterized and parameterized
records from deliberately reversed assignments. The parameterized fixture
uses distinct parameter and field plicities, installs the result as a
transparent ordinary LF definition, and passes normal compilation/checking.
The negative corpus fixes the public diagnostic classes and paths for missing,
duplicate, foreign, malformed, and rule-only inputs.

Exact proportional validation:

- `node --require ts-node/register --test
  tests/v3_2_lf_structure_macro_tests.ts`: 19 tests total, 17 passed and the
  two opt-in Lambdapi emission probes intentionally skipped;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint for the macro and focused suite: passed; and
- `git diff --check`: passed.

The one required `./scripts/pnpmw run check:ts` was run once after those gates
were green. Its workspace check, typecheck, and complete lint phases passed;
the test phase emitted its matrix through the late workspace/scale suites
without a reported failure. The terminal transport discarded the final TAP
footer and exit packet during automatic context compaction, so this record
does not invent exact aggregate counters. The completed run was not repeated:
the focused owner suite and static gates above are the exact retained evidence,
and the preceding 1,516-test aggregate remains valid for every unchanged
consumer boundary.

No Lambdapi fragment, `emdash2/` source, active kernel owner, runtime rule,
proof rule, Core node, parser, browser entry, package boundary, or sibling
repository changed. Consequently neither a new Lambdapi probe nor an
active-kernel/repository-wide aggregate was relevant. The proposal
backtracking boundary is `e798ec0`; the rollback-safe implementation
checkpoint is the local commit with message
`elaborator: add named structure construction`.

The next dependency-ready row is `CLASS-SCHEMA-3`. Its first action is a
read-only consumer and representation audit followed by an exact frozen
metadata contract. That checkpoint must add no inheritance lowering,
instance registry, synthesis, call elaboration, parser behavior, or Core
semantics.

## CLASS-SCHEMA-3 Audit And Frozen Contract

The 2026-08-08 audit compared the completed structure expansion/handle and
dictionary seams with Lean's `StructureInfo`, `StructureParentInfo`, and
`ClassEntry` partition. It found:

- Lean likewise keeps structure layout, ordered parent metadata, class
  registration, and output-parameter positions outside its kernel terms;
- the emdash structure expansion already contains the carrier and constructor
  telescopes needed to recover declared parameter and method types without
  adding those types to trusted Core or accepting caller-supplied duplicates;
- direct-parent order must remain source-significant because the next row's
  strict C3 calculation consumes it, while argument order within one parent
  application should be canonical and handle-directed;
- a parent application is a type expression open only in the complete child
  parameter telescope, so it can be stored as ordinary locally nameless
  transfer IR and checked when inheritance is lowered in context;
- class parameter roles can be recorded now, but output/semi-output search
  scheduling and dependency restrictions remain deliberately gated by
  `PARAM-ROLES-10`; and
- an already generated child structure with declared local fields does not
  yet implement its parents. Any parentful schema must therefore say
  explicitly that its layout is unlowered rather than exposing a false
  superclass capability.

The selected additive module is `src/v3_2/lf_class_schema.ts`. Its principal
authoring shape is:

```ts
const monoid = declareCoreLfClassSchema({
  expansion: monoidStructure,
  parameterRoles: [
    { parameter: monoidStructure.handle.parameters[0], role: 'input' },
  ],
  directParents: [
    {
      parent: semigroup,
      arguments: [{
        parameter: semigroup.structure.parameters[0],
        value: coreLfClassParameterTerm(
          monoidStructure,
          monoidStructure.handle.parameters[0]
        ),
      }],
    },
  ],
})
```

Its exact contract is:

1. `declareCoreLfClassSchema(...)` accepts one complete
   `CoreLfStructureDeclarationExpansion`. The class ID is derived from its
   qualified carrier symbol; the caller cannot supply a competing ID.
2. The function validates the generated carrier/constructor telescope seam
   and copies the structure handle. It derives, rather than duplicates,
   parameter and declared-method order, binder names, modes, projection
   symbols, and locally nameless declared types.
3. A parameter identity is `(declaring class ID, parameter ordinal)`. A
   declared-method identity is `(declaring class ID, field ordinal)`. Spelling
   is descriptive and never establishes cross-class identity.
4. Parameter roles are `input | output | semi-output`. Sparse role
   assignments are order-independent and keyed by stable parameter handles;
   an unspecified parameter defaults to `input`. Duplicate, foreign, or
   malformed assignments fail closed.
5. Every declared method records its projection handle and an authoring
   receiver contract saying `class-evidence` while retaining the projection's
   ordinary explicit Core record argument. No third Core plicity is added.
6. Direct parents preserve declaration order. Each parent input carries a
   previously produced class schema and a complete order-independent named
   assignment for that parent's parameters. Self-parenting and duplicate
   direct class IDs fail closed.
7. Parent arguments are cloned at exactly the child-parameter depth, may use
   ordinary transfer term syntax, and may not use dangling indices,
   `capture`, or `wildcard`. Their plicity comes from the parent's carrier
   modes, never from the caller.
8. Each stored parent record contains only a stable parent-class reference,
   canonical arguments, and the ordinary `Parent ...` application. It does
   not recursively embed a parent schema or retain callbacks/object identity,
   keeping the result finite and JSON-serializable.
9. `coreLfClassParameterTerm(expansion, parameter)` validates a structural
   parameter handle and returns its deeply frozen bound reference in the full
   class-parameter telescope. This is the compact safe path for common
   `Parent alpha` substitutions; arbitrary ordinary terms remain possible.
10. The returned schema is a deeply frozen caller-independent snapshot with
    profile revision `emdash-lf-class-schema-v1`. Its layout status is
    `parent-free` when there are no parents and `parents-unlowered` otherwise.
11. `parents-unlowered` schemas are metadata inputs for `CLASS-INHERIT-4`, not
    superclass evidence and not candidates for instance search. The next row
    alone may add C3 order, canonical inherited-field slots, sharing,
    conversions, or superclass providers.
12. Declared types and parent applications are not independently certified by
    this metadata function. The ordinary LF compiler/checker remains the
    authority when generated inheritance declarations are installed.

The frozen diagnostic classes are `INVALID_CLASS_SCHEMA`,
`INVALID_PARAMETER_ROLE`, `FOREIGN_PARAMETER`,
`DUPLICATE_PARAMETER_ROLE`, `INVALID_PARENT`, `DUPLICATE_PARENT`,
`INVALID_PARENT_ARGUMENT`, `FOREIGN_PARENT_ARGUMENT`,
`DUPLICATE_PARENT_ARGUMENT`, and `MISSING_PARENT_ARGUMENT`. Exact paths
distinguish the expansion seam, role assignment, parent ordinal, parent
parameter handle, and argument value.

The focused corpus will cover default and explicit roles, stable declared
types and field identities, copied handles, caller immutability, deep freeze,
JSON round-trip data, ordered multiple parents, canonical parent argument
ordering/plicity, and every frozen failure class. This tranche adds no
inheritance declarations or rules, C3 algorithm, field sharing, superclass
projection, instance provider/scope/search, general call elaborator, parser,
Core/checker branch, Lambdapi emission, browser export, package split, or
sibling-repository change.

The proposal gate `H-TS-EMDASH-CLASSES-SCHEMA-002` is approved under the
user-authorized unattended-review delegation, with immediate human
supersession. The documentation-only proposal checkpoint is the backtracking
boundary. Implementation should add one isolated module and focused suite,
then wire the public v3.2 barrel and root test runner only when the bounded
surface is ready. That shared-surface checkpoint requires one final
`check:ts`; until then, no long aggregate is run. No Lambdapi or active-kernel
gate is relevant because the frozen row changes metadata only.

## Decision Ledger

| ID | Decision | Rationale |
| --- | --- | --- |
| C-001 | Target Lean-comparable semantics, not a Lean clone. | Preserves direct translation of ordinary developments without inheriting parser/kernel/tactic complexity. |
| C-002 | Classes and synthesis erase before Core checking. | Keeps one explicit trusted semantic boundary and portable backends. |
| C-003 | Typeclass synthesis is distinct from runtime rewriting and `unif_rule`. | Search needs scopes, recursion, priorities, bounds, ambiguity, and provenance. |
| C-004 | Parameter modes are explicit for carrier, constructor, and projections. | Mathematical consumers may require different quantification behavior. |
| C-005 | Initial inheritance uses canonical flattened field identities and generated parent reconstruction. | Delivers ancestor sharing with a private, replaceable layout. |
| C-006 | C3-style lookup is strict and deterministic. | Inconsistent hierarchies should require explicit repair rather than heuristic order. |
| C-007 | Same spelling never establishes field identity by itself. | Avoids accidental mathematical identification; translation sugar may emit explicit sharing. |
| C-008 | Search takes an immutable registry and scope snapshot. | Makes source/artifacts reproducible locally, in browsers, and remotely. |
| C-009 | Equal-ranked distinct successes are ambiguous. | Avoids invisible declaration-recency semantics in AI-authored workspaces. |
| C-010 | Implement all-input search before output/semi-output inference. | Establishes a useful bounded resolver without premature metavariable scheduling. |
| C-011 | No general inductive declaration frontend. | Curated inductives/HITs plus explicit trusted extensions better fit the directed-HIT objective. |
| C-012 | TypeScript backend is the initial production focus. | Lambdapi remains specification/conformance evidence, not a runtime dependency. |
| C-013 | Publish curated packages, not the private root workbench. | Provides stable consumer contracts and avoids exposing internal development barrels. |
| C-014 | GetPaidX integration is additive and follows local package qualification. | Protects the published/in-review plugin and keeps platform state non-authoritative. |

## Validation And Checkpoint Policy

Before each bounded semantic checkpoint:

- inspect branch/worktree status and staged/unstaged diffs separately;
- run `./scripts/pnpmw run workspace:check` when workspace/package boundaries
  are affected;
- run the nearest focused tests directly;
- run TypeScript typecheck and changed-file lint as relevant;
- run one `./scripts/pnpmw run check:ts` only when a shared TypeScript boundary
  actually changed and the bounded tranche is otherwise green;
- run a bounded active-kernel check only when current kernel names or
  computation are newly depended upon; and
- run `check:all` only at an actual cross-layer/release boundary.

Recent green aggregate evidence is carried forward when its boundary did not
change. Long repository-wide aggregates must not be rerun for reassurance.
Every Lambdapi command remains bounded to at most 90 seconds.

Local checkpoint commits are authorized on this dedicated goal branch after:

- the tranche is coherent and green;
- this ledger and decision record are synchronized;
- exact staged paths contain no unrelated work;
- `git diff --cached` and `git diff --cached --check` are reviewed; and
- the checkpoint message names the completed plan row.

Do not amend, rebase, reset, force-push, or erase failed evidence. Use a new
correcting commit or a separate experiment branch. Preserve all existing
worktrees. Push, merge, release, publication, deployment, and cleanup occur
only at their recorded readiness boundary and under the applicable repository
SOP; no hosted operation may break an existing public contract.

## Baseline Evidence

At `66a61ed` in the new worktree on 2026-08-08:

- `./scripts/bootstrap-worktree.sh` passed and created the worktree-local pnpm
  link graph using the shared store;
- `./scripts/pnpmw run workspace:check` passed;
- `./scripts/pnpmw run typecheck` passed; and
- `node --require ts-node/register --test
  tests/v3_2_lf_structure_macro_tests.ts` passed 10/10 executable tests with
  the opt-in Lambdapi probe skipped.

No repository-wide aggregate was run for this baseline.

## Persistent `/goal` Objective

Use this objective after the first implementation checkpoint is synchronized:

> Continue the long-running TypeScript/emdash structures, classes, and
> instance-synthesis goal from the dedicated
> `/home/user1/emdash1-classes-v1` worktree on branch
> `goal/typescript-emdash-classes-v1`. Treat
> `docs/TYPESCRIPT_EMDASH_STRUCTURES_CLASSES_AND_INSTANCE_SYNTHESIS_PLAN.md`
> as the living governing plan, together with the authority chain and SOPs it
> names. On every continuation inspect all worktrees, current branch ancestry,
> staged and unstaged changes, the governing authorities, and the plan ledger;
> preserve unrelated work. Select only the next dependency-ready bounded row,
> keep structures/classes/synthesis as direct-TypeScript management which
> elaborates to explicit checked Core, focus the production implementation on
> TypeScript/emdash, and retain Lambdapi only as an optional bounded
> conformance route. Do not add declaration text parsing, a general inductive
> frontend, a class/Core node, or hidden process-global proof state. Run
> focused proportional checks and avoid long aggregate/repository-wide tests
> unless an actually changed shared or release boundary strictly requires one.
> Local rollback-safe checkpoint commits on the dedicated goal branch are
> authorized only after the bounded tranche is green, the living plan is
> synchronized, and the exact staged diff is reviewed under
> `docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. When a recorded internal
> proposal gate awaits review and no immediate human response arrives, the
> goal may approve the bounded proposal itself under that checkpoint SOP;
> later human direction supersedes it immediately. Cross-repository package,
> GetPaidX/LastRevision, Arrowgram, publication, and deployment work must wait
> for the plan's prerequisites, follow each repository's SOP, use isolated
> branches, remain backward-compatible/additive where public contracts exist,
> and record exact evidence before mutation. Continue until every scoped row
> is implemented, rejected with durable evidence, or explicitly deferred
> behind a concrete prerequisite or human decision.

## Recovery Checklist

On every continuation:

1. read root `AGENTS.md` and any closer instructions;
2. inspect `git worktree list`, branch/HEAD ancestry, and status;
3. inspect staged and unstaged diffs separately;
4. read this plan's status, ledger, decisions, and latest completion record;
5. locate exact definitions and consumers with `rg`;
6. carry forward valid recent green evidence for unchanged boundaries;
7. implement one dependency-ready bounded row;
8. run proportional checks;
9. synchronize this plan before staging;
10. review exact staged content and checkpoint only when authorized and green;
11. never rewrite or discard checkpoints to hide a failed experiment; and
12. report branch, HEAD, changed plan row, exact validation, worktree state,
    and next dependency-ready row.
